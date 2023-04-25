use std::{collections::HashMap, rc::Rc};

use halo2_proofs::{
    arithmetic::Field,
    circuit::{Layouter, Region, Value},
    halo2curves::FieldExt,
    plonk::{
        Advice, Column, ConstraintSystem, Expression, FirstPhase, Fixed, SecondPhase, ThirdPhase,
        VirtualCells,
    },
    poly::Rotation,
};

use crate::{
    ast::{query::Queriable, ForwardSignal, InternalSignal, StepType, ToField},
    compiler::{
        cell_manager::Placement, step_selector::StepSelector, FixedGenContext, TraceContext,
        WitnessGenContext,
    },
    dsl::StepTypeHandler,
    ir::{
        Circuit, Column as cColumn, ColumnType::Advice as cAdvice, ColumnType::Fixed as cFixed,
        ColumnType::Halo2Advice, ColumnType::Halo2Fixed, PolyExpr,
    },
};

#[allow(non_snake_case)]
pub fn chiquito2Halo2<F: FieldExt, TraceArgs, StepArgs: Clone>(
    circuit: Circuit<F, TraceArgs, StepArgs>,
) -> ChiquitoHalo2<F, TraceArgs, StepArgs> { 
    ChiquitoHalo2::new(circuit)
}

#[derive(Clone, Debug)]
pub struct ChiquitoHalo2<F: Field, TraceArgs, StepArgs: Clone> {
    pub debug: bool,

    circuit: Circuit<F, TraceArgs, StepArgs>,

    advice_columns: HashMap<u32, Column<Advice>>,
    fixed_columns: HashMap<u32, Column<Fixed>>,
}

impl<F: FieldExt, TraceArgs, StepArgs: Clone> ChiquitoHalo2<F, TraceArgs, StepArgs> {
    pub fn new(circuit: Circuit<F, TraceArgs, StepArgs>) -> ChiquitoHalo2<F, TraceArgs, StepArgs> {
        ChiquitoHalo2 {
            debug: true,
            circuit,
            advice_columns: Default::default(),
            fixed_columns: Default::default(),
        }
    }

    pub fn configure(&mut self, meta: &mut ConstraintSystem<F>) {
        let mut advice_columns = HashMap::<u32, Column<Advice>>::new();
        let mut fixed_columns = HashMap::<u32, Column<Fixed>>::new();

        for column in self.circuit.columns.iter() { // iterate over ir Circuit columns
            match column.ctype { // column type
                cAdvice => { // convert to native type
                    let halo2_column = to_halo2_advice(meta, column);
                    advice_columns.insert(column.uuid(), halo2_column);
                    meta.annotate_lookup_any_column(halo2_column, || column.annotation.clone());
                }
                cFixed => { // convert to native type
                    let halo2_column = meta.fixed_column();
                    fixed_columns.insert(column.uuid(), halo2_column);
                    meta.annotate_lookup_any_column(halo2_column, || column.annotation.clone());
                }
                Halo2Advice => { // native type directly imported
                    let halo2_column = column
                        .halo2_advice
                        .unwrap_or_else(|| {
                            panic!("halo2 advice column not found {}", column.annotation)
                        })
                        .column;
                    advice_columns.insert(column.uuid(), halo2_column);
                    meta.annotate_lookup_any_column(halo2_column, || column.annotation.clone());
                }
                Halo2Fixed => { // native type directly imported
                    let halo2_column = column
                        .halo2_fixed
                        .unwrap_or_else(|| {
                            panic!("halo2 advice column not found {}", column.annotation)
                        })
                        .column;
                    fixed_columns.insert(column.uuid(), halo2_column);
                    meta.annotate_lookup_any_column(halo2_column, || column.annotation.clone());
                }
            }
        }

        self.advice_columns = advice_columns; // note that both native halo2 advice columns and advice columns converted from chiquito are stored under the same hashmap
        self.fixed_columns = fixed_columns;

        if !self.circuit.polys.is_empty() {
            meta.create_gate("main", |meta| { // create_gate function in halo2 native
                let mut constraints: Vec<(&'static str, Expression<F>)> = Vec::new();

                for poly in self.circuit.polys.iter() { // iterate over all ir Circuit PolyExpr (with annotation)
                    let converted = self.convert_poly(meta, &poly.expr); // converts to Halo2 native Expression
                    let annotation = Box::leak(
                        format!("{} => {:?}", poly.annotation, converted).into_boxed_str(),
                    );
                    constraints.push((annotation, converted));
                }

                constraints // returns constraints as a vector
            });
        }

        for lookup in self.circuit.lookups.iter() { // iterate over all ir Circuit PolyLookup
            meta.lookup_any("", |meta| { // lookup_any function in halo2 native
                let mut exprs = Vec::new();
                for (src, dest) in lookup.exprs.iter() {
                    exprs.push((self.convert_poly(meta, src), self.convert_poly(meta, dest)))
                }

                exprs // return a vector of tuple (Expression<F>, Expression<F>)
            });
        }
    }

    pub fn synthesize(&self, layouter: &mut impl Layouter<F>, args: TraceArgs) {
        let (advice_assignments, height) = self.synthesize_advice(args); // returns vector of fixed assignments; Assignment is an alias type that includes Column, offset, and Value

        let _ = layouter.assign_region(
            || "circuit",
            |mut region| {
                self.annotate_circuit(&mut region);

                let fixed_assignments = self.synthesize_fixed(); // returns vector of fixed assignments; Assignment is an alias type that includes Column, offset, and Value
                for (column, offset, value) in fixed_assignments.iter() {
                    region.assign_fixed(|| "", *column, *offset, || *value)?; // call halo2 native functions
                }

                for (column, offset, value) in advice_assignments.iter() {
                    region.assign_advice(|| "", *column, *offset, || *value)?;
                }

                if height > 0 {
                    self.default_fixed(&mut region, height);
                }

                Ok(())
            },
        );
    }

    fn synthesize_fixed(&self) -> Vec<Assignment<F, Fixed>> {
        if let Some(fg) = &self.circuit.fixed_gen { // if a fixed generator exists in the ir Circuit (fixed generator is the alias of a function type)
            let mut ctx = FixedGenContextHalo2::<F> {
                assigments: Default::default(),

                max_offset: 0,
            };

            fg(&mut ctx); // invoke fix generator function on FixedGenContext
            // call fixed generating function on an empty ctx that's just created
            // because within the fixed generating function, we can assign cell values to fixed columns

            ctx.assigments // return vector of assignments; 
        } else {
            vec![]
        }
    }

    fn synthesize_advice(&self, args: TraceArgs) -> (Vec<Assignment<F, Advice>>, usize) {
        if self.debug {
            println!("starting advise generation");
        }

        if let Some(trace) = &self.circuit.trace { // trace: Option<Rc<Trace<TraceArgs, StepArgs>>> of ir Circuit; if trace exists
            let mut ctx = TraceContextHalo2::<F, StepArgs> { // new TraceContext object
                assigments: Default::default(),
                advice_columns: self.advice_columns.clone(),
                placement: self.circuit.placement.clone(),
                selector: self.circuit.selector.clone(),
                step_types: self.circuit.step_types.clone(),
                offset: 0,
                cur_step: None,
                max_offset: 0,
                height: 0,
            };

            trace(&mut ctx, args); // trace is a function that takes a TraceContext and TraceArgs, where TraceArgs are external inputs to the circuit

            let height = if ctx.height > 0 { // ??? what are height and max_offset used for?
                ctx.height
            } else {
                ctx.max_offset + 1
            };

            (ctx.assigments, height) // return advice assignments and height
        } else {
            (vec![], 0)
        }
    }

    fn annotate_circuit(&self, region: &mut Region<F>) {
        for column in self.circuit.columns.iter() { // iterate over all columns stored in ir Circuit 
            match column.ctype {
                cAdvice | Halo2Advice => { // chiquito advice or halo2 native advice column type
                    let halo2_column = self
                        .advice_columns
                        .get(&column.uuid())
                        .expect("advice column not found");

                    region.name_column(|| column.annotation.clone(), *halo2_column); // invoke halo2 native function to name column
                }
                cFixed | Halo2Fixed => { // chiquito fixed or halo2 native fixed column type
                    let halo2_column = self
                        .fixed_columns
                        .get(&column.uuid())
                        .expect("fixed column not found");

                    region.name_column(|| column.annotation.clone(), *halo2_column);
                }
            }
        }
    }

    fn default_fixed(&self, region: &mut Region<F>, height: usize) { 
        let q_enable = self
            .fixed_columns
            .get(&self.circuit.q_enable.uuid())
            .expect("q_enable column not found");
        // invokes assign_fixed halo2 native function 
        for i in 0..height { // assigns 1 for all rows of q_enable
            region.assign_fixed(|| "q_enable=1", *q_enable, i, || Value::known(F::one()));
        }

        if let Some(q_first) = self.circuit.q_first.clone() {
            let q_first = self
                .fixed_columns
                .get(&q_first.uuid())
                .expect("q_enable column not found");
            // assigns 1 for first row
            region.assign_fixed(|| "q_first=1", *q_first, 0, || Value::known(F::one()));
        }

        if let Some(q_last) = self.circuit.q_last.clone() {
            let q_last = self
                .fixed_columns
                .get(&q_last.uuid())
                .expect("q_enable column not found");
            // assigns 1 for last row
            region.assign_fixed(
                || "q_first=1",
                *q_last,
                height - 1,
                || Value::known(F::one()),
            );
        }
    }
    
    fn convert_poly(&self, meta: &mut VirtualCells<'_, F>, src: &PolyExpr<F>) -> Expression<F> { // convert ir PolyExpr to halo2 Expression
        match src { // convert_poly is called recursively
            PolyExpr::Const(c) => Expression::Constant(*c),
            PolyExpr::Sum(es) => {
                let mut iter = es.iter();
                let first = self.convert_poly(meta, iter.next().unwrap());
                iter.fold(first, |acc, e| acc + self.convert_poly(meta, e))
            }
            PolyExpr::Mul(es) => {
                let mut iter = es.iter();
                let first = self.convert_poly(meta, iter.next().unwrap());
                iter.fold(first, |acc, e| acc * self.convert_poly(meta, e))
            }
            PolyExpr::Neg(e) => -self.convert_poly(meta, e),
            PolyExpr::Pow(e, n) => {
                if *n == 0 {
                    Expression::Constant(1.field())
                } else {
                    let e = self.convert_poly(meta, e);
                    (1..*n).fold(e.clone(), |acc, _| acc * e.clone())
                }
            }
            PolyExpr::Halo2Expr(e) => e.clone(),
            PolyExpr::Query(column, rotation, _) => self.convert_query(meta, column, *rotation), // invokes convert query below
        }
    }

    fn convert_query( // convert Querible to halo2 Expression; in halo2, we first invoke query_advice or query_fixed to get halo2 Expression, and then construct constraint vector using them
        &self,
        meta: &mut VirtualCells<'_, F>,
        column: &cColumn,
        rotation: i32,
    ) -> Expression<F> {
        match column.ctype {
            cAdvice | Halo2Advice => {
                let c = self
                    .advice_columns
                    .get(&column.uuid())
                    .unwrap_or_else(|| panic!("column not found {}", column.annotation));

                meta.query_advice(*c, Rotation(rotation))
            }
            cFixed | Halo2Fixed => {
                let c = self
                    .fixed_columns
                    .get(&column.uuid())
                    .unwrap_or_else(|| panic!("column not found {}", column.annotation));

                meta.query_fixed(*c, Rotation(rotation))
            }
        }
    }
}

type Assignment<F, CT> = (Column<CT>, usize, Value<F>); // assignment includes column, offset, and value

struct TraceContextHalo2<F: Field, StepArgs> {
    advice_columns: HashMap<u32, Column<Advice>>,
    placement: Placement<F, StepArgs>,
    selector: StepSelector<F, StepArgs>,
    step_types: HashMap<u32, Rc<StepType<F, StepArgs>>>,

    offset: usize,
    cur_step: Option<Rc<StepType<F, StepArgs>>>,

    assigments: Vec<Assignment<F, Advice>>,

    max_offset: usize,
    height: usize,
}

impl<F: Field, StepArgs: Clone> TraceContextHalo2<F, StepArgs> {
    fn find_halo2_placement(
        &self,
        step: &StepType<F, StepArgs>,
        query: Queriable<F>,
    ) -> (Column<Advice>, i32) { // returns advice column and rotation
        match query {
            Queriable::Internal(signal) => self.find_halo2_placement_internal(step, signal),

            Queriable::Forward(forward, next) => {
                self.find_halo2_placement_forward(step, forward, next)
            }

            Queriable::Halo2AdviceQuery(signal, rotation) => (signal.column, rotation),

            _ => panic!("invalid advice assignment on queriable {:?}", query),
        }
    }

    fn find_halo2_placement_internal(
        &self,
        step: &StepType<F, StepArgs>,
        signal: InternalSignal,
    ) -> (Column<Advice>, i32) {
        let placement = self.placement.find_internal_signal_placement(step, &signal);

        let column = self
            .advice_columns
            .get(&placement.column.uuid())
            .unwrap_or_else(|| panic!("column not found for internal signal {:?}", signal));

        (*column, placement.rotation)
    }

    fn find_halo2_placement_forward(
        &self,
        step: &StepType<F, StepArgs>,
        forward: ForwardSignal,
        next: bool,
    ) -> (Column<Advice>, i32) {
        let placement = self.placement.get_forward_placement(&forward);

        let super_rotation = placement.rotation // add placement rotation to step_height, because need to skip a super row by step_height if the forward column invokes next
            + if next {
                self.placement.step_height(step) as i32
            } else {
                0
            };

        let column = self
            .advice_columns
            .get(&placement.column.uuid())
            .unwrap_or_else(|| panic!("column not found for forward signal {:?}", forward));

        (*column, super_rotation) // super rotation = placement rotation + step height
    }
}

impl<F: Field, StepArgs: Clone> TraceContext<StepArgs> for TraceContextHalo2<F, StepArgs> {
    fn add(&mut self, step: &StepTypeHandler, args: StepArgs) { // add is a function defined under TraceContext interface in compiler, and is invoked to instantiate a step in trace function
        if let Some(cur_step) = &self.cur_step { 
            self.offset += self.placement.step_height(cur_step) as usize; // update TraceContext offset to increment by step height if cur_step exists, cur_step is a steptype with stepargs ??? what are we doing here?
        } else {
            self.offset = 0;
        }

        let cur_step = Rc::clone(
            self.step_types
                .get(&step.uuid())
                .expect("step type not found"),
        );

        self.cur_step = Some(Rc::clone(&cur_step));

        (*cur_step.wg)(self, args); // wg is a witness generation function field of StepType, gets called under step_type_def ??? why is it called here? looks like when adding a step instantiation, all step witnesses are generated according to wg, which is set up using the wg function in step_type_def

        // activate selector ??? tbh i don't really understand this code of activating selector

        let selector_assignment = self
            .selector
            .selector_assignment // steptype to selector assignment hashmap; SelectorAssignment is a (PolyExpr, F) tuple
            .get(&cur_step)
            .expect("selector assignment for step not found");

        for (expr, value) in selector_assignment.iter() { 
            match expr {
                PolyExpr::Query(column, rot, _) => {
                    let column = self
                        .advice_columns // ??? why are selector columns advice columns, aren't they q_enable, q_first, q_last, etc.?
                        .get(&column.uuid())
                        .expect("selector expression column not found");

                    self.assigments.push((
                        *column,
                        self.offset + *rot as usize, // ??? how are offset and rotation different here? is offset the accumulated row height and rot the relative rotation value for the current step? 
                        Value::known(*value),
                    ))
                }
                _ => panic!("wrong type of expresion is selector assignment"),
            }
        }
    }

    fn set_height(&mut self, height: usize) {
        self.height = height;
    }
}

impl<F: Field, StepArgs: Clone> WitnessGenContext<F> for TraceContextHalo2<F, StepArgs> { // ??? why is wg context implemented for tracecontext? shouldn't wg be under step_type_def?
    fn assign(&mut self, lhs: Queriable<F>, rhs: F) { //  called under the closure defined in wg, to assign RHS value to LHS Queriable, then push the assignments under TraceContext
        if let Some(cur_step) = &self.cur_step {
            let (column, rotation) = self.find_halo2_placement(cur_step, lhs);

            let offset = (self.offset as i32 + rotation) as usize; // absolute offset as current offset plus step rotation
            self.assigments.push((column, offset, Value::known(rhs)));

            self.max_offset = self.max_offset.max(offset);
        } else {
            panic!("jarrl assigning outside a step");
        }
    }
}

struct FixedGenContextHalo2<F: Field> {
    assigments: Vec<Assignment<F, Fixed>>,

    max_offset: usize,
}

impl<F: Field> FixedGenContextHalo2<F> {
    fn find_halo2_placement(query: Queriable<F>) -> (Column<Fixed>, i32) {
        match query {
            Queriable::Halo2FixedQuery(signal, rotation) => (signal.column, rotation),
            _ => panic!("invalid fixed assignment on queriable {:?}", query),
        }
    }
}

impl<F: Field> FixedGenContext<F> for FixedGenContextHalo2<F> {
    fn assign(&mut self, offset: usize, lhs: Queriable<F>, rhs: F) { // called by the user under fixed_gen function, assign RHS value to LHS Querible at offset
        let (column, rotation) = Self::find_halo2_placement(lhs);

        if rotation != 0 {
            panic!("cannot assign fixed value with rotation");
        }

        self.assigments.push((column, offset, Value::known(rhs))); // ??? why push witness generation under TraceContextHalo2 (which implements WitnessGenContext), but push fixed column assignment under FixedGenContextHalo2 (which implements FixedGenContext)? why not have TraceContextHalo2 implement FixedGenContext as well?

        self.max_offset = self.max_offset.max(offset);
    }
}

pub fn to_halo2_advice<F: Field>( // ??? i don't really see where phase is used?
    meta: &mut ConstraintSystem<F>,
    column: &cColumn,
) -> Column<Advice> {
    match column.phase {
        0 => meta.advice_column_in(FirstPhase), // construct Phase objects in halo2 native circuit to Column<Advice> in halo2
        1 => meta.advice_column_in(SecondPhase),
        2 => meta.advice_column_in(ThirdPhase),
        _ => panic!("jarll wrong phase"),
    }
}
