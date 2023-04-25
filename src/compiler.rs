use core::fmt::Debug;
use std::{collections::HashMap, rc::Rc};

use halo2_proofs::plonk::Column as Halo2Column;
use halo2_proofs::{arithmetic::Field, plonk::Advice};

use crate::{
    ast::{
        query::Queriable, Circuit as astCircuit, Expr, ImportedHalo2Advice, ImportedHalo2Fixed,
        StepType,
    },
    dsl::StepTypeHandler,
    ir::{Circuit, Column, ColumnType, Poly, PolyExpr, PolyLookup},
    util::uuid,
};

use self::{
    cell_manager::{CellManager, Placement},
    step_selector::{StepSelector, StepSelectorBuilder},
};

pub mod cell_manager;
pub mod step_selector;

pub trait TraceContext<StepArgs> {
    fn add(&mut self, step: &StepTypeHandler, args: StepArgs);
    fn set_height(&mut self, height: usize);
}

pub trait WitnessGenContext<F> {
    fn assign(&mut self, lhs: Queriable<F>, rhs: F);
}

pub trait FixedGenContext<F> {
    fn assign(&mut self, offset: usize, lhs: Queriable<F>, rhs: F);
}

#[derive(Debug)]
pub struct CompilationUnit<F, StepArgs> {
    pub placement: Placement<F, StepArgs>,
    pub selector: StepSelector<F, StepArgs>,
    pub columns: Vec<Column>,
    pub step_types: HashMap<u32, Rc<StepType<F, StepArgs>>>,
    pub annotations: HashMap<u32, String>,
    pub polys: Vec<Poly<F>>,
    pub lookups: Vec<PolyLookup<F>>,
}

impl<F, StepArgs> Default for CompilationUnit<F, StepArgs> {
    fn default() -> Self {
        Self {
            placement: Default::default(),
            selector: Default::default(),
            columns: Default::default(),
            step_types: Default::default(),
            annotations: Default::default(),
            polys: Default::default(),
            lookups: Default::default(),
        }
    }
}

impl<F, StepArgs> CompilationUnit<F, StepArgs> {
    fn find_halo2_advice(&self, to_find: ImportedHalo2Advice) -> Option<Column> {
        for column in self.columns.iter() {
            if let Some(advice) = column.halo2_advice {
                if advice == to_find {
                    return Some(column.clone());
                }
            }
        }

        None
    }

    fn find_halo2_advice_native(&self, halo2_advice: Halo2Column<Advice>) -> Option<Column> {
        for column in self.columns.iter() {
            if let Some(advice) = column.halo2_advice {
                if advice.column == halo2_advice {
                    return Some(column.clone());
                }
            }
        }

        None
    }

    fn find_halo2_fixed(&self, to_find: ImportedHalo2Fixed) -> Option<Column> {
        for column in self.columns.iter() {
            if let Some(fixed) = column.halo2_fixed {
                if fixed == to_find {
                    return Some(column.clone());
                }
            }
        }

        None
    }
}

pub struct Compiler<CM: CellManager, SSB: StepSelectorBuilder> {
    cell_manager: CM,
    step_selector_builder: SSB,
}

impl<CM: CellManager, SSB: StepSelectorBuilder> Compiler<CM, SSB> {
    pub fn new(cell_manager: CM, step_selector_builder: SSB) -> Compiler<CM, SSB> {
        Compiler {
            cell_manager,
            step_selector_builder,
        }
    }

    pub fn compile<F: Field + Clone, TraceArgs, StepArgs>( 
        &self,
        sc: &astCircuit<F, TraceArgs, StepArgs>,
    ) -> Circuit<F, TraceArgs, StepArgs> { // creates an IR circuit
        let mut unit = CompilationUnit::<F, StepArgs> {
            annotations: {
                let mut acc = sc.annotations.clone(); // annotations from the circuit, i.e. not specific to a steptype, e.g. forward rows
                for step in sc.step_types.values() { // iterate annotations from each steptype, e.g. internal steps
                    acc.extend(step.annotations.clone());
                }

                acc
            },
            ..Default::default() // the rest value is set to default for now
        };

        let halo2_advice_columns: Vec<Column> = sc // ast circuit
            .halo2_advice
            .iter()
            .map(|signal| {
                if let Some(annotation) = unit.annotations.get(&signal.uuid()) { // if the advice column's annotation exists
                    Column::new_halo2_advice(format!("halo2 advice {}", annotation), *signal)
                } else {
                    Column::new_halo2_advice("halo2 advice", *signal) // if no annotation exists, default annotation is "halo2 advice"
                }
            })
            .collect();

        let halo2_fixed_columns: Vec<Column> = sc
            .halo2_fixed
            .iter()
            .map(|signal| {
                if let Some(annotation) = unit.annotations.get(&signal.uuid()) {
                    Column::new_halo2_fixed(format!("halo2 fixed {}", annotation), *signal)
                } else {
                    Column::new_halo2_fixed("halo2 fixed", *signal)
                }
            })
            .collect();

        unit.columns = vec![halo2_advice_columns, halo2_fixed_columns].concat(); // both advice and fixed columns go to columns under CompilationUnit
        unit.step_types = sc.step_types.clone();

        self.cell_manager.place(&mut unit, sc); // fill the placement field of CompilationUnit; placement field holds three hashmaps, one for forward signals, one for all columns, and one for all steps
        self.step_selector_builder
            .build::<F, TraceArgs, StepArgs>(&mut unit); // fill the selector field of CompilationUnit and push all columns to the CompilationUnit's column field

        for step in unit.step_types.clone().values() {
            // compile ast objects to ir, for columns that are probably limited to a step type, that's why compile_step function is needed
            self.compile_step(&mut unit, step); // converts all columns and lookups from ast to ir (Poly) for each steptype
        }

        let q_enable = Column { // create an enable column 
            annotation: "q_enable".to_owned(),
            ctype: ColumnType::Fixed,
            halo2_advice: None,
            halo2_fixed: None,
            phase: 0,
            id: uuid(),
        };

        unit.columns.push(q_enable.clone());

        self.add_q_enable(&mut unit, q_enable.clone()); // multiply all lookup and regular columns in the PLONK table

        let q_first = if let Some(step_type) = sc.first_step { // if there's a first_step set by the pragma_first_step function in dsl
            let q_first = Column { 
                annotation: "q_first".to_owned(),
                ctype: ColumnType::Fixed,
                halo2_advice: None,
                halo2_fixed: None,
                phase: 0,
                id: uuid(),
            };
            unit.columns.push(q_first.clone()); // create a q_first column and push it to the CompilationUnit

            let step = unit  // this is the first_step field of the ast circuit
                .step_types
                .get(&step_type.uuid())
                .expect("step not found");

            let poly = PolyExpr::Mul(vec![ // multiply q_first to (1 - first_step) ??? why 
                PolyExpr::<F>::Query(q_first.clone(), 0, "q_first".to_owned()),
                unit.selector.unselect(step), // unselect creates a (1 - step). here it is (1 - first_step)
            ]);

            unit.polys.push(Poly {
                annotation: "q_first".to_string(),
                expr: poly,
            });

            Some(q_first)
        } else {
            None
        };

        let q_last = if let Some(step_type) = sc.last_step {
            let q_last = Column {
                annotation: "q_last".to_owned(),
                ctype: ColumnType::Fixed,
                halo2_advice: None,
                halo2_fixed: None,
                phase: 0,
                id: uuid(),
            };
            unit.columns.push(q_last.clone());

            let step = unit
                .step_types
                .get(&step_type.uuid())
                .expect("step not found");

            let poly = PolyExpr::Mul(vec![ // q_last * (1 - last_step)
                PolyExpr::<F>::Query(q_last.clone(), 0, "q_last".to_owned()),
                unit.selector.unselect(step), // 1 - last_step
            ]);

            unit.polys.push(Poly {
                annotation: "q_last".to_string(),
                expr: poly,
            });

            Some(q_last)
        } else {
            None
        };

        Circuit::<F, TraceArgs, StepArgs> { // ir Circuit type constructed from CompilationUnit fields, which are constructed from ast Circuit
            placement: unit.placement,
            selector: unit.selector,
            columns: unit.columns,
            polys: unit.polys,
            lookups: unit.lookups,
            step_types: unit.step_types,
            q_enable, // q_enable, q_first, and q_last are all fixed columns
            q_first,
            q_last,

            trace: sc.trace.as_ref().map(|v| Rc::clone(v)),
            fixed_gen: sc.fixed_gen.as_ref().map(|v| Rc::clone(v)),
        }
    }

    fn compile_step<F: Clone + Debug, StepArgs>(
        &self,
        unit: &mut CompilationUnit<F, StepArgs>,
        step: &StepType<F, StepArgs>,
    ) {
        let step_annotation = unit
            .annotations
            .get(&step.uuid())
            .unwrap_or(&"??".to_string()) // default value of "??" is used incase the value is None
            .to_owned(); // convert to owned String from &String

        for constr in step.constraints.iter() {
            let constraint = self.transform_expr(unit, step, &constr.expr.clone()); // transform to PolyExpr defined in IR
            let poly = unit.selector.select(step, &constraint); // return the multiplication of selector (defined in steptype) and the constraint, as a PolyExpr

            unit.polys.push(Poly {
                expr: poly,
                annotation: format!(
                    "{}::{} => {:?}",
                    step_annotation.clone(),
                    constr.annotation.clone(),
                    constr.expr
                ),
            })
        }

        // TODO only transition_constraints should have rotations
        for constr in step.transition_constraints.iter() {
            let constraint = self.transform_expr(unit, step, &constr.expr.clone());
            let poly = unit.selector.select(step, &constraint); // multiply by selector for TransitionConstraints as well

            unit.polys.push(Poly {
                expr: poly,
                annotation: format!(
                    "{}::{} => {:?}",
                    step_annotation.clone(),
                    constr.annotation.clone(),
                    constr.expr
                ),
            })
        }

        for lookup in step.lookups.iter() {
            let poly_lookup = PolyLookup {
                exprs: lookup
                    .exprs
                    .iter()
                    .map(|(src, dest)| {
                        let src_poly = self.transform_expr(unit, step, src); // source lookup column (this is already after multiplying the enabler)
                        let dest_poly = self.transform_expr(unit, step, dest); // destination lookup column
                        let src_selected = unit.selector.select(step, &src_poly); // multiply selector in steptype to source column

                        (src_selected, dest_poly)
                    })
                    .collect(),
            };

            unit.lookups.push(poly_lookup); // convert to PolyLookup
        }
    }

    fn place_queriable<F: Clone, StepArgs>( // relied on by transform_expr; main purpose of PolyExpr is to convert the Querible type of ast
        &self,
        unit: &CompilationUnit<F, StepArgs>,
        step: &StepType<F, StepArgs>,
        q: Queriable<F>,
    ) -> PolyExpr<F> {
        match q {
            Queriable::Internal(signal) => {
                let placement = unit.placement.find_internal_signal_placement(step, &signal); // cell manager assigns column numbers for all forward and internal signals

                let annotation = if let Some(annotation) = unit.annotations.get(&signal.uuid()) { // use default annotation if not found
                    format!(
                        "{}[{}, {}]",
                        annotation, placement.column.annotation, placement.rotation
                    )
                } else {
                    format!("[{}, {}]", placement.column.annotation, placement.rotation)
                };

                PolyExpr::Query(placement.column, placement.rotation, annotation) // column, rotation, annotation; 
            }
            Queriable::Forward(forward, next) => {
                let placement = unit.placement.get_forward_placement(&forward);

                let super_rotation = placement.rotation // ??? means super row rotation? 
                    + if next {
                        unit.placement.step_height(step) as i32
                    } else {
                        0
                    };

                let annotation = if let Some(annotation) = unit.annotations.get(&forward.uuid()) {
                    if next {
                        format!(
                            "next({})[{}, {}]",
                            annotation, placement.column.annotation, super_rotation
                        )
                    } else {
                        format!(
                            "{}[{}, {}]",
                            annotation, placement.column.annotation, super_rotation
                        )
                    }
                } else {
                    format!("[{}, {}]", placement.column.annotation, super_rotation)
                };
                PolyExpr::Query(placement.column, super_rotation, annotation)
            }
            Queriable::StepTypeNext(step_type_handle) => {
                let super_rotation = unit.placement.step_height(step);
                let dest_step = unit
                    .step_types
                    .get(&step_type_handle.uuid())
                    .expect("step not found");

                unit.selector.next_expr(dest_step, super_rotation) // rotate a steptype to create a PolyExpr; next_expr does the rotation
            }
            Queriable::Halo2AdviceQuery(signal, rot) => { 
                let annotation = if let Some(annotation) = unit.annotations.get(&signal.uuid()) {
                    format!("[{}, {}]", annotation, rot)
                } else {
                    format!("[halo2_advice?, {}]", rot)
                };
                PolyExpr::Query(
                    unit.find_halo2_advice(signal)
                        .expect("halo2 advice column not found"),
                    rot,
                    annotation,
                )
            }
            Queriable::Halo2FixedQuery(signal, rot) => {
                let annotation = if let Some(annotation) = unit.annotations.get(&signal.uuid()) {
                    format!("[{}, {}]", annotation, rot)
                } else {
                    format!("[halo2_fixed?, {}]", rot)
                };
                PolyExpr::Query(
                    unit.find_halo2_fixed(signal)
                        .expect("halo2 fixed column not found"),
                    rot,
                    annotation,
                )
            }
            Queriable::_unaccessible(_) => panic!("jarrl"),
        }
    }

    fn transform_expr<F: Clone, StepArgs>( // relied on by compile_steps function
        &self,
        unit: &CompilationUnit<F, StepArgs>,
        step: &StepType<F, StepArgs>,
        source: &Expr<F>,
    ) -> PolyExpr<F> {
        match source.clone() {
            Expr::Const(c) => PolyExpr::Const(c), // transform_expr is called by itself recursively
            Expr::Sum(v) => PolyExpr::Sum(
                v.into_iter()
                    .map(|e| self.transform_expr(unit, step, &e))
                    .collect(),
            ),
            Expr::Mul(v) => PolyExpr::Mul(
                v.into_iter()
                    .map(|e| self.transform_expr(unit, step, &e))
                    .collect(),
            ),
            Expr::Neg(v) => PolyExpr::Neg(Box::new(self.transform_expr(unit, step, &v))),
            Expr::Pow(v, exp) => PolyExpr::Pow(Box::new(self.transform_expr(unit, step, &v)), exp),
            Expr::Query(q) => self.place_queriable(unit, step, q),
            Expr::Halo2Expr(expr) => PolyExpr::Halo2Expr(expr), // Halo2Expr are directly concverted
        }
    }

    fn add_q_enable<F: Clone, StepArgs>(
        &self,
        unit: &mut CompilationUnit<F, StepArgs>,
        q_enable: Column,
    ) {
        unit.polys = unit
            .polys
            .iter()
            .map(|poly| Poly {
                annotation: poly.annotation.clone(),
                expr: PolyExpr::Mul(vec![
                    PolyExpr::<F>::Query(q_enable.clone(), 0, "q_enable".to_owned()), // multiply q_enable by all PolyExpr stored under CompilationUnit 
                    poly.expr.clone(),
                ]),
            })
            .collect();

        unit.lookups = unit
            .lookups
            .iter()
            .map(|lookup| PolyLookup {
                exprs: lookup
                    .exprs
                    .iter()
                    .map(|(src, dest)| {
                        (
                            PolyExpr::Mul(vec![
                                PolyExpr::<F>::Query(q_enable.clone(), 0, "q_enable".to_owned()), // multiply q_enable by all PolyLookup's source column stored under CompilationUnit. ??? don't we have an enable column for lookup already that multiplies to the source column?
                                src.clone(),
                            ]),
                            dest.clone(),
                        )
                    })
                    .collect(),
            })
            .collect();
    }
}
