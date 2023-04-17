use crate::{
    ast::{query::Queriable, Circuit, Expr, StepType, StepTypeUUID},
    compiler::{FixedGenContext, TraceContext, WitnessGenContext},
    util::uuid,
};

use halo2_proofs::plonk::{Advice, Column as Halo2Column, Fixed};

use self::cb::Constraint;

pub struct CircuitContext<F, TraceArgs, StepArgs> {
    sc: Circuit<F, TraceArgs, StepArgs>,
}

impl<F, TraceArgs, StepArgs> CircuitContext<F, TraceArgs, StepArgs> {
    pub fn forward(&mut self, name: &str) -> Queriable<F> {
        Queriable::Forward(self.sc.add_forward(name, 0), false) // initialize to false so that rotation is zero; add ForwardSignal to the Circuit under CircuitContext 
    }

    pub fn forward_with_phase(&mut self, name: &str, phase: usize) -> Queriable<F> {
        Queriable::Forward(self.sc.add_forward(name, phase), false) 
    }

    pub fn import_halo2_advice(&mut self, name: &str, column: Halo2Column<Advice>) -> Queriable<F> {
        Queriable::Halo2AdviceQuery(self.sc.add_halo2_advice(name, column), 0) 
    }

    pub fn import_halo2_fixed(&mut self, name: &str, column: Halo2Column<Fixed>) -> Queriable<F> {
        Queriable::Halo2FixedQuery(self.sc.add_halo2_fixed(name, column), 0)
    }

    pub fn step_type(&mut self, name: &str) -> StepTypeHandler { // add a new StepType using a StepTypeHandler that defines the name string, no StepType definition yet
        let handler = StepTypeHandler::new(name.to_string());

        self.sc.add_step_type(handler, name); // save the Handler to the Circuit, but only in the annotaiton field (see add_step_type function)

        handler
    }

    pub fn step_type_def<D>(&mut self, handler: StepTypeHandler, def: D) // StepType definition
    where
        D: FnOnce(&mut StepTypeContext<F, StepArgs>),
    {
        let mut context =
            StepTypeContext::<F, StepArgs>::new(handler.uuid(), handler.annotation.to_string());

        def(&mut context); // call the def function to manipulate the StepTypeContext, which contains StepType
        // the def function typically add constraints to a StepType and define witness generation

        self.sc.add_step_type_def(context.step_type); // save the StepType to the circuit
    }

    pub fn trace<D>(&mut self, def: D) 
    where
        D: Fn(&mut dyn TraceContext<StepArgs>, TraceArgs) + 'static, // TraceContext trait has an "add" function that adds step instantiation defined in the compiler
    {
        self.sc.set_trace(def); // ast function invoked
    }

    pub fn fixed_gen<D>(&mut self, def: D)
    where
        D: Fn(&mut dyn FixedGenContext<F>) + 'static, // FixedGenContext has an "assign" function defined in the compiler
    {
        self.sc.set_fixed_gen(def); // ast function invoked
    }

    pub fn pragma_first_step(&mut self, step_type: StepTypeHandler) {
        self.sc.first_step = Some(step_type);
    }

    pub fn pragma_last_step(&mut self, step_type: StepTypeHandler) {
        self.sc.last_step = Some(step_type);
    }
}

pub struct StepTypeContext<F, Args> { // ??? why wrap StepType in a StepTypeContext
    step_type: StepType<F, Args>,
}

impl<F, Args> StepTypeContext<F, Args> { // invoke ast functions to add constraints to a StepType
    pub fn new(uuid: u32, name: String) -> Self { 
        Self {
            step_type: StepType::new(uuid, name),
        }
    }

    pub fn internal(&mut self, name: &str) -> Queriable<F> { 
        Queriable::Internal(self.step_type.add_signal(name))
    }

    pub fn constr<C: Into<Constraint<F>>>(&mut self, constraint: C) {
        let constraint = constraint.into();

        self.step_type
            .add_constr(constraint.annotation, constraint.expr);
    }

    pub fn transition<C: Into<Constraint<F>>>(&mut self, constraint: C) {
        let constraint = constraint.into();

        self.step_type
            .add_transition(constraint.annotation, constraint.expr);
    }

    pub fn lookup(&mut self, _annotation: &str, exprs: Vec<(Expr<F>, Expr<F>)>) {
        // TODO annotate lookup
        self.step_type.add_lookup(exprs)
    }

    pub fn wg<D>(&mut self, def: D)
    where
        D: Fn(&mut dyn WitnessGenContext<F>, Args) + 'static, // WitnessGenContext has one assign function that takes a Queriable on LHS and an F:Field on RHS
        // the WitnessGenContext trait is implemented by the halo2 backend
    {
        self.step_type.set_wg(def); // ast function that assigns def function to the wg field of a StepType type
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StepTypeHandler {
    id: StepTypeUUID,
    pub annotation: &'static str,
}

impl StepTypeHandler { // StepTypeHandler just stores the annotation; while StepTypeContext wraps the StepType and has constraints and wg stored under it
    fn new(annotation: String) -> Self {
        Self {
            id: uuid(),
            annotation: Box::leak(annotation.into_boxed_str()),
        }
    }

    pub fn uuid(&self) -> u32 {
        self.id
    }

    pub fn next<F>(&self) -> Queriable<F> {
        Queriable::StepTypeNext(*self) // ??? what's StepTypeNext used for?
    }
}

pub struct ForwardSignalHandler {
    // fs: ForwardSignal,
}

pub fn circuit<F, TraceArgs, StepArgs, D>(_name: &str, def: D) -> Circuit<F, TraceArgs, StepArgs> // this is the main circuit function we invoke and put everything in
where
    D: Fn(&mut CircuitContext<F, TraceArgs, StepArgs>), // CircuitContext stores a single Circuit instance
{
    // TODO annotate circuit
    let mut context = CircuitContext {
        sc: Circuit::default(),
    };

    def(&mut context); // def is the main circuit building function, inside which we define step types

    context.sc // returns the Circuit
}

pub mod cb;
