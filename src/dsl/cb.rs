use std::{fmt::Debug, vec};

use halo2_proofs::arithmetic::Field;

use crate::ast::{query::Queriable, Expr, ToExpr};

use super::StepTypeHandler;

#[derive(Clone)]
pub struct Constraint<F> {
    pub annotation: String,
    pub expr: Expr<F>,
}

impl<F: Debug> From<Expr<F>> for Constraint<F> { // converts Expr<F> to Constraint<F>
    fn from(expr: Expr<F>) -> Self {
        let annotation = format!("{:?}", &expr); // Expr<F> has a Debug trait implementation which has the fmt function that defines formatter for the Expr<F> type
        // {:?} indicates the format! macro uses the formatter implemented in the Debug trait
        Self { expr, annotation }
    }
}

impl<F> From<Queriable<F>> for Constraint<F> { // converts Queriable<F> to Constraint<F>
    fn from(query: Queriable<F>) -> Self {
        annotate(query.annotation(), Expr::Query(query))
    }
}

impl<F: Field + From<u64> + Debug> From<i32> for Constraint<F> { 
    fn from(v: i32) -> Self { // converts i32 into Constraint<F>
        v.expr().into()  // expr converts v:i32 to Expr<F>; into converts Expr<F> to Constraint, because From<Constraint<F>> is implemented by Expr type
    }
}

macro_rules! impl_cb_like {
    ($type:ty) => {
        impl<F: From<u64> + Debug> From<$type> for Constraint<F> { 
            #[inline]
            fn from(value: $type) -> Self { // convert from $type to Constraint<F>
                Expr::Const(F::from(value as u64)).into() // wrap type to u64 first, then to F using the from function, and to Expr, and finally to Constraint
            }
        }
    };
}
// convert the following types to Constraint<F> by implementing the From<$type> traits
impl_cb_like!(bool); 
impl_cb_like!(u8);
impl_cb_like!(u32);
impl_cb_like!(u64);
impl_cb_like!(usize);

impl<F> Debug for Constraint<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.annotation)
    }
}

pub fn and<F: From<u64>, E: Into<Constraint<F>>, I: IntoIterator<Item = E>>( // ???: why use an into Iterator instead of Iterator<Item>
    inputs: I,
) -> Constraint<F> {
    let mut annotations: Vec<String> = vec![];
    let mut expr: Expr<F> = 1u64.expr();

    for constraint in inputs.into_iter() { // into_iter function converts the IntoIterator<Item> into an Iterator<Item>
        let constraint = constraint.into(); // each item is generic type E that impl Into<Constraint<F>> trait
        annotations.push(constraint.annotation); // push each annotation of the constraints into an annotation vector

        expr = expr * constraint.expr; // ??? is my understanding correct: multiply all the expressions (A, B, ...) and constraint them to zero is equivalent to A and B and ...
    }

    Constraint {
        annotation: format!("({})", annotations.join(" AND ")),
        expr,
    }
}

pub fn or<
    F: From<u64> + Debug,
    E: Into<Constraint<F>> + Clone,
    I: IntoIterator<Item = E> + Clone,
>(
    inputs: I,
) -> Constraint<F> {
    let mut annotations: Vec<String> = vec![];
    let mut exprs: Vec<Expr<F>> = vec![];

    for constraint in inputs.into_iter() {
        let constraint = constraint.into();
        annotations.push(constraint.annotation);
        exprs.push(constraint.expr); // a vector of expression instead of chaining them using the multiplication operator as in the and function above
    }

    let result = not(and(exprs.into_iter().map(not))); // basically chaining all the expressions in the stack by or, because not(and(not A, not B, not ...)) is equivalent to A or B or ...

    Constraint {
        annotation: format!("({})", annotations.join(" OR ")),
        expr: result.expr,
    }
}

pub fn xor<F: From<u64> + Clone, LHS: Into<Expr<F>>, RHS: Into<Expr<F>>>(
    lhs: LHS,
    rhs: RHS,
) -> Expr<F> {
    let lhs = lhs.into();
    let rhs = rhs.into();

    lhs.clone() + rhs.clone() - 2u64.expr() * lhs * rhs // ??? equivalent to a(1-b) + b(1-a), not sure why this is xor? !!! should it be lhs + rhs - 2 * lhs * rhs - 1 instead?
}

pub fn eq<F, LHS: Into<Constraint<F>>, RHS: Into<Constraint<F>>>( // lhs - rhs = 0
    lhs: LHS,
    rhs: RHS,
) -> Constraint<F> {
    let lhs = lhs.into();
    let rhs = rhs.into();

    Constraint {
        annotation: format!("{} == {}", lhs.annotation, rhs.annotation),
        expr: lhs.expr - rhs.expr,
    }
}

pub fn select< // selector * when_true + (1 - selector) * when_false == 0
    F: From<u64> + Clone,
    T1: Into<Constraint<F>>,
    T2: Into<Constraint<F>>,
    T3: Into<Constraint<F>>,
>(
    selector: T1,
    when_true: T2,
    when_false: T3,
) -> Constraint<F> {
    let selector = selector.into();
    let when_true = when_true.into();
    let when_false = when_false.into();

    Constraint {
        annotation: format!(
            "if({})then({})else({})",
            selector.annotation, when_true.annotation, when_false.annotation
        ),
        expr: selector.expr.clone() * when_true.expr
            + (1u64.expr() - selector.expr) * when_false.expr,
    }
}

// not, works only if the parameter is 0 or 1
pub fn not<F: From<u64>, T: Into<Constraint<F>>>(constraint: T) -> Constraint<F> { // !!!: should constrain T to 0 or 1
    let constraint = constraint.into();
    let annotation = format!("NOT({})", constraint.annotation);
    let expr = 1u64.expr() - constraint.expr;

    Constraint { annotation, expr }
}

/// Is zero
pub fn isz<F, T: Into<Constraint<F>>>(constraint: T) -> Constraint<F> { // ??? why do this when there's a gadget already?
    let constraint = constraint.into(); // basically the expression itself is constrained to zero

    Constraint {
        annotation: format!("0 == {}", constraint.annotation),
        expr: constraint.expr,
    }
}

pub fn if_next_step<F: Clone, T: Into<Constraint<F>>>( // ??? what's this function used for?
    step_type: StepTypeHandler,
    constraint: T,
) -> Constraint<F> {
    let constraint = constraint.into();

    let annotation = format!(
        "if(next step is {})then({})",
        step_type.annotation, constraint.annotation
    );

    Constraint {
        expr: step_type.next() * constraint.expr,
        annotation,
    }
}

pub fn annotate<F, E: Into<Expr<F>>>(annotation: String, expr: E) -> Constraint<F> { // builds an annotated Constraint using a annotation string and an Into<Expr<F>>
    Constraint {
        annotation,
        expr: expr.into(),
    }
}

pub fn rlc<F: From<u64>, E: Into<Expr<F>> + Clone, R: Into<Expr<F>> + Clone>( // returns a random linear combination using a slice of expressions and a randomness
    exprs: &[E], // slice of type E provides read only access to the vector rather than creating a clone or taking ownership of vector using Vec<E>
    randomness: R,
) -> Expr<F> {
    if !exprs.is_empty() {
        let mut exprs = exprs.iter().rev().map(|e| e.clone().into()); 
        let init = exprs.next().expect("should not be empty");

        exprs.fold(init, |acc, expr| acc * randomness.clone().into() + expr) // ??? looks like (((expr * rand + expr) * rand + expr) * rand + expr) ... rather than an RLC
    } else {
        0u64.expr()
    }
}
