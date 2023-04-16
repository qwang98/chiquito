use std::fmt::Debug;
use std::ops::{Add, Mul, Neg, Sub};

use halo2_proofs::{arithmetic::Field, plonk::Expression};

use crate::dsl::cb::Constraint;

use self::query::Queriable;

pub trait ToExpr<F> { // trait version of expr
    fn expr(&self) -> Expr<F>;
}

pub trait ToField<F> {
    fn field(&self) -> F;
}

#[derive(Clone)]
pub enum Expr<F> {
    Const(F),
    Sum(Vec<Expr<F>>),
    Mul(Vec<Expr<F>>),
    Neg(Box<Expr<F>>), // ??? what is box used here for
    Pow(Box<Expr<F>>, u32),
    Query(Queriable<F>),
    Halo2Expr(Expression<F>), // halo2 Expression type, including Advice, Fixed, etc.
}

impl<F: Debug> Debug for Expr<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Const(arg0) => write!(f, "{:?}", arg0),
            Self::Sum(arg0) => write!( // loop through the vector elements in and concatenate them using "+"
                f,
                "({})",
                arg0.iter()
                    .map(|v| format!("{:?}", v))
                    .collect::<Vec<String>>()
                    .join(" + ")
            ),
            Self::Mul(arg0) => write!( // loop through the vector elements in and concatenate them using "*"
                f, 
                "({})",
                arg0.iter()
                    .map(|v| format!("{:?}", v))
                    .collect::<Vec<String>>()
                    .join(" * ")
            ),
            Self::Neg(arg0) => write!(f, "-{:?}", arg0),
            Self::Pow(arg0, arg1) => write!(f, "({:?})^{}", arg0, arg1),
            Self::Query(arg0) => write!(f, "{:?}", arg0),
            Self::Halo2Expr(arg0) => write!(f, "halo2({:?})", arg0),
        }
    }
}

impl<F: Clone> ToExpr<F> for Expr<F> { // implements ToExpr trait
    fn expr(&self) -> Expr<F> {
        self.clone()
    }
}

impl<F> From<Constraint<F>> for Expr<F> {
    fn from(c: Constraint<F>) -> Self {
        c.expr
    }
}

impl<F> From<Queriable<F>> for Expr<F> {
    fn from(value: Queriable<F>) -> Self {
        Expr::Query(value)
    }
}

impl<F, RHS: Into<Expr<F>>> Add<RHS> for Expr<F> { // RHS is a generic trait here as well
    type Output = Self; // Output type is defined but never used, because it's required by rust for Add trait and the rust compiler checks the resulting type matches the Output type
    fn add(self, rhs: RHS) -> Self {
        use Expr::*;
        match self { // if the expression itself is:
            Sum(mut xs) => { // a sum enum type, then push the rhs Expr<F> into the vector and get the sum, returning Sum is an enum type of Expr<F>
                xs.push(rhs.into());
                Sum(xs)
            }
            e => Sum(vec![e, rhs.into()]), // if not Sum type, then use this function instead, e is a non-Sum catch all parameter internal to 'match' function
        }
    }
}

impl<F, RHS: Into<Expr<F>>> Sub<RHS> for Expr<F> {
    type Output = Self;
    fn sub(self, rhs: RHS) -> Self {
        use Expr::*;
        match self {
            Sum(mut xs) => {
                xs.push(rhs.into().neg());
                Sum(xs)
            }
            e => Sum(vec![e, rhs.into().neg()]), // define this separately for non-Sum type, because other types will be expressed as chained functions, but the sum type you can simply input the expression as one of the vector elements and evaluate the Sum, instead of evaluating Sum(Sum(Vec<Expr<F>>), Expr<F>)
        }
    }
}

impl<F, RHS: Into<Expr<F>>> Mul<RHS> for Expr<F> {
    type Output = Self;
    fn mul(self, rhs: RHS) -> Self {
        use Expr::*;
        match self {
            Mul(mut xs) => { // Mul instead of Expr::Mul here, because Expr::* is imported right above
                xs.push(rhs.into());
                Mul(xs)
            }
            e => Mul(vec![e, rhs.into()]),
        }
    }
}

impl<F> Neg for Expr<F> {
    type Output = Self; 
    fn neg(self) -> Self {
        match self {
            Expr::Neg(xs) => *xs, // if the expression is already negated, then we are negating a negation, so we can just return the boxed Expr<F> value, * here dereferences the Box
            e => Expr::Neg(Box::new(e)), // apply a box and then wrap it in Neg for future evaluation
            // ??? why use a Box type above?
        }
    }
}

// add, sub, neg, and mul functions: add RHS to one enum type if the LHS (self) has the same type as the calculation operation OR wrap the LHS in a new enum type

macro_rules! impl_expr_like { // defining a macro that can build Expr from multiple simple data types
    ($type:ty) => {
        impl<F: From<u64>> From<$type> for Expr<F> { // From<u64> trait is implemented for F type, so that F::from can convert from u64 to F; From<$type> trait is implemented for Expr<F>, so that Expr<F> can convert from $type to Expr<F>
            #[inline]
            fn from(value: $type) -> Self { // from function converts simple value to Expr::Const<F>
                Expr::Const(F::from(value as u64))
            }
        }

        impl<F: From<u64>> $crate::ast::ToExpr<F> for $type { // ToExpr<F> trait is implemented, so that expr function can evaluate $type to Expr<F>
            #[inline]
            fn expr(&self) -> Expr<F> {
                Expr::Const(F::from(*self as u64))
            }
        }

        impl<F: From<u64>> $crate::ast::ToField<F> for $type { // ToField<F> trait is implemented, so that field function can evaluate $type to F
            #[inline]
            fn field(&self) -> F {
                F::from(*self as u64)
            }
        }
    };
}

// in summary, from converts $type to Expr<F>, expr converts $type to Expr<F>, and field converts $type to F
// ??? what's the difference between from and expr functions above?

impl_expr_like!(bool);
impl_expr_like!(u8);
impl_expr_like!(u32);
impl_expr_like!(u64);
impl_expr_like!(usize);

impl<F: Field + From<u64>> From<i32> for Expr<F> { // basically converts signed integer to Expr<F>
    #[inline]
    fn from(value: i32) -> Self {
        Expr::Const(
            F::from(value.unsigned_abs() as u64)
                * if value.is_negative() {
                    -F::one()
                } else {
                    F::one()
                },
        )
    }
}

impl<F: Field + From<u64>> ToExpr<F> for i32 { // converts signed integer to Expr<F> 
    #[inline]
    fn expr(&self) -> Expr<F> {
        Expr::Const(
            F::from(self.unsigned_abs() as u64)
                * if self.is_negative() {
                    -F::one()
                } else {
                    F::one()
                },
        )
    }
}

impl<F: Field + From<u64>> ToField<F> for i32 { // converts signed integer to F (which implements Field)
    #[inline]
    fn field(&self) -> F {
        F::from(self.unsigned_abs() as u64)
            * if self.is_negative() {
                -F::one()
            } else {
                F::one()
            }
    }
}

impl<F> From<Expression<F>> for Expr<F> { // converts Expression<F>, i.e. Halo2 native Expression<F> type, to Expr<F>
    #[inline]
    fn from(value: Expression<F>) -> Self {
        Expr::Halo2Expr(value)
    }
}

// ??? overall, what's the purpose of wrapping Expression<F> around a new Expr<F> type?

pub mod query {
    use std::{
        fmt::Debug,
        marker::PhantomData,
        ops::{Add, Mul, Neg, Sub},
    };

    use crate::{
        ast::{ForwardSignal, ImportedHalo2Advice, ImportedHalo2Fixed, InternalSignal},
        dsl::StepTypeHandler,
    };

    use super::{Expr, ToExpr}; // super refers to this crate, i.e. the upper level of mod query

    // Queriable
    #[derive(Clone, Copy, PartialEq, Eq)] // clone allows explicit clone by calling clone function, copy doesn't require this
    pub enum Queriable<F> { 
        Internal(InternalSignal), // signal
        Forward(ForwardSignal, bool), // signal
        StepTypeNext(StepTypeHandler),
        Halo2AdviceQuery(ImportedHalo2Advice, i32), // advice column
        Halo2FixedQuery(ImportedHalo2Fixed, i32), // fixed column
        #[allow(non_camel_case_types)]
        _unaccessible(PhantomData<F>),
    }

    impl<F> Debug for Queriable<F> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.annotation())
        }
    }

    impl<F> Queriable<F> {
        pub fn next(&self) -> Queriable<F> {
            use Queriable::*;
            match self {
                Forward(s, rot) => { // ??? explain the use of rot in Forward and Halo2 Expr::Query::Foward and Expr::Query::Halo2 as defined below; i think it means rotation? why Forward rotation only has 0 or 1 but not for halo2 columns?
                    if !*rot { 
                        Forward(*s, true) // rot needs to be false to call next on the Queriable object
                    } else {
                        panic!("jarrl: cannot rotate next(forward)")
                    }
                }
                Halo2AdviceQuery(s, rot) => Halo2AdviceQuery(*s, rot + 1),
                Halo2FixedQuery(s, r) => Halo2FixedQuery(*s, r + 1),
                _ => panic!("can only next a forward or halo2 column"), // any other Queriable enum can't call the next function
            }
        }

        pub fn uuid(&self) -> u32 {
            match self {
                Queriable::Internal(s) => s.uuid(),
                Queriable::Forward(s, _) => s.uuid(),
                Queriable::StepTypeNext(s) => s.uuid(),
                Queriable::Halo2AdviceQuery(s, _) => s.uuid(),
                Queriable::Halo2FixedQuery(s, _) => s.uuid(),
                Queriable::_unaccessible(_) => panic!("jarrl wrong queriable type"),
            }
        }

        pub fn annotation(&self) -> String {
            match self {
                Queriable::Internal(s) => s.annotation.to_string(),
                Queriable::Forward(s, rot) => {
                    if !rot {
                        s.annotation.to_string()
                    } else {
                        format!("next({})", s.annotation) // annotation with one rotation, i.e. "next(annotation)"
                    }
                }
                Queriable::StepTypeNext(s) => s.annotation.to_string(),
                Queriable::Halo2AdviceQuery(s, rot) => {
                    if *rot != 0 {
                        format!("{}(rot {})", s.annotation, rot) // annotation with rotation number
                    } else { 
                        s.annotation.to_string() // plain annotation without rotation
                    }
                }
                Queriable::Halo2FixedQuery(s, rot) => {
                    if *rot != 0 {
                        format!("{}(rot {})", s.annotation, rot)
                    } else {
                        s.annotation.to_string()
                    }
                }
                Queriable::_unaccessible(_) => todo!(),
            }
        }
    }

    impl<F: Clone> ToExpr<F> for Queriable<F> { // return Expr::Query by calling expr function (required for ToExpr trait)
        fn expr(&self) -> Expr<F> {
            Expr::Query((*self).clone())
        }
    }

    impl<F: Clone, RHS: Into<Expr<F>>> Add<RHS> for Queriable<F> {
        type Output = Expr<F>; // Output type required for Add trait

        fn add(self, rhs: RHS) -> Self::Output {
            self.expr() + rhs // + is defined as Add for Expr<F>, so self.expr() + rhs is essentially self.expr().add(rhs), and Expr<F>::add takes an Into<Expr<F>>
        }
    }

    impl<F: Clone, RHS: Into<Expr<F>>> Sub<RHS> for Queriable<F> {
        type Output = Expr<F>;

        fn sub(self, rhs: RHS) -> Self::Output {
            self.expr() - rhs
        }
    }

    impl<F: Clone, RHS: Into<Expr<F>>> Mul<RHS> for Queriable<F> {
        type Output = Expr<F>;

        fn mul(self, rhs: RHS) -> Self::Output {
            self.expr() * rhs
        }
    }

    impl<F: Clone> Neg for Queriable<F> {
        type Output = Expr<F>;

        fn neg(self) -> Self::Output {
            self.expr().neg()
        }
    }
}
