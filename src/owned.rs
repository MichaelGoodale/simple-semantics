//! Includes [`OwnedRootedLambdaPool`] so that you can easily represent [`RootedLambdaPool`]s
//! without borrowing, at a small expense when converting between borrowed and owned versions.
//! Also applies to [`OwnedValue`]
//!
//! ```

use crate::lambda::{Neutral, Value};

/// # fn main() -> anyhow::Result<()> {
/// let s = "lambda <a,t> P P".to_string();
/// //x has the lifetime of s here.
/// let x = RootedLambdaPool::<Expr>::parse(s.as_str())?;
/// let y = x.into_owned();
/// drop(s);
///
/// assert_eq!(
///     y.into_borrowed(),
///     RootedLambdaPool::parse("lambda <a,t> P P")?,
/// );
///
/// # Ok(())
/// # }
/// ```
use crate::{
    Event,
    lambda::{
        Bvar, ExprType, FreeVar, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool,
        Literal, RootedLambdaPool, types::LambdaType,
    },
    language::{ActorOrEvent, BinOp, Constant, Expr, MonOp, Quantifier},
};

///An owned variant of [`FreeVar`]
#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[expect(missing_docs)]
pub enum OwnedFreeVar {
    Named(String),
    Anonymous(usize),
}

impl OwnedFreeVar {
    ///Converts to [`FreeVar`]
    pub fn into_borrowed<'a>(&'a self) -> FreeVar<'a> {
        self.into()
    }
}

impl FreeVar<'_> {
    ///Converts to [`OwnedFreeVar`]
    pub fn into_owned(self) -> OwnedFreeVar {
        self.into()
    }
}

impl<'a> From<&'a OwnedFreeVar> for FreeVar<'a> {
    fn from(value: &'a OwnedFreeVar) -> Self {
        match value {
            OwnedFreeVar::Named(x) => FreeVar::Named(x.as_str()),
            OwnedFreeVar::Anonymous(i) => FreeVar::Anonymous(*i),
        }
    }
}

impl From<FreeVar<'_>> for OwnedFreeVar {
    fn from(value: FreeVar<'_>) -> Self {
        match value {
            FreeVar::Named(x) => OwnedFreeVar::Named(x.to_string()),
            FreeVar::Anonymous(i) => OwnedFreeVar::Anonymous(i),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum OwnedLambdaExpr<T> {
    Lambda(LambdaExprRef, LambdaType),
    BoundVariable(Bvar, LambdaType),
    FreeVariable(OwnedFreeVar, LambdaType),
    Application {
        subformula: LambdaExprRef,

        argument: LambdaExprRef,
    },
    LanguageOfThoughtExpr(T, ExprType),
}

impl<'a, OwnedType, RefType> From<&'a OwnedLambdaExpr<OwnedType>> for LambdaExpr<'a, RefType>
where
    RefType: From<&'a OwnedType>,
{
    fn from(value: &'a OwnedLambdaExpr<OwnedType>) -> Self {
        match value {
            OwnedLambdaExpr::Lambda(i, t) => LambdaExpr::Lambda(*i, t.clone()),
            OwnedLambdaExpr::BoundVariable(bvar, t) => LambdaExpr::BoundVariable(*bvar, t.clone()),
            OwnedLambdaExpr::FreeVariable(var, t) => {
                LambdaExpr::FreeVariable(var.into(), t.clone())
            }
            OwnedLambdaExpr::Application {
                subformula,
                argument,
            } => LambdaExpr::Application {
                subformula: *subformula,
                argument: *argument,
            },
            OwnedLambdaExpr::LanguageOfThoughtExpr(t, expr_type) => {
                LambdaExpr::LanguageOfThoughtExpr(t.into(), *expr_type)
            }
        }
    }
}

impl<OwnedType, RefType> From<LambdaExpr<'_, RefType>> for OwnedLambdaExpr<OwnedType>
where
    OwnedType: From<RefType>,
{
    fn from(value: LambdaExpr<'_, RefType>) -> Self {
        match value {
            LambdaExpr::Lambda(i, t) => OwnedLambdaExpr::Lambda(i, t),
            LambdaExpr::BoundVariable(bvar, t) => OwnedLambdaExpr::BoundVariable(bvar, t),
            LambdaExpr::FreeVariable(var, t) => OwnedLambdaExpr::FreeVariable(var.into(), t),
            LambdaExpr::Application {
                subformula,
                argument,
            } => OwnedLambdaExpr::Application {
                subformula,
                argument,
            },
            LambdaExpr::LanguageOfThoughtExpr(expr, expr_type) => {
                OwnedLambdaExpr::LanguageOfThoughtExpr(expr.into(), expr_type)
            }
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct OwnedLambdaPool<T>(Vec<OwnedLambdaExpr<T>>);

impl<'a, OwnedType, RefType> From<&'a OwnedLambdaPool<OwnedType>> for LambdaPool<'a, RefType>
where
    RefType: LambdaLanguageOfThought,
    LambdaExpr<'a, RefType>: From<&'a OwnedLambdaExpr<OwnedType>>,
{
    fn from(value: &'a OwnedLambdaPool<OwnedType>) -> Self {
        LambdaPool(value.0.iter().map(|x| x.into()).collect())
    }
}

impl<'a, OwnedType, RefType> From<LambdaPool<'a, RefType>> for OwnedLambdaPool<OwnedType>
where
    RefType: LambdaLanguageOfThought,
    OwnedLambdaExpr<OwnedType>: From<LambdaExpr<'a, RefType>>,
{
    fn from(value: LambdaPool<'a, RefType>) -> Self {
        OwnedLambdaPool(value.0.into_iter().map(|x| x.into()).collect())
    }
}

///Struct that is just [`RootedLambdaPool`] but entirely self owning.
///It implements `From<&'a OwnedRootedLambdaPool<T> for RootedLambdaPool<'a T2>` for cases where you
///don't want lifetimes, at a cloning cost.
#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct OwnedRootedLambdaPool<T> {
    root: LambdaExprRef,
    pool: OwnedLambdaPool<T>,
}

impl<'a, OwnedType, RefType> From<&'a OwnedRootedLambdaPool<OwnedType>>
    for RootedLambdaPool<'a, RefType>
where
    RefType: LambdaLanguageOfThought,
    LambdaExpr<'a, RefType>: From<&'a OwnedLambdaExpr<OwnedType>>,
{
    fn from(value: &'a OwnedRootedLambdaPool<OwnedType>) -> Self {
        RootedLambdaPool {
            pool: (&value.pool).into(),
            root: value.root,
        }
    }
}

impl<'a, OwnedType, RefType> From<RootedLambdaPool<'a, RefType>>
    for OwnedRootedLambdaPool<OwnedType>
where
    RefType: LambdaLanguageOfThought,
    OwnedLambdaExpr<OwnedType>: From<LambdaExpr<'a, RefType>>,
{
    fn from(value: RootedLambdaPool<'a, RefType>) -> Self {
        OwnedRootedLambdaPool {
            pool: value.pool.into(),
            root: value.root,
        }
    }
}

///Owned variant of [`Expr`] solely for self-owning, typically in FFI.
///Incurs a small conversion cost.
#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[expect(missing_docs)]
pub enum OwnedExpr {
    Quantifier {
        quantifier: Quantifier,
        var_type: ActorOrEvent,
    },
    Actor(String),
    Event(Event),
    Binary(BinOp),
    Unary(MonOp),
    Everyone,
    EveryEvent,
    Contradiction,
    Tautology,
    Property(String, ActorOrEvent),
}

impl<'a> From<&'a OwnedExpr> for Expr<'a> {
    fn from(value: &'a OwnedExpr) -> Self {
        match value {
            OwnedExpr::Quantifier {
                quantifier,
                var_type,
            } => Expr::Quantifier {
                quantifier: *quantifier,
                var_type: *var_type,
            },
            OwnedExpr::Actor(actor) => Expr::Actor(actor.as_str()),
            OwnedExpr::Event(event) => Expr::Event(*event),
            OwnedExpr::Binary(bin_op) => Expr::Binary(*bin_op),
            OwnedExpr::Unary(mon_op) => Expr::Unary(*mon_op),
            OwnedExpr::Everyone => Expr::Constant(Constant::Everyone),
            OwnedExpr::EveryEvent => Expr::Constant(Constant::EveryEvent),
            OwnedExpr::Contradiction => Expr::Constant(Constant::Contradiction),
            OwnedExpr::Tautology => Expr::Constant(Constant::Tautology),
            OwnedExpr::Property(property, actor_or_event) => {
                Expr::Constant(Constant::Property(property.as_str(), *actor_or_event))
            }
        }
    }
}

impl<'a> From<Expr<'a>> for OwnedExpr {
    fn from(value: Expr<'a>) -> Self {
        match value {
            Expr::Quantifier {
                quantifier,
                var_type,
            } => OwnedExpr::Quantifier {
                quantifier,
                var_type,
            },
            Expr::Actor(actor) => OwnedExpr::Actor(actor.to_owned()),
            Expr::Event(event) => OwnedExpr::Event(event),
            Expr::Binary(bin_op) => OwnedExpr::Binary(bin_op),
            Expr::Unary(mon_op) => OwnedExpr::Unary(mon_op),
            Expr::Constant(Constant::Everyone) => OwnedExpr::Everyone,
            Expr::Constant(Constant::EveryEvent) => OwnedExpr::EveryEvent,
            Expr::Constant(Constant::Contradiction) => OwnedExpr::Contradiction,
            Expr::Constant(Constant::Tautology) => OwnedExpr::Tautology,
            Expr::Constant(Constant::Property(property, actor_or_event)) => {
                OwnedExpr::Property(property.to_owned(), actor_or_event)
            }
        }
    }
}

///A pair of traits with [`IntoBorrowedLOT`] that allows you to specify for a given LOT expression
///what its owned type is.
pub trait IntoOwnedLOT: LambdaLanguageOfThought + Sized {
    ///How it is when owned
    type OwnedExpression: From<Self>;
}

///A pair of traits with [`IntoBorrowedLOT`] that allows you to specify for a given owned LOT expression
///what its normal, reference type is.
pub trait IntoBorrowedLOT: Sized {
    ///How it is when referenced
    type RefExpression<'a>: LambdaLanguageOfThought + From<&'a Self>
    where
        Self: 'a;
}

impl<'a> IntoOwnedLOT for Expr<'a> {
    type OwnedExpression = OwnedExpr;
}

impl IntoBorrowedLOT for OwnedExpr {
    type RefExpression<'a> = Expr<'a>;
}

impl<T> RootedLambdaPool<'_, T>
where
    T: IntoOwnedLOT,
{
    ///Gets the owned version of [`RootedLambdaPool`]
    pub fn into_owned(self) -> OwnedRootedLambdaPool<T::OwnedExpression> {
        self.into()
    }
}

impl<T> OwnedRootedLambdaPool<T>
where
    T: IntoBorrowedLOT,
{
    ///Converts to the usable, version: [`RootedLambdaPool`] instead of the owned version.
    pub fn as_borrowed<'a>(&'a self) -> RootedLambdaPool<'a, T::RefExpression<'a>> {
        self.into()
    }
}

///Owned variant of [`Literal`] solely for self-owning, typically in FFI.
///Incurs a small conversion cost.
#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[expect(missing_docs)]
pub enum OwnedLiteral {
    Bool(bool),
    Actor(String),
    Event(Event),
    ActorSet(Vec<String>),
    EventSet(Vec<Event>),
    TruthTable { on_false: bool, on_true: bool },
}

impl<'a> From<&'a OwnedLiteral> for Literal<'a> {
    fn from(value: &'a OwnedLiteral) -> Self {
        match value {
            OwnedLiteral::Bool(value) => Literal::Bool(*value),
            OwnedLiteral::Actor(value) => Literal::Actor(value),
            OwnedLiteral::Event(value) => Literal::Event(*value),
            OwnedLiteral::ActorSet(values) => {
                Literal::ActorSet(values.iter().map(String::as_str).collect())
            }
            OwnedLiteral::EventSet(values) => Literal::EventSet(values.clone()),
            OwnedLiteral::TruthTable { on_false, on_true } => Literal::TruthTable {
                on_false: *on_false,
                on_true: *on_true,
            },
        }
    }
}

impl From<Literal<'_>> for OwnedLiteral {
    fn from(value: Literal<'_>) -> Self {
        match value {
            Literal::Bool(value) => OwnedLiteral::Bool(value),
            Literal::Actor(value) => OwnedLiteral::Actor(value.to_owned()),
            Literal::Event(value) => OwnedLiteral::Event(value),
            Literal::ActorSet(values) => {
                OwnedLiteral::ActorSet(values.into_iter().map(str::to_owned).collect())
            }
            Literal::EventSet(values) => OwnedLiteral::EventSet(values),
            Literal::TruthTable { on_false, on_true } => {
                OwnedLiteral::TruthTable { on_false, on_true }
            }
        }
    }
}

impl Literal<'_> {
    fn into_owned(self) -> OwnedLiteral {
        self.into()
    }
}

impl OwnedLiteral {
    fn as_borrowed<'a>(&'a self) -> Literal<'a> {
        self.into()
    }
}

/// An owned variant of [`Value`]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[expect(missing_docs)]
pub enum OwnedValue<T> {
    Base(OwnedLiteral),
    Function(Box<OwnedValue<T>>, LambdaType, usize),
    Neutral(OwnedNeutral<T>),
    Primitive { expr: T, args: Vec<OwnedValue<T>> },
}

/// An owned variant of [`Neutral`]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[expect(missing_docs)]
pub enum OwnedNeutral<T> {
    FreeVar(OwnedFreeVar, LambdaType),
    BoundVar(Bvar, LambdaType),
    AppBoth(Box<OwnedNeutral<T>>, Box<OwnedNeutral<T>>),
    AppHead(Box<OwnedNeutral<T>>, Box<OwnedValue<T>>),
    AppArg(Box<OwnedValue<T>>, Box<OwnedNeutral<T>>),
    Primitive { expr: T, args: Vec<OwnedValue<T>> },
}

impl<T> Value<'_, '_, T>
where
    T: IntoOwnedLOT + Clone,
{
    ///Converts from a [`Value`] to the owned variant, [`OwnedValue`]
    pub fn into_owned(self) -> OwnedValue<T::OwnedExpression> {
        self.into()
    }
}

impl<'a, T> OwnedValue<T>
where
    T: IntoBorrowedLOT + 'a,
    T::RefExpression<'a>: Clone,
{
    ///Converts to the usable, version: [`Value`] instead of the owned version.
    pub fn as_borrowed(&'a self) -> Value<'a, 'a, T::RefExpression<'a>> {
        self.into()
    }
}

impl<'a, OwnedType, RefType> From<&'a OwnedValue<OwnedType>> for Value<'a, 'a, RefType>
where
    RefType: LambdaLanguageOfThought + From<&'a OwnedType> + Clone,
{
    fn from(value: &'a OwnedValue<OwnedType>) -> Self {
        match value {
            OwnedValue::Base(literal) => Value::Base(literal.as_borrowed()),
            OwnedValue::Function(body, ty, index) => {
                Value::Function(Box::new(Value::from(body.as_ref())), ty, *index)
            }
            OwnedValue::Neutral(neutral) => Value::Neutral(neutral.into()),
            OwnedValue::Primitive { expr, args } => Value::Primitive {
                expr: RefType::from(expr),
                args: args.iter().map(Value::from).collect(),
            },
        }
    }
}

impl<OwnedType, RefType> From<Value<'_, '_, RefType>> for OwnedValue<OwnedType>
where
    OwnedType: From<RefType>,
    RefType: LambdaLanguageOfThought + Clone,
{
    fn from(value: Value<'_, '_, RefType>) -> Self {
        match value {
            Value::Base(literal) => OwnedValue::Base(literal.into_owned()),
            Value::Function(body, ty, index) => {
                OwnedValue::Function(Box::new((*body).into()), (*ty).clone(), index)
            }
            Value::Neutral(neutral) => OwnedValue::Neutral(neutral.into()),
            Value::Primitive { expr, args } => OwnedValue::Primitive {
                expr: expr.into(),
                args: args.into_iter().map(Into::into).collect(),
            },
        }
    }
}

impl<'a, OwnedType, RefType> From<&'a OwnedNeutral<OwnedType>> for Neutral<'a, 'a, RefType>
where
    RefType: LambdaLanguageOfThought + From<&'a OwnedType> + Clone,
{
    fn from(value: &'a OwnedNeutral<OwnedType>) -> Self {
        match value {
            OwnedNeutral::FreeVar(var, ty) => Neutral::FreeVar(var.into(), ty),
            OwnedNeutral::BoundVar(bvar, ty) => Neutral::BoundVar(*bvar, ty),
            OwnedNeutral::AppBoth(left, right) => Neutral::AppBoth(
                Box::new(Neutral::from(left.as_ref())),
                Box::new(Neutral::from(right.as_ref())),
            ),
            OwnedNeutral::AppHead(head, arg) => Neutral::AppHead(
                Box::new(Neutral::from(head.as_ref())),
                Box::new(Value::from(arg.as_ref())),
            ),
            OwnedNeutral::AppArg(head, arg) => Neutral::AppArg(
                Box::new(Value::from(head.as_ref())),
                Box::new(Neutral::from(arg.as_ref())),
            ),
            OwnedNeutral::Primitive { expr, args } => Neutral::Primitive {
                expr: RefType::from(expr),
                args: args.iter().map(Value::from).collect(),
            },
        }
    }
}

impl<OwnedType, RefType> From<Neutral<'_, '_, RefType>> for OwnedNeutral<OwnedType>
where
    OwnedType: From<RefType>,
    RefType: LambdaLanguageOfThought + Clone,
{
    fn from(value: Neutral<'_, '_, RefType>) -> Self {
        match value {
            Neutral::FreeVar(var, ty) => OwnedNeutral::FreeVar(var.into(), (*ty).clone()),
            Neutral::BoundVar(bvar, ty) => OwnedNeutral::BoundVar(bvar, (*ty).clone()),
            Neutral::AppBoth(left, right) => {
                OwnedNeutral::AppBoth(Box::new((*left).into()), Box::new((*right).into()))
            }
            Neutral::AppHead(head, arg) => {
                OwnedNeutral::AppHead(Box::new((*head).into()), Box::new((*arg).into()))
            }
            Neutral::AppArg(head, arg) => {
                OwnedNeutral::AppArg(Box::new((*head).into()), Box::new((*arg).into()))
            }
            Neutral::Primitive { expr, args } => OwnedNeutral::Primitive {
                expr: expr.into(),
                args: args.into_iter().map(Into::into).collect(),
            },
        }
    }
}

#[cfg(test)]
mod test {
    use std::collections::BTreeMap;

    use crate::{
        Scenario,
        lambda::{Literal, RootedLambdaPool, Value},
        language::Expr,
    };

    #[test]
    fn test_ownership() -> anyhow::Result<()> {
        let s = "lambda <a,t> P P".to_string();
        let x = RootedLambdaPool::<Expr>::parse(s.as_str())?;
        let y = x.into_owned();
        drop(s);
        assert_eq!(
            y.as_borrowed(),
            RootedLambdaPool::parse("lambda <a,t> P P")?
        );

        let scenario = Scenario::new(vec![], vec![], BTreeMap::default());
        let s = "True & False".to_string();
        let x = RootedLambdaPool::<Expr>::parse(s.as_str())?;
        let v = x.interp(&scenario)?;
        let y = v.into_owned();
        drop(x);
        drop(s);
        assert_eq!(y.as_borrowed(), Value::Base(Literal::Bool(false)));

        Ok(())
    }
}
