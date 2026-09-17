use std::{collections::BTreeMap, fmt::Display};

use crate::{
    Actor, Entity, Event, Scenario,
    lambda::{
        Bvar,
        EvaluationError::{Stuck, UndefinedExpression, Unfinished},
        ExprType, FreeVar, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool,
        RootedLambdaPool,
        types::LambdaType,
    },
    language::{
        ActorOrEvent::{self},
        BinOp, Constant,
        Expr::{self},
        MonOp, Quantifier,
    },
};
use chumsky::container::Seq;
use itertools::Itertools;
use serde::Serialize;
use thiserror::Error;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct ValueId(u32);

impl From<ValueId> for usize {
    fn from(value: ValueId) -> Self {
        value.0 as usize
    }
}

///A representation of literals of a few basic types.
#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Serialize)]
pub enum Literal<'a> {
    ///Booleans, type: t
    Bool(bool),
    ///[`Actor`], type: a
    Actor(Actor<'a>),
    ///[`Event`], type: e
    Event(Event),
    ///A set of actors (represented as a vector), type: <a,t>
    ActorSet(Vec<Actor<'a>>),
    ///A set of events (represented as a vector), type: <e,t>
    EventSet(Vec<Event>),
    ///A mapping from truth to truth, type: <t,t>
    TruthTable {
        ///If the argument is false, what to do we do.
        on_false: bool,
        ///If the argument is true, what to do we do.
        on_true: bool,
    },
}

impl Display for Literal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Bool(true) => f.write_str("True"),
            Literal::Bool(false) => f.write_str("False"),
            Literal::Actor(a) => write!(f, "a_{a}"),
            Literal::Event(e) => write!(f, "e_{e}"),
            Literal::ActorSet(items) => {
                write!(
                    f,
                    "{{{}}}",
                    items.iter().map(|x| format!("a_{x}")).join(", ")
                )
            }
            Literal::EventSet(items) => {
                write!(
                    f,
                    "{{{}}}",
                    items.iter().map(|x| format!("e_{x}")).join(", ")
                )
            }
            Literal::TruthTable { on_true, on_false } => {
                write!(f, "False → {on_false}, True → {on_true}")
            }
        }
    }
}

impl<'src> Literal<'src> {
    ///Converts the literal into an [`Vec<Actor>`]. Returns `None` if not a set of [`Actor`].
    #[must_use]
    pub fn into_actor_set(self) -> Option<Vec<Actor<'src>>> {
        let Literal::ActorSet(x) = self else {
            return None;
        };
        Some(x)
    }

    ///If `self` is a constant function that always returns the same value, return that value.
    #[must_use]
    pub fn constant_app(&self) -> Option<Literal<'src>> {
        match self {
            Literal::ActorSet(items) if items.is_empty() => Some(Literal::Bool(false)),
            Literal::EventSet(items) if items.is_empty() => Some(Literal::Bool(false)),
            Literal::TruthTable { on_false, on_true } if on_false == on_true => {
                Some(Literal::Bool(*on_true))
            }
            _ => None,
        }
    }

    ///Converts the literal into an [`Vec<Event>`]. Returns `None` if not a set of [`Event`].
    #[must_use]
    pub fn into_event_set(self) -> Option<Vec<Event>> {
        let Literal::EventSet(x) = self else {
            return None;
        };
        Some(x)
    }

    ///Whether a type can be expressed as a [`Literal`].
    #[must_use]
    #[expect(clippy::missing_panics_doc)]
    pub fn has_literal(typ: &LambdaType) -> bool {
        // this is fine since we check its a function before unwrapping.
        !typ.is_function() || (typ.is_one_place_function() && typ.rhs().unwrap() == &LambdaType::T)
    }

    ///Get the type of the literal.
    #[must_use]
    pub fn typ(&self) -> &LambdaType {
        match self {
            Literal::Bool(_) => &LambdaType::T,
            Literal::Actor(_) => &LambdaType::A,
            Literal::Event(_) => &LambdaType::E,
            Literal::ActorSet(_) => LambdaType::at(),
            Literal::EventSet(_) => LambdaType::et(),
            Literal::TruthTable { .. } => LambdaType::tt(),
        }
    }

    ///Applies an argument to a function literal.
    ///
    ///# Panics
    ///Will panic if the types are not correct.
    #[must_use]
    pub fn apply(&self, other: &Literal<'src>) -> Literal<'src> {
        match (self, other) {
            (Literal::ActorSet(items), Literal::Actor(a)) => Literal::Bool(items.contains(a)),
            (Literal::EventSet(items), Literal::Event(e)) => Literal::Bool(items.contains(e)),
            (Literal::TruthTable { on_true, on_false }, Literal::Bool(b)) => {
                Literal::Bool(if *b { *on_true } else { *on_false })
            }
            _ => panic!("Type error that shouldn't occur!"),
        }
    }

    ///Converts the literal into a `bool`. Returns `None` if not a `bool`.
    #[must_use]
    pub fn as_bool(&self) -> Option<bool> {
        if let Literal::Bool(b) = self {
            Some(*b)
        } else {
            None
        }
    }

    ///Converts the literal into an [`Entity`]. Returns `None` if not an [`Entity`].
    #[must_use]
    pub fn as_entity(&self) -> Option<Entity<'src>> {
        match self {
            Literal::Actor(a) => Some(Entity::Actor(a)),
            Literal::Event(e) => Some(Entity::Event(*e)),
            _ => None,
        }
    }

    ///Converts the literal into an [`Actor`]. Returns `None` if not an [`Actor`].
    #[must_use]
    pub fn as_actor(&self) -> Option<Actor<'src>> {
        match self {
            Literal::Actor(a) => Some(a),
            _ => None,
        }
    }

    ///Converts the literal into an [`Event`]. Returns `None` if not an [`Event`].
    fn as_event(&self) -> Option<Event> {
        match self {
            Literal::Event(e) => Some(*e),
            _ => None,
        }
    }
}

#[derive(Debug, Error, Clone, Copy, PartialEq, Eq)]
///An error resulting from evaluating an expression that returns undefined, or if an evaluation
///can't be further reduced.
pub enum EvaluationError {
    ///An expression which is necessarily undefined (e.g. 1/0)
    #[error("This expression cannot be evaluated because it returns an undefined value")]
    UndefinedExpression,

    ///An expression which is stuck and cannot be reduced further (e.g. 1/x).
    #[error("This expression cannot be evaluated further because there is something undefined")]
    Stuck,

    ///A primitive which cannot be reduced yet.
    #[error("This expression cannot be evaluated further because it needs more applicands")]
    Unfinished,
}

///A value resulting from evaluating an expression.
#[derive(Debug, Clone)]
pub enum Value<'src, 'pool, T: LambdaLanguageOfThought + Clone> {
    ///A [`Literal`]
    Base(Literal<'src>),
    ///A lambda function
    Function(Box<Value<'src, 'pool, T>>, &'pool LambdaType, usize),
    ///A [`Neutral`] value, e.g. a value which cannot be evaluated without more information.
    Neutral(Neutral<'src, 'pool, T>),

    /// A primitive expression paired with its arguments.
    Primitive {
        ///The primitive expression
        expr: T,
        ///Its accumulated arguments.
        args: Vec<Value<'src, 'pool, T>>,
    },
}

///A value which cannot be evaluated yet.
#[derive(Debug, Clone)]
pub enum Neutral<'src, 'pool, T: LambdaLanguageOfThought + Clone> {
    ///A free variable.
    FreeVar(FreeVar<'src>, &'pool LambdaType),
    ///A bound variable
    BoundVar(Bvar, &'pool LambdaType),
    ///An application where both children are [`Neutral`].
    AppBoth(Box<Neutral<'src, 'pool, T>>, Box<Neutral<'src, 'pool, T>>),
    ///An application where only the head is neutral.
    AppHead(Box<Neutral<'src, 'pool, T>>, Box<Value<'src, 'pool, T>>),
    //An application where only the argument is neutral.
    AppArg(Box<Value<'src, 'pool, T>>, Box<Neutral<'src, 'pool, T>>),

    ///A primitive with some neutral argument.
    Primitive {
        expr: T,
        args: Vec<Value<'src, 'pool, T>>,
    },
}

impl<T> PartialEq for Neutral<'_, '_, T>
where
    T: LambdaLanguageOfThought + Clone + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::FreeVar(x, x_t), Self::FreeVar(y, y_t)) => x == y && x_t == y_t,
            (Self::AppBoth(x1, x2), Self::AppBoth(y1, y2)) => x1 == y1 && x2 == y2,
            (Self::AppHead(x1, x2), Self::AppHead(y1, y2)) => x1 == y1 && x2 == y2,
            (Self::AppArg(x1, x2), Self::AppArg(y1, y2)) => x1 == y1 && x2 == y2,
            (Self::BoundVar(x1, x2), Self::BoundVar(y1, y2)) => x1 == y1 && x2 == y2,
            (
                Self::Primitive {
                    expr: l_expr,
                    args: l_args,
                },
                Self::Primitive {
                    expr: r_expr,
                    args: r_args,
                },
            ) => l_expr == r_expr && l_args == r_args,
            _ => false,
        }
    }
}

impl<T> Eq for Neutral<'_, '_, T> where T: LambdaLanguageOfThought + Clone + Eq {}

impl<T> PartialEq for Value<'_, '_, T>
where
    T: LambdaLanguageOfThought + Clone + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Base(x), Self::Base(y)) => x == y,
            (Self::Function(x, x_t, x_d), Self::Function(y, y_t, y_d)) => {
                x_t == y_t && x == y && x_d == y_d
            }
            (Self::Neutral(x), Self::Neutral(y)) => x == y,
            (
                Self::Primitive {
                    expr: l_expr,
                    args: l_args,
                },
                Self::Primitive {
                    expr: r_expr,
                    args: r_args,
                },
            ) => l_expr == r_expr && l_args == r_args,
            _ => false,
        }
    }
}

impl<T> Eq for Value<'_, '_, T> where T: LambdaLanguageOfThought + Clone + Eq {}

impl<T> Value<'_, '_, T>
where
    T: LambdaLanguageOfThought + Clone,
{
    ///The type of this [`Value`]
    ///
    ///# Panics
    ///May panic if there is inconsistent type definitions.
    pub fn typ(&self) -> LambdaType {
        match self {
            Value::Base(literal) => literal.typ().clone(),
            Value::Function(body, arg_type, _) => {
                LambdaType::Composition(Box::new((*arg_type).clone()), Box::new(body.typ()))
            }
            Value::Neutral(n) => n.typ().clone(),
            Value::Primitive { expr, args } => {
                let mut t = expr.typ();
                for _ in 0..args.len() {
                    t = t
                        .rhs()
                        .expect("Expression has more arguments than is possible by types?");
                }
                t.clone()
            }
        }
    }
}
impl<T> Neutral<'_, '_, T>
where
    T: LambdaLanguageOfThought + Clone,
{
    pub fn typ(&self) -> LambdaType {
        match self {
            Neutral::FreeVar(_, t) | Neutral::BoundVar(_, t) => (*t).clone(),
            Neutral::AppBoth(x, _) | Neutral::AppHead(x, _) => x.typ().split().unwrap().1.clone(),
            Neutral::AppArg(x, _) => x.typ().split().unwrap().1.clone(),
            Neutral::Primitive { expr, args } => {
                let mut t = expr.typ();
                for _ in 0..args.len() {
                    t = t.rhs().unwrap();
                }
                t.clone()
            }
        }
    }
}

fn reduce_domain<'src>(
    func: Value<'src, '_, Expr<'src>>,
    arg_type: &LambdaType,
    scenario: &Scenario<'src>,
) -> Result<Literal<'src>, EvaluationError> {
    Ok(match arg_type {
        LambdaType::A => {
            let mut actor_set = vec![];
            for (a, func) in scenario
                .actors
                .iter()
                .copied()
                .zip(std::iter::repeat_n(func, scenario.actors.len()))
            {
                let v = Value::Base(Literal::Actor(a));
                let v = func.apply(v, scenario)?;
                match v {
                    Value::Base(Literal::Bool(b)) => {
                        if b {
                            actor_set.push(a);
                        }
                    }
                    Value::Neutral(_) => {
                        return Err(EvaluationError::Stuck);
                    }
                    _ => todo!("Don't know how to handle {v:?} result"),
                }
            }
            Literal::ActorSet(actor_set)
        }
        LambdaType::E => {
            let mut event_set = vec![];
            for (e, func) in
                std::iter::repeat_n(func, scenario.thematic_relations.len()).enumerate()
            {
                let e = u8::try_from(e).unwrap();
                let v = Value::Base(Literal::Event(e));
                let v = func.apply(v, scenario)?;
                match v {
                    Value::Base(Literal::Bool(b)) => {
                        if b {
                            event_set.push(e);
                        }
                    }
                    Value::Neutral(_) => {
                        return Err(EvaluationError::Stuck);
                    }
                    _ => todo!("Don't know how to handle {v:?} result"),
                }
            }
            Literal::EventSet(event_set)
        }
        LambdaType::T => {
            let on_false = match func
                .clone()
                .apply(Value::Base(Literal::Bool(false)), scenario)?
            {
                Value::Base(Literal::Bool(x)) => x,
                Value::Neutral(_) => {
                    return Err(EvaluationError::Stuck);
                }
                _ => todo!(),
            };

            let on_true = match func.apply(Value::Base(Literal::Bool(true)), scenario)? {
                Value::Base(Literal::Bool(x)) => x,
                Value::Neutral(_) => {
                    return Err(EvaluationError::Stuck);
                }
                _ => todo!(),
            };

            Literal::TruthTable { on_false, on_true }
        }
        LambdaType::Composition(..) => panic!("{arg_type} has no iterable domain"), //shouldn't happen anyhow because of above
    })
}

impl<'src> Value<'src, '_, Expr<'src>> {
    ///Convert the value into a [`Literal`], if possible.
    #[must_use]
    pub fn into_base_value(self) -> Option<Literal<'src>> {
        if let Value::Base(x) = self {
            Some(x)
        } else {
            None
        }
    }
    ///Convert the value into a [`Literal`], if possible.
    ///
    ///Returns None if the type cannot be turned into a literal.
    ///
    ///# Errors
    ///
    /// - returns [`EvaluationError::UndefinedExpression`] if there is an undefined expression (e.g. 1/0)
    /// - returns [`EvaluationError::Stuck`] if there is an undefined variable somewhere,
    ///
    ///# Panics
    ///
    ///May panic if the expression's type is incorrectly set.
    pub fn into_base_value_with_scenario(
        self,
        scenario: &Scenario<'src>,
    ) -> Result<Option<Literal<'src>>, EvaluationError> {
        match self {
            Value::Base(literal) => Ok(Some(literal)),
            Value::Function(body, arg_type, d) => {
                // we can only make <e,t> <a,t> or <t,t> into base values.
                if arg_type.is_function() || body.typ() != LambdaType::T {
                    return Ok(None);
                }

                let func = Value::Function(body, arg_type, d);
                reduce_domain(func, arg_type, scenario).map(Some)
            }
            Value::Primitive { expr, args } => {
                let mut t = expr.typ();
                for _ in 0..args.len() {
                    t = t
                        .rhs()
                        .expect("Expression has more applications than its type allows");
                }
                if t.is_one_place_function() && t.rhs().unwrap() == &LambdaType::T {
                    reduce_domain(Value::Primitive { expr, args }, t.lhs().unwrap(), scenario)
                        .map(Some)
                } else {
                    Ok(None)
                }
            }
            Value::Neutral(..) => Err(Stuck),
        }
    }

    fn is_neutral(&self) -> bool {
        matches!(&self, Value::Neutral(_))
    }
}

#[derive(Debug, Error)]
#[error("Not the desired type!")]
pub struct ValueConversionError;

impl<'src> TryFrom<Value<'src, '_, Expr<'src>>> for bool {
    type Error = ValueConversionError;
    fn try_from(value: Value<'src, '_, Expr<'src>>) -> Result<Self, Self::Error> {
        value
            .into_base_value()
            .and_then(|x| x.as_bool())
            .ok_or(ValueConversionError)
    }
}

impl<'src> Expr<'src> {
    fn n_arguments(&self) -> usize {
        match self {
            Expr::Constant(_) | Expr::Actor(_) | Expr::Event(_) => 0,
            Expr::Unary(_) => 1,
            Expr::Quantifier { .. } | Expr::Binary(_) => 2,
        }
    }

    fn eval<'pool>(
        &self,
        mut arguments: Vec<Value<'src, 'pool, Expr<'src>>>,
        scenario: &Scenario<'src>,
    ) -> Result<Value<'src, 'pool, Expr<'src>>, EvaluationError> {
        let x = match self {
            Expr::Quantifier {
                quantifier,
                var_type,
            } => {
                if arguments.len() < 2 {
                    return Err(EvaluationError::Unfinished);
                }
                let mut arguments = arguments
                    .into_iter()
                    .map(|x| x.into_base_value_with_scenario(scenario))
                    .collect::<Result<Option<Vec<_>>, _>>()?
                    .unwrap();
                let predicate = arguments.pop().unwrap();
                let restrictor = arguments.pop().unwrap();
                let v = match var_type {
                    ActorOrEvent::Actor => {
                        let predicate = predicate.into_actor_set().unwrap();
                        let restrictor = restrictor.into_actor_set().unwrap();
                        match quantifier {
                            Quantifier::Universal => {
                                restrictor.iter().all(|x| predicate.contains(x))
                            }
                            Quantifier::Existential => {
                                restrictor.iter().any(|x| predicate.contains(x))
                            }
                        }
                    }
                    ActorOrEvent::Event => {
                        let predicate = predicate.into_event_set().unwrap();
                        let restrictor = restrictor.into_event_set().unwrap();
                        match quantifier {
                            Quantifier::Universal => {
                                restrictor.iter().all(|x| predicate.contains(x))
                            }
                            Quantifier::Existential => {
                                restrictor.iter().any(|x| predicate.contains(x))
                            }
                        }
                    }
                };
                Literal::Bool(v)
            }
            Expr::Unary(MonOp::Iota(a_o_e)) => {
                let x = arguments
                    .pop()
                    .unwrap()
                    .into_base_value_with_scenario(scenario)?
                    .unwrap();
                match a_o_e {
                    ActorOrEvent::Actor => {
                        let mut x = x.into_actor_set().unwrap();
                        if x.len() != 1 {
                            return Err(EvaluationError::UndefinedExpression);
                        }
                        Literal::Actor(x.pop().unwrap())
                    }
                    ActorOrEvent::Event => {
                        let mut x = x.into_event_set().unwrap();
                        if x.len() != 1 {
                            return Err(EvaluationError::UndefinedExpression);
                        }
                        Literal::Event(x.pop().unwrap())
                    }
                }
            }
            Expr::Actor(a) => Literal::Actor(a),
            Expr::Event(e) => Literal::Event(*e),
            Expr::Binary(op @ (BinOp::AgentOf | BinOp::PatientOf), ..) => {
                let arguments = arguments
                    .into_iter()
                    .map(|x| x.into_base_value_with_scenario(scenario))
                    .collect::<Result<Option<Vec<_>>, _>>()?
                    .unwrap();
                if arguments.is_empty() {
                    return Err(EvaluationError::Unfinished);
                } else if arguments.len() == 1 {
                    let a = arguments[0].as_actor().unwrap();
                    let events = scenario
                        .thematic_relations
                        .iter()
                        .enumerate()
                        .filter_map(|(i, e)| match op {
                            BinOp::AgentOf => e.agent.and_then(|x| {
                                if x == a {
                                    Some(u8::try_from(i).unwrap())
                                } else {
                                    None
                                }
                            }),
                            BinOp::PatientOf => e.patient.and_then(|x| {
                                if x == a {
                                    Some(u8::try_from(i).unwrap())
                                } else {
                                    None
                                }
                            }),
                            _ => panic!("impossible bc of prior check!"),
                        })
                        .collect();
                    Literal::EventSet(events)
                } else {
                    let a = arguments[0].as_actor().unwrap();
                    let e = arguments[1].as_event().unwrap();
                    let e = scenario
                        .thematic_relations
                        .get(usize::from(e))
                        .ok_or(EvaluationError::UndefinedExpression)?;
                    Literal::Bool(match op {
                        BinOp::AgentOf => e.agent.is_some_and(|x| x == a),
                        BinOp::PatientOf => e.patient.is_some_and(|x| x == a),
                        _ => panic!("impossible bc of prior check!"),
                    })
                }
            }
            Expr::Binary(BinOp::And) => {
                if arguments.len() == 1 {
                    let first_arg = arguments
                        .pop()
                        .unwrap()
                        .into_base_value_with_scenario(scenario)?
                        .unwrap()
                        .as_bool()
                        .unwrap();
                    Literal::TruthTable {
                        on_false: false,
                        on_true: first_arg,
                    }
                } else {
                    'shortcircuit: {
                        for x in arguments {
                            let value = x
                                .into_base_value_with_scenario(scenario)?
                                .unwrap()
                                .as_bool()
                                .expect("Type inference error!");

                            if !value {
                                break 'shortcircuit Literal::Bool(false);
                            }
                        }

                        Literal::Bool(true)
                    }
                }
            }

            Expr::Binary(BinOp::Or) => {
                if arguments.len() == 1 {
                    let first_arg = arguments
                        .pop()
                        .unwrap()
                        .into_base_value_with_scenario(scenario)?
                        .unwrap()
                        .as_bool()
                        .unwrap();
                    Literal::TruthTable {
                        on_false: first_arg,
                        on_true: true,
                    }
                } else {
                    'shortcircuit: {
                        for x in arguments {
                            let value = x
                                .into_base_value_with_scenario(scenario)?
                                .unwrap()
                                .as_bool()
                                .expect("Type inference error!");

                            if value {
                                break 'shortcircuit Literal::Bool(true);
                            }
                        }

                        Literal::Bool(false)
                    }
                }
            }

            Expr::Unary(MonOp::Not) => {
                if arguments.is_empty() {
                    return Err(Unfinished);
                }
                Literal::Bool(
                    !arguments
                        .pop()
                        .unwrap()
                        .into_base_value_with_scenario(scenario)?
                        .unwrap()
                        .as_bool()
                        .unwrap(),
                )
            }
            Expr::Constant(Constant::Everyone) => Literal::ActorSet(scenario.actors.clone()),
            Expr::Constant(Constant::EveryEvent) => Literal::EventSet(scenario.events().collect()),
            Expr::Constant(Constant::Tautology) => Literal::Bool(true),
            Expr::Constant(Constant::Contradiction) => Literal::Bool(false),
            Expr::Constant(Constant::Property(p, a_or_e)) => {
                let x = scenario
                    .properties
                    .get(p)
                    .ok_or(EvaluationError::UndefinedExpression)?;
                match a_or_e {
                    ActorOrEvent::Actor => Literal::ActorSet(
                        x.iter()
                            .filter_map(|x| {
                                if let Entity::Actor(x) = x {
                                    Some(*x)
                                } else {
                                    None
                                }
                            })
                            .collect(),
                    ),
                    ActorOrEvent::Event => Literal::EventSet(
                        x.iter()
                            .filter_map(|x| {
                                if let Entity::Event(x) = x {
                                    Some(*x)
                                } else {
                                    None
                                }
                            })
                            .collect(),
                    ),
                }
            }
        };
        Ok(Value::Base(x))
    }
}

impl<'src, 'pool> Value<'src, 'pool, Expr<'src>> {
    ///Applies a value to another.
    ///
    ///# Errors
    ///May return a [`EvaluationError::UndefinedExpression`] if there is an undefined value in the
    ///expression, e.g. (1/0).
    pub fn apply(
        self,
        other: Self,
        scenario: &Scenario<'src>,
    ) -> Result<Value<'src, 'pool, Expr<'src>>, EvaluationError> {
        match self {
            Value::Base(f) if let Some(x) = f.constant_app() => Ok(Value::Base(x)),
            Value::Base(f) => match other {
                Value::Base(a) => Ok(Value::Base(f.apply(&a))),
                Value::Neutral(x) => Ok(Value::Neutral(Neutral::AppArg(
                    Box::new(Value::Base(f)),
                    Box::new(x),
                ))),
                _ => todo!(),
            },
            Value::Function(head, _, d) => {
                if let Value::Neutral(arg) = other {
                    Ok(Value::Neutral(Neutral::AppArg(head, Box::new(arg))))
                } else {
                    head.eval(BTreeMap::from([(d, other)]), scenario)
                }
            }
            Value::Neutral(Neutral::Primitive { expr, mut args }) => {
                args.push(other);
                Ok(Value::Neutral(Neutral::Primitive { expr, args }))
            }
            Value::Neutral(head) => Ok(Value::Neutral(match other {
                Value::Neutral(arg) => Neutral::AppBoth(Box::new(head), Box::new(arg)),
                arg @ (Value::Primitive { .. } | Value::Base(_) | Value::Function(..)) => {
                    Neutral::AppHead(Box::new(head), Box::new(arg))
                }
            })),
            Value::Primitive { expr, mut args } => {
                args.push(other);
                eval_expr(expr, args, scenario)
            }
        }
    }
}

impl<'src, 'pool> Value<'src, 'pool, Expr<'src>> {
    fn reduce(
        self,
        scenario: &Scenario<'src>,
    ) -> Result<Value<'src, 'pool, Expr<'src>>, EvaluationError> {
        match self {
            Value::Base(literal) => Ok(Value::Base(literal)),
            Value::Function(value, arg_type, d) => {
                let b = value.typ();
                if !arg_type.is_function() && b == LambdaType::T {
                    let f = Value::Function(value, arg_type, d);
                    if let Ok(Some(x)) = f.clone().into_base_value_with_scenario(scenario) {
                        Ok(Value::Base(x))
                    } else {
                        Ok(f)
                    }
                } else {
                    Ok(Value::Function(
                        Box::new(value.reduce(scenario)?),
                        arg_type,
                        d,
                    ))
                }
            }
            Value::Neutral(neutral) => neutral.reduce(scenario),
            Value::Primitive { expr, args } => {
                let args: Vec<_> = args
                    .into_iter()
                    .map(|x| x.reduce(scenario))
                    .collect::<Result<_, _>>()?;

                eval_expr(expr, args, scenario)
            }
        }
    }
}

impl<'src, 'pool> Neutral<'src, 'pool, Expr<'src>> {
    fn reduce(
        self,
        scenario: &Scenario<'src>,
    ) -> Result<Value<'src, 'pool, Expr<'src>>, EvaluationError> {
        match self {
            Neutral::Primitive { expr, args } => {
                let args: Vec<_> = args
                    .into_iter()
                    .map(|x| x.reduce(scenario))
                    .collect::<Result<_, _>>()?;
                eval_expr(expr, args, scenario)
            }
            v @ (Neutral::FreeVar(..) | Neutral::BoundVar(..)) => Ok(Value::Neutral(v)),
            Neutral::AppBoth(head, arg) => {
                let head = head.reduce(scenario)?;
                let arg = arg.reduce(scenario)?;
                head.apply(arg, scenario)
            }
            Neutral::AppHead(head, arg) => {
                let head = head.reduce(scenario)?;
                let arg = arg.reduce(scenario)?;
                head.apply(arg, scenario)
            }
            Neutral::AppArg(head, arg) => {
                let head = head.reduce(scenario)?;
                let arg = arg.reduce(scenario)?;
                head.apply(arg, scenario)
            }
        }
    }
}

impl<'src> RootedLambdaPool<'src, Expr<'src>> {
    ///Interprets an expression given a particular scenario.
    ///The resulting [`Value`] may be a [`Literal`] but may also still be an unreduced function
    ///(e.g. if you have a closure or the like)
    ///
    ///# Errors
    ///May return a [`EvaluationError::UndefinedExpression`] if there is an undefined value in the
    ///expression, e.g. (1/0).
    pub fn interp<'pool>(
        &'pool self,
        scenario: &Scenario<'src>,
    ) -> Result<Value<'src, 'pool, Expr<'src>>, EvaluationError> {
        let x = self
            .pool
            .eval(self.root, vec![], scenario, None)
            .map(|(x, _)| x)?;

        x.reduce(scenario)
    }
}

impl<'src, 'pool> Neutral<'src, 'pool, Expr<'src>> {
    fn eval(
        self,
        mut variables: BTreeMap<usize, Value<'src, 'pool, Expr<'src>>>,
        scenario: &Scenario<'src>,
    ) -> Result<Value<'src, 'pool, Expr<'src>>, EvaluationError> {
        match self {
            Neutral::FreeVar(..) => todo!(),
            Neutral::BoundVar(b, lambda_type) => {
                if let Some(x) = variables.remove(&b) {
                    Ok(x)
                } else {
                    Ok(Value::Neutral(Neutral::BoundVar(b, lambda_type)))
                }
            }
            Neutral::AppBoth(head, arg) => {
                let head = head.eval(variables.clone(), scenario)?;
                let arg = arg.eval(variables, scenario)?;
                head.apply(arg, scenario)
            }
            Neutral::AppHead(head, arg) => {
                let head = head.eval(variables, scenario)?;
                head.apply(*arg, scenario)
            }
            Neutral::AppArg(head, arg) => {
                let arg = arg.eval(variables, scenario)?;
                head.apply(arg, scenario)
            }
            Neutral::Primitive { expr, args } => {
                let args: Vec<_> = args
                    .into_iter()
                    .map(|x| x.eval(variables.clone(), scenario))
                    .collect::<Result<_, _>>()?;
                eval_expr(expr, args, scenario)
            }
        }
    }
}

impl<'src, 'pool> Value<'src, 'pool, Expr<'src>> {
    fn eval(
        self,
        mut variables: BTreeMap<usize, Value<'src, 'pool, Expr<'src>>>,
        scenario: &Scenario<'src>,
    ) -> Result<Value<'src, 'pool, Expr<'src>>, EvaluationError> {
        match self {
            Value::Function(body, arg_type, d) => {
                variables.insert(d, Value::Neutral(Neutral::BoundVar(d, arg_type)));
                let body = body.eval(variables, scenario)?;
                Ok(Value::Function(Box::new(body), arg_type, d))
            }
            Value::Primitive { expr, args } => {
                let arguments = args
                    .into_iter()
                    .map(|x| Value::eval(x, variables.clone(), scenario))
                    .collect::<Result<Vec<_>, _>>()?;

                if arguments.iter().all(|x| !x.is_neutral()) {
                    expr.eval(arguments, scenario)
                } else {
                    Ok(Value::Primitive {
                        expr,
                        args: arguments,
                    })
                }
            }
            Value::Base(literal) => Ok(Value::Base(literal)),
            Value::Neutral(x) => x.eval(variables, scenario),
        }
    }

    fn contains_var(&self, var: usize) -> bool {
        match self {
            Value::Base(_) => false,
            Value::Function(v, _, _) => v.contains_var(var),
            Value::Neutral(v) => v.contains_var(var),
            Value::Primitive { args, .. } => args.iter().any(|x| x.contains_var(var)),
        }
    }

    ///Shifts any variables/functions with d>var down by one to account for var not existing.
    fn remove_var(&mut self, var: usize) {
        match self {
            Value::Base(_) => {}
            Value::Function(v, _, d) => {
                debug_assert_ne!(
                    var, *d,
                    "If we're shifting variables, the removed variable can't be attested"
                );
                if *d > var {
                    *d -= 1;
                }
                v.remove_var(var);
            }
            Value::Neutral(v) => v.remove_var(var),
            Value::Primitive { args, .. } => args.iter_mut().for_each(|x| x.remove_var(var)),
        }
    }

    fn primitive_application_head(&self) -> Option<&Expr<'src>> {
        match self {
            Value::Base(..) | Value::Function(..) => None,
            Value::Neutral(x) => x.primitive_application_head(),
            Value::Primitive { expr, .. } => Some(expr),
        }
    }
}

impl<'src> Neutral<'src, '_, Expr<'src>> {
    fn primitive_application_head(&self) -> Option<&Expr<'src>> {
        match self {
            Neutral::AppBoth(head, ..) | Neutral::AppHead(head, ..) => {
                head.primitive_application_head()
            }
            Neutral::AppArg(head, ..) => head.primitive_application_head(),
            Neutral::Primitive { expr, .. } => Some(expr),
            Neutral::FreeVar(..) | Neutral::BoundVar(..) => None,
        }
    }

    fn contains_var(&self, var: usize) -> bool {
        match self {
            Neutral::FreeVar(..) => false,
            Neutral::BoundVar(v, _) => *v == var,
            Neutral::AppBoth(a, b) => a.contains_var(var) || b.contains_var(var),
            Neutral::AppHead(a, b) => a.contains_var(var) || b.contains_var(var),
            Neutral::AppArg(a, b) => a.contains_var(var) || b.contains_var(var),
            Neutral::Primitive { args, .. } => args.iter().any(|x| x.contains_var(var)),
        }
    }

    fn remove_var(&mut self, var: usize) {
        match self {
            Neutral::FreeVar(..) => (),
            Neutral::BoundVar(d, _) => {
                debug_assert_ne!(
                    var, *d,
                    "If we're shifting variables, the removed variable can't be attested"
                );
                if *d > var {
                    *d -= 1;
                }
            }
            Neutral::AppBoth(head, arg) => {
                head.remove_var(var);
                arg.remove_var(var);
            }
            Neutral::AppHead(head, arg) => {
                head.remove_var(var);
                arg.remove_var(var);
            }
            Neutral::AppArg(head, arg) => {
                head.remove_var(var);
                arg.remove_var(var);
            }
            Neutral::Primitive { args, .. } => args.iter_mut().for_each(|x| x.remove_var(var)),
        }
    }
}

impl<'src> LambdaPool<'src, Expr<'src>> {
    fn eval<'pool>(
        &'pool self,
        index: LambdaExprRef,
        mut variables: Vec<Value<'src, 'pool, Expr<'src>>>,
        scenario: &Scenario<'src>,
        under_lambda: Option<usize>,
    ) -> Result<(Value<'src, 'pool, Expr<'src>>, bool), EvaluationError> {
        println!("{index:?}\t{:?}", self.get(index));
        let x = match self.get(index) {
            LambdaExpr::Lambda(body, arg_type) => {
                let d = variables.len();
                variables.push(Value::Neutral(Neutral::BoundVar(d, arg_type)));
                let (body, eta_reduced) = self.eval(*body, variables, scenario, Some(d))?;
                if eta_reduced {
                    Ok((body, false))
                } else {
                    Ok((Value::Function(Box::new(body), arg_type, d), false))
                }
            }
            LambdaExpr::BoundVariable(x, _) => {
                Ok((variables[variables.len() - 1 - *x].clone(), false))
            }
            LambdaExpr::FreeVariable(..) => {
                todo!("No support for free variables yet.")
            }
            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                let (argument, _) = self.eval(*argument, variables.clone(), scenario, None)?;
                let (mut subformula, _) =
                    self.eval(*subformula, variables.clone(), scenario, None)?;

                //eta-reduction
                if let Some(d) = under_lambda
                    && matches!(argument, Value::Neutral(Neutral::BoundVar(x, _)) if x == d)
                    && subformula
                        .primitive_application_head()
                        .is_none_or(|x| !x.infix())
                    && !subformula.contains_var(d)
                {
                    subformula.remove_var(d);
                    Ok((subformula, true))
                } else {
                    subformula.apply(argument, scenario).map(|x| (x, false))
                }
            }
            LambdaExpr::LanguageOfThoughtExpr(x, ExprType::NoVar) => {
                if x.n_arguments() == 0 {
                    x.eval(vec![], scenario).map(|x| (x, false))
                } else {
                    Ok((
                        Value::Primitive {
                            expr: *x,
                            args: vec![],
                        },
                        false,
                    ))
                }
            }

            LambdaExpr::LanguageOfThoughtExpr(expr, ExprType::BindVarTwoBodies(x, y)) => {
                let d = variables.len();
                let arg_type = expr
                    .var_type()
                    .expect("Expression is syncategorematic without haveing var_type");

                variables.push(Value::Neutral(Neutral::BoundVar(d, arg_type)));
                let (x_body, eta_reduced) = self.eval(*x, variables.clone(), scenario, Some(d))?;

                let x = if eta_reduced {
                    x_body
                } else {
                    Value::Function(Box::new(x_body), arg_type, d)
                };
                let (y_body, eta_reduced) = self.eval(*y, variables.clone(), scenario, Some(d))?;

                let y = if eta_reduced {
                    y_body
                } else {
                    Value::Function(Box::new(y_body), arg_type, d)
                };

                let arguments = vec![x, y];
                eval_expr(*expr, arguments, scenario).map(|x| (x, false))
            }
            LambdaExpr::LanguageOfThoughtExpr(expr, ExprType::BindVar(x)) => {
                let d = variables.len();
                let arg_type = expr
                    .var_type()
                    .expect("Expression is syncategorematic without haveing var_type");

                variables.push(Value::Neutral(Neutral::BoundVar(d, arg_type)));
                let (x_body, eta_reduced) = self.eval(*x, variables.clone(), scenario, Some(d))?;
                let x = if eta_reduced {
                    x_body
                } else {
                    Value::Function(Box::new(x_body), arg_type, d)
                };

                let arguments = vec![x];
                eval_expr(*expr, arguments, scenario).map(|x| (x, false))
            }
        };
        println!("{x:?}");
        x
    }
}

fn eval_expr<'src, 'pool>(
    expr: Expr<'src>,
    args: Vec<Value<'src, 'pool, Expr<'src>>>,
    scenario: &Scenario<'src>,
) -> Result<Value<'src, 'pool, Expr<'src>>, EvaluationError> {
    match expr.eval(args.clone(), scenario) {
        Ok(x) => Ok(x),
        Err(EvaluationError::Unfinished) => Ok(Value::Primitive { expr, args }),
        Err(Stuck) => Ok(Value::Neutral(Neutral::Primitive { expr, args })),
        Err(UndefinedExpression) => Err(UndefinedExpression),
    }
}
#[cfg(test)]
mod test {
    use crate::lambda::{enumerator::Generator, printing::VarContext};

    use super::*;

    #[test]
    fn basic_interp() -> anyhow::Result<()> {
        let scenario = Scenario::parse(
            "<john,mary,phil (kind);{A: john,P: mary (likes)},{A: mary},{P: phil}>",
        )?;

        let data = [
            (
                "lambda t phi lambda t psi lambda t phi1 phi & psi & phi1",
                "lambda t phi lambda t psi lambda t phi1 phi & psi & phi1",
            ),
            ("a_john", "a_john"),
            ("pa_kind(a_john)", "False"),
            ("True | True", "True"),
            ("True | False", "True"),
            ("False | True", "True"),
            ("False | False", "False"),
            ("True & True", "True"),
            ("True & False", "False"),
            ("False & True", "False"),
            ("False & False", "False"),
            ("~False", "True"),
            ("~True", "False"),
            ("~(False & False)", "True"),
            ("AgentOf(a_john, e_0) | False", "True"),
            ("some(all_a, pa_kind)", "True"),
            ("every(all_a, pa_kind)", "False"),
            ("some(lambda a x pa_kind(x) | ~pa_kind(x), pa_kind)", "True"),
            (
                "some_e(all_e, lambda e x some(pa_kind, lambda a y AgentOf(y, x)))",
                "False",
            ),
            (
                "some_e(all_e, lambda e x some(lambda a y ~pa_kind(y), lambda a y AgentOf(y, x)))",
                "True",
            ),
            (
                "lambda a x lambda a y pa_kind(x)",
                "lambda a x lambda a y {a_phil}(x)",
            ),
            ("some(x, all_a(x), pa_kind(x))", "True"),
            ("every(x, all_a(x), pa_kind(x))", "False"),
            ("pa_kind", "{a_phil}"),
            ("lambda a x pa_kind(x)", "{a_phil}"),
            (
                "lambda a x lambda a y pa_kind(x)",
                "lambda a x lambda a y {a_phil}(x)",
            ),
        ];

        let n_width = data
            .iter()
            .map(|(x, y)| x.chars().count() + y.chars().count() + 5)
            .max()
            .unwrap();

        for (phi_s, val) in data {
            print!("[{phi_s}] = {val}");
            let n_dots = n_width - phi_s.chars().count() - val.chars().count();
            print!("{}", ".".repeat(n_dots));
            let phi = RootedLambdaPool::parse(phi_s)?;
            let mut alt_phi = phi.clone();
            alt_phi.reduce()?;
            println!("alt_phi={alt_phi}");
            println!("{:#?}", phi.tokens(phi.root, VarContext::default()));
            assert_eq!(
                phi.to_string(),
                phi_s,
                "Printed, parsed value {phi} != string {phi_s}"
            );
            let calculated_value = phi.interp(&scenario)?;
            if calculated_value.to_string() != val {
                println!("❌");
                assert_eq!(
                    calculated_value.to_string(),
                    val,
                    "{calculated_value} != {val} \n ({calculated_value:#?}"
                );
            }

            println!("✅");
        }

        Ok(())
    }
    #[test]
    fn simple_reduction() -> anyhow::Result<()> {
        let scenario = Scenario::parse(
            "<john,mary,phil (kind);{A: john,P: mary (likes)},{A: mary},{P: phil}>",
        )?;

        let expr = RootedLambdaPool::parse("AgentOf(a_john)")?;

        let e = expr.interp(&scenario)?;

        assert_eq!(e, Value::Base(Literal::EventSet(vec![0])));

        Ok(())
    }

    #[test]
    fn fancy_interp() -> anyhow::Result<()> {
        let scenario = Scenario::parse(
            "<john,mary,phil (kind);{A: john,P: mary (likes)},{A: mary},{P: phil}>",
        )?;

        let mut expressions = scenario.scenario_ops();
        expressions.extend(Expr::basic_ops());
        let mut generator: Generator<Expr> = Generator::new(expressions);

        for ty in LambdaType::all().take(12) {
            generator.enumerate_or_generate(ty.clone(), 4);
            let pools = generator.enumerate(&ty, 4).unwrap();

            let pools = pools
                .iter()
                .map(|x| generator.to_rooted_lambda_pool(*x).unwrap())
                .collect::<Vec<_>>();

            for phi in pools {
                print!("[{phi}]");
                let calculated_value = phi.interp(&scenario).map(|x| x.to_string());
                println!("\t{calculated_value:?}");
            }
        }

        Ok(())
    }
}
