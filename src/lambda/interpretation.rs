use std::{borrow::Cow, fmt::Display, iter::repeat_n};

use crate::{
    Actor, Entity, Event, Scenario,
    lambda::{
        Bvar, ExprType, FreeVar, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool,
        RootedLambdaPool, equal_expr, types::LambdaType,
    },
    language::{
        ActorOrEvent::{self},
        BinOp, Constant,
        Expr::{self},
        MonOp, Quantifier,
    },
    scenario,
};
use chumsky::container::Seq;
use itertools::{Either, Itertools};
use thiserror::Error;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct ValueId(u32);

impl From<ValueId> for usize {
    fn from(value: ValueId) -> Self {
        value.0 as usize
    }
}

///A representation of literals of a few basic types.
#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
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
    TruthTable { on_false: bool, on_true: bool },
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
    pub fn has_literal(typ: &LambdaType) -> bool {
        !typ.is_function() || typ.is_one_place_function()
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

    fn apply(&self, other: &Literal<'src>) -> Literal<'src> {
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
#[error("This expression cannot be evaluated because it returns an undefined value")]
///An error resulting from evaluating an expression that returns undefined.
pub struct UndefinedExpression;

///A value resulting from evaluating an expression.
#[derive(Debug, Clone)]
pub enum Value<'src, 'pool, T: LambdaLanguageOfThought + Clone> {
    ///A [`Literal`]
    Base(Literal<'src>),
    Closure {
        pool: &'pool LambdaPool<'src, T>,
        arg_type: &'pool LambdaType,
        f: LambdaExprRef,
        env: Vec<Value<'src, 'pool, T>>,
    },
    Neutral(Neutral<'src, 'pool, T>),
    Primitive {
        expr: T,
        args: Vec<Value<'src, 'pool, T>>,
    },
}

#[derive(Debug, Clone)]
pub enum Neutral<'src, 'pool, T: LambdaLanguageOfThought + Clone> {
    FreeVar(FreeVar<'src>),
    BoundVar(Bvar, &'pool LambdaType),
    App(Box<Neutral<'src, 'pool, T>>, Box<Value<'src, 'pool, T>>),
}

impl<T> PartialEq for Neutral<'_, '_, T>
where
    T: LambdaLanguageOfThought + Clone + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::FreeVar(x), Self::FreeVar(y)) => x == y,
            (Self::App(x1, x2), Self::App(y1, y2)) => x1 == y1 && x2 == y2,
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
            (
                Self::Closure {
                    pool: l_pool,
                    arg_type: l_type,
                    f: l_f,
                    env: l_env,
                },
                Self::Closure {
                    pool: r_pool,
                    arg_type: r_type,
                    f: r_f,
                    env: r_env,
                },
            ) => l_type == r_type && equal_expr(l_pool, *l_f, r_pool, *r_f) && l_env == r_env,
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

impl<'src, T> Value<'src, '_, T>
where
    T: LambdaLanguageOfThought + Clone,
{
    pub fn typ(&self) -> LambdaType {
        match self {
            Value::Base(literal) => literal.typ().clone(),
            Value::Closure {
                pool, f, arg_type, ..
            } => LambdaType::Composition(
                Box::new((*arg_type).clone()),
                Box::new(pool.get_type(*f).unwrap()),
            ),
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
impl<'src, T> Neutral<'src, '_, T>
where
    T: LambdaLanguageOfThought + Clone,
{
    pub fn typ(&self) -> &LambdaType {
        match self {
            Neutral::FreeVar(free_var) => todo!(),
            Neutral::BoundVar(_, t) => *t,
            Neutral::App(x, y) => x.typ().split().unwrap().1,
        }
    }
}

impl<'src> Value<'src, '_, Expr<'src>> {
    fn to_base_value(&self) -> Option<&Literal<'src>> {
        if let Value::Base(b) = self {
            Some(b)
        } else {
            None
        }
    }

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
    pub fn into_base_value_with_scenario(
        self,
        scenario: &Scenario<'src>,
    ) -> Result<Option<Literal<'src>>, UndefinedExpression> {
        Ok(match self {
            Value::Base(literal) => Some(literal),
            func @ Value::Closure {
                pool, f, arg_type, ..
            } => {
                // we can only make <e,t> <a,t> or <t,t> into base values.
                if arg_type.is_function() || pool.get_type(f).unwrap() != LambdaType::T {
                    return Ok(None);
                }

                match arg_type {
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
                            if let Value::Base(Literal::Bool(b)) = v {
                                if b {
                                    actor_set.push(a);
                                }
                            } else {
                                return Ok(None);
                            };
                        }
                        Some(Literal::ActorSet(actor_set))
                    }
                    LambdaType::E => {
                        let mut event_set = vec![];
                        for (e, func) in
                            std::iter::repeat_n(func, scenario.thematic_relations.len()).enumerate()
                        {
                            let e = u8::try_from(e).unwrap();
                            let v = Value::Base(Literal::Event(e));
                            let v = func.apply(v, scenario)?;
                            if let Value::Base(Literal::Bool(b)) = v {
                                if b {
                                    event_set.push(e);
                                }
                            } else {
                                return Ok(None);
                            };
                        }
                        Some(Literal::EventSet(event_set))
                    }
                    LambdaType::T => {
                        let Value::Base(Literal::Bool(on_false)) = func
                            .clone()
                            .apply(Value::Base(Literal::Bool(false)), scenario)?
                        else {
                            return Ok(None);
                        };
                        let Value::Base(Literal::Bool(on_true)) =
                            func.apply(Value::Base(Literal::Bool(true)), scenario)?
                        else {
                            return Ok(None);
                        };

                        Some(Literal::TruthTable { on_false, on_true })
                    }
                    LambdaType::Composition(..) => None, //shouldn't happen anyhow because of above
                                                         //check
                }
            }
            Value::Neutral(neutral) => todo!(),
            Value::Primitive { expr, args } => todo!(),
        })
    }

    #[expect(dead_code)]
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
        arguments: Vec<Value<'src, 'pool, Expr<'src>>>,
        scenario: &Scenario<'src>,
    ) -> Result<Value<'src, 'pool, Expr<'src>>, UndefinedExpression> {
        let mut arguments: Vec<_> = arguments
            .into_iter()
            .map(|x| x.into_base_value_with_scenario(scenario))
            .collect::<Result<Option<_>, _>>()?
            .unwrap();
        let x = match self {
            Expr::Quantifier {
                quantifier,
                var_type,
            } => {
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
                let x = arguments.pop().unwrap();
                match a_o_e {
                    ActorOrEvent::Actor => {
                        let mut x = x.into_actor_set().unwrap();
                        if x.len() != 1 {
                            return Err(UndefinedExpression);
                        }
                        Literal::Actor(x.pop().unwrap())
                    }
                    ActorOrEvent::Event => {
                        let mut x = x.into_event_set().unwrap();
                        if x.len() != 1 {
                            return Err(UndefinedExpression);
                        }
                        Literal::Event(x.pop().unwrap())
                    }
                }
            }
            Expr::Actor(a) => Literal::Actor(a),
            Expr::Event(e) => Literal::Event(*e),
            Expr::Binary(op @ (BinOp::AgentOf | BinOp::PatientOf), ..) => {
                let a = arguments[0].as_actor().unwrap();
                let e = arguments[1].as_event().unwrap();
                let e = scenario
                    .thematic_relations
                    .get(usize::from(e))
                    .ok_or(UndefinedExpression)?;
                Literal::Bool(match op {
                    BinOp::AgentOf => e.agent.is_some_and(|x| x == a),
                    BinOp::PatientOf => e.patient.is_some_and(|x| x == a),
                    _ => panic!("impossible bc of prior check!"),
                })
            }
            Expr::Binary(BinOp::And) => Literal::Bool(
                arguments
                    .iter()
                    .all(|x| x.as_bool().expect("Type inference error!")),
            ),
            Expr::Binary(BinOp::Or) => Literal::Bool(
                arguments
                    .iter()
                    .any(|x| x.as_bool().expect("Type inference error!")),
            ),
            Expr::Unary(MonOp::Not) => Literal::Bool(!arguments.pop().unwrap().as_bool().unwrap()),
            Expr::Constant(Constant::Everyone) => Literal::ActorSet(scenario.actors.clone()),
            Expr::Constant(Constant::EveryEvent) => Literal::EventSet(scenario.events().collect()),
            Expr::Constant(Constant::Tautology) => Literal::Bool(true),
            Expr::Constant(Constant::Contradiction) => Literal::Bool(false),
            Expr::Constant(Constant::Property(p, a_or_e)) => {
                let x = scenario.properties.get(p).ok_or(UndefinedExpression)?;
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
    pub fn apply(
        self,
        other: Self,
        scenario: &Scenario<'src>,
    ) -> Result<Value<'src, 'pool, Expr<'src>>, UndefinedExpression> {
        match self {
            Value::Base(f) => match other {
                Value::Base(a) => Ok(Value::Base(f.apply(&a))),
                Value::Closure {
                    pool,
                    arg_type,
                    f,
                    env,
                } => todo!(),
                Value::Neutral(neutral) => todo!(),
                Value::Primitive { expr, args } => todo!(),
            },
            Value::Closure {
                pool, f, mut env, ..
            } => {
                env.push(other);
                pool.eval(f, env, scenario)
            }
            Value::Neutral(neutral) => todo!(),
            Value::Primitive { expr, mut args } => {
                args.push(other);
                if expr.n_arguments() == args.len() {
                    expr.eval(args, scenario)
                } else {
                    Ok(Value::Primitive { expr, args })
                }
            }
        }
    }

    fn reify_inner(
        self,
        scenario: &Scenario<'src>,
        level: usize,
    ) -> Result<Value<'src, 'pool, Expr<'src>>, UndefinedExpression> {
        match self {
            Value::Base(literal) => Ok(Value::Base(literal)),
            closure @ Value::Closure { arg_type, .. } => {
                let v = Value::Neutral(Neutral::BoundVar(level, arg_type));
                closure.apply(v, scenario)?.reify_inner(scenario, level + 1)
            }
            Value::Neutral(neutral) => todo!(),
            Value::Primitive { expr, args } => {
                if expr.n_arguments() == args.len() {
                    expr.eval(args, scenario)
                } else {
                    let mut t = expr.typ();
                    let mut final_typ = None;
                    let mut arg_types = vec![];
                    let mut remaining_types = vec![];
                    for i in 1..=expr.n_arguments() {
                        let (lhs, rhs) = t
                            .split()
                            .expect("Too many arguments for this expression???");
                        t = rhs;
                        if i <= args.len() {
                            arg_types.push(lhs);
                        } else {
                            if final_typ.is_none() {
                                final_typ = Some(t);
                            }
                            remaining_types.push(rhs);
                        }
                    }

                    let final_typ = final_typ.unwrap();
                    println!("final_typ = {final_typ}");

                    //is it representable as a literal? can we iterate over all of its unfilled arguments?
                    if (!t.is_function() || t.is_one_place_function())
                        && remaining_types.iter().all(|x| !x.is_function())
                    {
                        let domains = remaining_types
                            .iter()
                            .map(|x| Literal::domain(x, scenario).unwrap().collect::<Vec<_>>())
                            .collect::<Vec<_>>();

                        for x in domains.iter().multi_cartesian_product() {
                            let mut args = args.clone();
                            args.extend(x.into_iter().map(|x| Value::Base(x.clone())));
                            let e = expr.eval(args, scenario)?;
                        }

                        todo!();
                    } else {
                        Ok(Value::Primitive { expr, args })
                    }
                }
            }
        }
    }
}

impl<'src> Literal<'src> {
    fn domain(
        typ: &LambdaType,
        scenario: &Scenario<'src>,
    ) -> Option<impl Iterator<Item = Literal<'src>>> {
        match typ {
            LambdaType::A => Some(Either::Left(
                scenario.actors.iter().copied().map(Literal::Actor),
            )),
            LambdaType::E => Some(Either::Right(Either::Left(
                (0..scenario.thematic_relations.len())
                    .map(|x| Literal::Event(u8::try_from(x).unwrap())),
            ))),
            LambdaType::T => Some(Either::Right(Either::Right(
                [false, true].map(Literal::Bool).into_iter(),
            ))),
            LambdaType::Composition(..) => None,
        }
    }
}

impl<'src> RootedLambdaPool<'src, Expr<'src>> {
    ///Interprets an expression given a particular scenario.
    ///The resulting [`Value`] may be a [`Literal`] but may also still be an unreduced function
    ///(e.g. if you have a closure or the like)
    pub fn interp<'pool>(
        &'pool self,
        scenario: &Scenario<'src>,
    ) -> Result<Value<'src, 'pool, Expr<'src>>, UndefinedExpression> {
        self.pool.eval(self.root, vec![], scenario)
    }
}

impl<'src> LambdaPool<'src, Expr<'src>> {
    fn eval<'pool>(
        &'pool self,
        index: LambdaExprRef,
        variables: Vec<Value<'src, 'pool, Expr<'src>>>,
        scenario: &Scenario<'src>,
    ) -> Result<Value<'src, 'pool, Expr<'src>>, UndefinedExpression> {
        match self.get(index) {
            LambdaExpr::Lambda(body, arg_type) => Ok(Value::Closure {
                pool: self,
                arg_type,
                f: *body,
                env: variables.clone(),
            }),
            LambdaExpr::BoundVariable(x, _) => Ok(variables[variables.len() - 1 - *x].clone()),
            LambdaExpr::FreeVariable(..) => {
                todo!("No support for free variables yet.")
            }
            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                let argument = self.eval(*argument, variables.clone(), scenario)?;
                let subformula = self.eval(*subformula, variables.clone(), scenario)?;
                subformula.apply(argument, scenario)
            }
            LambdaExpr::LanguageOfThoughtExpr(x, ExprType::NoVar) => {
                if x.n_arguments() == 0 {
                    x.eval(vec![], scenario)
                } else {
                    Ok(Value::Primitive {
                        expr: *x,
                        args: vec![],
                    })
                }
            }

            LambdaExpr::LanguageOfThoughtExpr(expr, ExprType::BindVarTwoBodies(x, y)) => {
                todo!()
                /*
                variables.push(None);
                let x = Value::Function(
                    Box::new(self.eval(*x, variables.clone(), scenario)?),
                    expr.var_type().unwrap().clone(),
                    expr.typ().clone().lhs().unwrap().clone(),
                );
                let y = Value::Function(
                    Box::new(self.eval(*y, variables.clone(), scenario)?),
                    expr.var_type().unwrap().clone(),
                    expr.typ().clone().lhs().unwrap().clone(),
                );
                variables.pop();

                Ok(Value::App(
                    Box::new(Value::App(Box::new(Value::Expr(*expr)), Box::new(x))),
                    Box::new(y),
                )
                .reduce(variables, scenario)?)*/
            }
            LambdaExpr::LanguageOfThoughtExpr(expr, ExprType::BindVar(x)) => {
                todo!();
                /*
                variables.push(None);
                let x = Value::Function(
                    Box::new(self.eval(*x, variables.clone(), scenario)?),
                    expr.var_type().unwrap().clone(),
                    expr.typ().clone().lhs().unwrap().clone(),
                );
                variables.pop();

                Ok(Value::App(Box::new(Value::Expr(*expr)), Box::new(x))
                    .reduce(variables, scenario)?)*/
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::lambda::enumerator::Generator;

    use super::*;

    #[test]
    fn basic_interp() -> anyhow::Result<()> {
        let scenario = Scenario::parse(
            "<john,mary,phil (kind);{A: john,P: mary (likes)},{A: mary},{P: phil}>",
        )?;

        let data = [
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
                "some_e(all_e, lambda e x some(lambda a y ~pa_kind(y), lambda a y AgentOf(y,x)))",
                "True",
            ),
            (
                "lambda a x lambda a y pa_kind(x)",
                "lambda a x lambda a y {a_phil}(x)",
            ),
            ("some(x, all_a(x), pa_kind(x))", "True"),
            ("every(x, all_a(x), pa_kind(x))", "False"),
        ];

        let n_width = data
            .iter()
            .map(|(x, y)| x.chars().count() + y.chars().count() + 5)
            .max()
            .unwrap();

        for (phi, val) in data {
            print!("[{phi}] = {val}");
            let n_dots = n_width - phi.chars().count() - val.chars().count();
            print!("{}", ".".repeat(n_dots));

            let phi = RootedLambdaPool::parse(phi)?;
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

        let phi = RootedLambdaPool::parse("lambda a x pa_kind(x)")?;
        println!("{phi}");
        let v = phi.interp(&scenario).unwrap();
        println!("{v:?}");

        let phi = RootedLambdaPool::parse("lambda a x lambda a y pa_kind(x)")?;
        let v = phi.interp(&scenario).unwrap();
        println!("{v:?}");

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

        let types = vec![
            // LambdaType::A,
            LambdaType::E,
            //LambdaType::T,
            //LambdaType::at().clone(),
            //LambdaType::et().clone(),
            //LambdaType::from_string("<<a,t>,t>").unwrap(),
        ];

        let mut expressions = scenario.scenario_ops();
        expressions.extend(Expr::basic_ops());
        let mut generator: Generator<Expr> = Generator::new(expressions);

        for ty in types {
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
