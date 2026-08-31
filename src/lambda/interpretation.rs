#![expect(dead_code)]

use std::borrow::Cow;

use crate::{
    Actor, Entity, Event, Scenario,
    lambda::{ExprType, FreeVar, LambdaExpr, LambdaExprRef, RootedLambdaPool, types::LambdaType},
    language::{
        ActorOrEvent, BinOp, Constant,
        Expr::{self},
        MonOp,
    },
};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct ValueId(u32);

impl From<ValueId> for usize {
    fn from(value: ValueId) -> Self {
        value.0 as usize
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum BaseValue<'a> {
    Bool(bool),
    Actor(Actor<'a>),
    Event(Event),
    ///A set of actors (represented as a vector).
    ActorSet(Vec<Actor<'a>>),
    ///A set of events (represented as a vector).
    EventSet(Vec<Event>),
    //A mapping from truth to truth.
    TruthTable(bool, bool),
}

impl<'src> BaseValue<'src> {
    fn has_literal(typ: &LambdaType) -> bool {
        !typ.is_function() || typ.is_one_place_function()
    }

    fn typ(&self) -> &LambdaType {
        match self {
            BaseValue::Bool(_) => &LambdaType::T,
            BaseValue::Actor(_) => &LambdaType::A,
            BaseValue::Event(_) => &LambdaType::E,
            BaseValue::ActorSet(_) => LambdaType::at(),
            BaseValue::EventSet(_) => LambdaType::et(),
            BaseValue::TruthTable(_, _) => LambdaType::tt(),
        }
    }

    fn apply(&self, other: &BaseValue<'src>) -> BaseValue<'src> {
        match (self, other) {
            (BaseValue::ActorSet(items), BaseValue::Actor(a)) => BaseValue::Bool(items.contains(a)),
            (BaseValue::EventSet(items), BaseValue::Event(e)) => BaseValue::Bool(items.contains(e)),
            (BaseValue::TruthTable(t, f), BaseValue::Bool(b)) => {
                BaseValue::Bool(if *b { *t } else { *f })
            }
            _ => panic!("Type error that shouldn't occur!"),
        }
    }

    fn as_bool(&self) -> Option<bool> {
        if let BaseValue::Bool(b) = self {
            Some(*b)
        } else {
            None
        }
    }

    fn as_entity(&self) -> Option<Entity<'src>> {
        match self {
            BaseValue::Actor(a) => Some(Entity::Actor(a)),
            BaseValue::Event(e) => Some(Entity::Event(*e)),
            _ => None,
        }
    }

    fn as_actor(&self) -> Option<Actor<'src>> {
        match self {
            BaseValue::Actor(a) => Some(a),
            _ => None,
        }
    }

    fn as_event(&self) -> Option<Event> {
        match self {
            BaseValue::Event(e) => Some(*e),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Ord, Eq)]
pub enum Value<'a, T> {
    Base(BaseValue<'a>),
    Function(Box<Value<'a, T>>),
    PrimitiveFunction { func: T, args: Vec<Value<'a, T>> },
    Neutral(Box<Value<'a, T>>),
    Var(u32),
    FreeVar(FreeVar<'a>),
    App(Box<Value<'a, T>>, Box<Value<'a, T>>),
}

impl<'src, T> Value<'src, T> {
    fn to_base_value(&self) -> Option<&BaseValue<'src>> {
        if let Value::Base(b) = self {
            Some(b)
        } else {
            None
        }
    }

    fn into_base_value(self) -> Option<BaseValue<'src>> {
        if let Value::Base(b) = self {
            Some(b)
        } else {
            None
        }
    }
    fn is_neutral(&self) -> bool {
        matches!(&self, Value::Neutral(_))
    }
}

use thiserror::Error;
#[derive(Debug, Error)]
#[error("Not the desired type!")]
pub struct ValueConversionError;

impl<T> TryFrom<Value<'_, T>> for bool {
    type Error = ValueConversionError;
    fn try_from(value: Value<T>) -> Result<Self, Self::Error> {
        value
            .into_base_value()
            .and_then(|x| x.as_bool())
            .ok_or(ValueConversionError)
    }
}

enum ValueBuilder {
    ///We haven't seen this value yet
    Search(LambdaExprRef),
    ///We've built its children
    Build(LambdaExprRef),
}

impl<'src> Expr<'src> {
    fn n_arguments(&self) -> usize {
        match self {
            Expr::Quantifier { .. } => 2,
            Expr::Binary(_) => 2,
            Expr::Unary(_) => 1,
            Expr::Constant(_) | Expr::Actor(_) | Expr::Event(_) => 0,
        }
    }

    fn eval(
        &self,
        arguments: &[Value<'src, Expr<'src>>],
        scenario: &Scenario<'src>,
    ) -> Option<Value<'src, Expr<'src>>> {
        let x = match self {
            Expr::Quantifier { .. } => todo!(),
            Expr::Unary(MonOp::Iota(_)) => todo!(),
            Expr::Actor(a) => BaseValue::Actor(a),
            Expr::Event(e) => BaseValue::Event(*e),
            Expr::Binary(op @ (BinOp::AgentOf | BinOp::PatientOf), ..) => {
                let a = arguments[0].to_base_value().unwrap().as_actor().unwrap();
                let e = arguments[1].to_base_value().unwrap().as_event().unwrap();
                let e = scenario.thematic_relations[usize::from(e)];
                BaseValue::Bool(match op {
                    BinOp::AgentOf => e.agent.is_some_and(|x| x == a),
                    BinOp::PatientOf => e.patient.is_some_and(|x| x == a),
                    _ => panic!("impossible bc of prior check!"),
                })
            }
            Expr::Binary(BinOp::And) => BaseValue::Bool(arguments.iter().all(|x| {
                x.to_base_value()
                    .unwrap()
                    .as_bool()
                    .expect("Type inference error!")
            })),
            Expr::Binary(BinOp::Or) => BaseValue::Bool(arguments.iter().any(|x| {
                x.to_base_value()
                    .unwrap()
                    .as_bool()
                    .expect("Type inference error!")
            })),
            Expr::Unary(MonOp::Not) => BaseValue::Bool(
                !arguments
                    .first()
                    .unwrap()
                    .to_base_value()
                    .unwrap()
                    .as_bool()
                    .unwrap(),
            ),
            Expr::Constant(Constant::Everyone) => BaseValue::ActorSet(scenario.actors.clone()),
            Expr::Constant(Constant::EveryEvent) => {
                BaseValue::EventSet(scenario.events().collect())
            }
            Expr::Constant(Constant::Tautology) => BaseValue::Bool(true),
            Expr::Constant(Constant::Contradiction) => BaseValue::Bool(false),
            Expr::Constant(Constant::Property(p, a_or_e)) => {
                let x = scenario.properties.get(p)?;
                match a_or_e {
                    ActorOrEvent::Actor => BaseValue::ActorSet(
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
                    ActorOrEvent::Event => BaseValue::EventSet(
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
        Some(Value::Base(x))
    }
}

impl<'src> RootedLambdaPool<'src, Expr<'src>> {
    pub fn interp(&self, scenario: &Scenario<'src>) -> Option<Value<'src, Expr<'src>>> {
        let expression: Cow<Self> = if !self.is_reduced() {
            let mut x = self.clone();
            x.reduce().expect("Can't reduce :(");
            Cow::Owned(x)
        } else {
            Cow::Borrowed(self)
        };

        let mut stack = vec![ValueBuilder::Search(expression.root)];
        let mut node_to_value: Vec<Option<Value<'src, Expr<'src>>>> =
            vec![None; expression.pool.0.len()];

        while let Some(x) = stack.pop() {
            match x {
                ValueBuilder::Search(nx) => {
                    stack.push(ValueBuilder::Build(nx));
                    stack.extend(expression.get(nx).get_children().map(ValueBuilder::Search));
                }

                ValueBuilder::Build(nx) => {
                    let node = expression.get(nx);
                    node_to_value[nx.0 as usize] = Some(match node {
                        LambdaExpr::Lambda(arg, _) => {
                            let arg = node_to_value[arg.0 as usize].take().unwrap();
                            Value::Function(Box::new(arg))
                        }
                        LambdaExpr::BoundVariable(e, _) => Value::Var(*e as u32),
                        LambdaExpr::FreeVariable(free_var, _) => {
                            Value::Neutral(Box::new(Value::FreeVar(*free_var)))
                        }
                        LambdaExpr::Application {
                            subformula,
                            argument,
                        } => {
                            let sub = node_to_value[subformula.0 as usize].take().unwrap();
                            let arg = node_to_value[argument.0 as usize].take().unwrap();
                            match (sub, arg) {
                                (Value::Base(alpha), Value::Base(beta)) => {
                                    Value::Base(alpha.apply(&beta))
                                }
                                (Value::PrimitiveFunction { func, mut args }, arg) => {
                                    args.push(arg);
                                    if func.n_arguments() == args.len() {
                                        func.eval(&args, scenario)?
                                    } else {
                                        Value::PrimitiveFunction { func, args }
                                    }
                                }
                                (sub, arg) => {
                                    todo!("Don't know how to combine {sub:?} and {arg:?}")
                                }
                            }
                        }
                        LambdaExpr::LanguageOfThoughtExpr(x, ExprType::NoVar) => {
                            if x.n_arguments() == 0 {
                                x.eval(&[], scenario)?
                            } else {
                                Value::PrimitiveFunction {
                                    func: *x,
                                    args: vec![],
                                }
                            }
                        }
                        LambdaExpr::LanguageOfThoughtExpr(_, _) => {
                            todo!("figure out quantification")
                        }
                    });
                    println!(
                        "{} {:#?}",
                        nx.0,
                        node_to_value[nx.0 as usize].as_ref().unwrap()
                    );
                }
            }
        }

        node_to_value[self.root.0 as usize].take()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn basic_interp() -> anyhow::Result<()> {
        let scenario =
            Scenario::parse("<john,mary,phil (kind);{A: john,P: mary},{A: mary},{P: phil}>")?;

        let data = [
            ("a_john", BaseValue::Actor("john")),
            ("pa_kind(a_john)", BaseValue::Bool(false)),
            ("True | True", BaseValue::Bool(true)),
            ("True | False", BaseValue::Bool(true)),
            ("False | True", BaseValue::Bool(true)),
            ("False | False", BaseValue::Bool(false)),
            ("True & True", BaseValue::Bool(true)),
            ("True & False", BaseValue::Bool(false)),
            ("False & True", BaseValue::Bool(false)),
            ("False & False", BaseValue::Bool(false)),
            ("~False", BaseValue::Bool(true)),
            ("~True", BaseValue::Bool(false)),
            ("~(False & False)", BaseValue::Bool(true)),
            ("AgentOf(a_john, e_0) | False", BaseValue::Bool(true)),
            ("some(all_a, pa_kind)", BaseValue::Bool(true)),
            ("every(all_a, pa_kind)", BaseValue::Bool(false)),
            ("some(x, all_a(x), pa_kind(x))", BaseValue::Bool(true)),
            ("every(x, all_a(x), pa_kind(x))", BaseValue::Bool(false)),
        ];

        for (phi, val) in data {
            println!("{phi}");
            let phi = RootedLambdaPool::parse(phi)?;
            let calculated_value = phi.interp(&scenario).unwrap();
            assert_eq!(calculated_value.into_base_value().unwrap(), val);
        }
        let phi = RootedLambdaPool::parse("lambda a x pa_kind(x)")?;
        println!("{phi}");
        let v = phi.interp(&scenario).unwrap();
        println!("{v:?}");

        let mut phi = RootedLambdaPool::parse("lambda a x lambda a y pa_kind(x)")?;
        let v = phi.interp(&scenario).unwrap();
        println!("{v:?}");

        Ok(())
    }
}
