#![expect(dead_code)]

use crate::{
    Actor, Entity, Event, Scenario,
    lambda::{FreeVar, LambdaExpr, LambdaExprRef, RootedLambdaPool, types::LambdaType},
    language::{
        ActorOrEvent, BinOp, Constant,
        Expr::{self},
        MonOp,
    },
};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct ValueId(u32);

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum BaseValue<'a> {
    Bool(bool),
    Actor(Actor<'a>),
    Event(Event),
    ///A set of actors (represented as a vector).
    ActorSet(Vec<Actor<'a>>),
    ///A set of events (represented as a vector).
    EventSet(Vec<Event>),
}

impl<'src> BaseValue<'src> {
    fn typ(&self) -> LambdaType {
        match self {
            BaseValue::Bool(_) => LambdaType::T,
            BaseValue::Actor(_) => LambdaType::A,
            BaseValue::Event(_) => LambdaType::E,
            BaseValue::ActorSet(_) => LambdaType::at().clone(),
            BaseValue::EventSet(_) => LambdaType::et().clone(),
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

#[derive(Debug, Clone)]
enum InnerValue<'a> {
    Base(BaseValue<'a>),
    Function(ValueId),
    Neutral(ValueId),
    Var(u32),
    FreeVar(FreeVar<'a>),
    App(ValueId, ValueId),
}

impl<'src> InnerValue<'src> {
    fn to_base_value(&self) -> Option<&BaseValue<'src>> {
        if let InnerValue::Base(b) = self {
            Some(b)
        } else {
            None
        }
    }

    fn into_base_value(self) -> Option<BaseValue<'src>> {
        if let InnerValue::Base(b) = self {
            Some(b)
        } else {
            None
        }
    }
}

use thiserror::Error;
#[derive(Debug, Error)]
#[error("Not the desired type!")]
pub struct ValueConversionError;

#[derive(Debug, Clone)]
pub struct Value<'a>(Vec<InnerValue<'a>>);

impl TryFrom<Value<'_>> for bool {
    type Error = ValueConversionError;
    fn try_from(value: Value) -> Result<Self, Self::Error> {
        value
            .into_base_value()
            .and_then(|x| x.as_bool())
            .ok_or(ValueConversionError)
    }
}

impl<'src> Value<'src> {
    fn value_at<'a>(&'a self, id: ValueId) -> ValueRef<'a, 'src> {
        ValueRef(id, self)
    }

    fn into_base_value(mut self) -> Option<BaseValue<'src>> {
        self.0.swap_remove(self.0.len() - 1).into_base_value()
    }
}

enum ValueBuilder {
    ///We haven't seen this value yet
    Search(LambdaExprRef),
    ///We've built its children
    Build(LambdaExprRef),
}

struct ValueRef<'a, 'src>(ValueId, &'a Value<'src>);

impl<'a, 'src> ValueRef<'a, 'src> {
    fn is_neutral(&self) -> bool {
        matches!(self.1.0[self.0.0 as usize], InnerValue::Neutral(_))
    }
    fn to_base_value(&self) -> Option<&'a BaseValue<'src>> {
        self.1.0[self.0.0 as usize].to_base_value()
    }
}

impl<'src> Expr<'src> {
    fn eval(
        &self,
        arguments: &[ValueRef<'_, 'src>],
        scenario: &Scenario<'src>,
    ) -> Option<Vec<InnerValue<'src>>> {
        let x = match self {
            Expr::Quantifier {
                quantifier,
                var_type,
            } => todo!(),
            Expr::Variable(variable) => todo!(),
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
            Expr::Unary(MonOp::Property(p, a_or_e)) => {
                let p = scenario.properties.get(p)?;
                let arg = arguments.first().unwrap();

                if let Some(arg) = arg.to_base_value() {
                    let e = arg.as_entity().unwrap();
                    BaseValue::Bool(p.contains(&e))
                } else {
                    let e = arg.0;
                    let p = match a_or_e {
                        ActorOrEvent::Actor => BaseValue::ActorSet(
                            p.iter()
                                .filter_map(|x| match x {
                                    Entity::Actor(a) => Some(*a),
                                    Entity::Event(_) => None,
                                })
                                .collect(),
                        ),
                        ActorOrEvent::Event => BaseValue::EventSet(
                            p.iter()
                                .filter_map(|x| match x {
                                    Entity::Actor(_) => None,
                                    Entity::Event(e) => Some(*e),
                                })
                                .collect(),
                        ),
                    };

                    let value_len = ValueId(arguments[0].1.0.len() as u32);

                    return Some(vec![InnerValue::Base(p), InnerValue::App(value_len, e)]);
                }
            }

            Expr::Unary(MonOp::Iota(a_o_e)) => todo!(),
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
        Some(vec![InnerValue::Base(x)])
    }
}

impl<'src> RootedLambdaPool<'src, Expr<'src>> {
    pub fn interp(&self, scenario: &Scenario<'src>) -> Option<Value<'src>> {
        let mut stack = vec![ValueBuilder::Search(self.root)];
        let mut node_to_value_id: Vec<Option<ValueId>> = vec![None; self.pool.0.len()];
        let mut value = Value(vec![]);

        while let Some(x) = stack.pop() {
            match x {
                ValueBuilder::Search(nx) => {
                    let node = self.get(nx);
                    stack.push(ValueBuilder::Build(nx));
                    stack.extend(self.get(nx).get_children().map(ValueBuilder::Search));
                }

                ValueBuilder::Build(nx) => {
                    let node = self.get(nx);
                    match node {
                        LambdaExpr::Lambda(arg, _) => {
                            let arg_val = node_to_value_id[arg.0 as usize].unwrap();
                            value.0.push(InnerValue::Function(arg_val));
                            node_to_value_id[nx.0 as usize] =
                                Some(ValueId((value.0.len() - 1) as u32));
                        }
                        LambdaExpr::BoundVariable(e, _) => {
                            value.0.push(InnerValue::Var(*e as u32));
                            node_to_value_id[nx.0 as usize] =
                                Some(ValueId((value.0.len() - 1) as u32));
                        }
                        LambdaExpr::FreeVariable(free_var, _) => {
                            value.0.push(InnerValue::FreeVar(*free_var));
                            value
                                .0
                                .push(InnerValue::Neutral(ValueId((value.0.len() - 1) as u32)));
                            node_to_value_id[nx.0 as usize] =
                                Some(ValueId((value.0.len() - 1) as u32));
                        }
                        LambdaExpr::Application {
                            subformula,
                            argument,
                        } => todo!(),
                        LambdaExpr::LanguageOfThoughtExpr(x, y) => {
                            let children = node
                                .get_children()
                                .map(|x| node_to_value_id[x.0 as usize].map(|x| value.value_at(x)))
                                .collect::<Option<Vec<_>>>()
                                .unwrap();

                            if children.iter().all(|x| !x.is_neutral()) {
                                debug_assert_eq!(
                                    children.len(),
                                    node.n_children(),
                                    "Inconsistent children length!"
                                );
                                let v = x.eval(&children, scenario)?;
                                value.0.extend(v);
                                node_to_value_id[nx.0 as usize] =
                                    Some(ValueId((value.0.len() - 1) as u32));
                            } else {
                                todo!()
                            }
                        }
                    }
                }
            }
        }

        Some(value)
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
            ("True | True", BaseValue::Bool(true)),
            ("True | False", BaseValue::Bool(true)),
            ("False | True", BaseValue::Bool(true)),
            ("False | False", BaseValue::Bool(false)),
            ("True & True", BaseValue::Bool(true)),
            ("True & False", BaseValue::Bool(false)),
            ("False & True", BaseValue::Bool(false)),
            ("False & False", BaseValue::Bool(false)),
            ("AgentOf(a_john, e_0) | False", BaseValue::Bool(true)),
        ];

        for (phi, val) in data {
            let phi = RootedLambdaPool::parse(phi)?;
            assert_eq!(
                phi.interp(&scenario).unwrap().into_base_value().unwrap(),
                val
            );
        }
        let mut phi = RootedLambdaPool::parse("lambda a x pa_kind(x)")?;
        println!("{phi}");
        let v = phi.interp(&scenario).unwrap();
        println!("{v:?}");

        let mut phi = RootedLambdaPool::parse("lambda a x lambda a y pa_kind(x)")?;
        let v = phi.interp(&scenario).unwrap();
        println!("{v:?}");

        Ok(())
    }
}
