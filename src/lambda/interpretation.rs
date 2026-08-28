#![expect(dead_code)]

use std::borrow::Cow;

use crate::{
    Actor, Entity, Event, Scenario,
    lambda::{
        ExprType, FreeVar, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, RootedLambdaPool,
        parser::ExprToken, types::LambdaType,
    },
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
enum BaseValue<'a> {
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
enum InnerValue<'a, T> {
    Base(BaseValue<'a>),
    Function(ValueId),
    Expr(T),
    Neutral(ValueId),
    Var(u32),
    FreeVar(FreeVar<'a>),
    App(ValueId, ValueId),
}

impl<'src, T> InnerValue<'src, T> {
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

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Value<'a, T>(Vec<InnerValue<'a, T>>);

impl<T> TryFrom<Value<'_, T>> for bool {
    type Error = ValueConversionError;
    fn try_from(value: Value<T>) -> Result<Self, Self::Error> {
        value
            .into_base_value()
            .and_then(|x| x.as_bool())
            .ok_or(ValueConversionError)
    }
}

impl<'src, T> Value<'src, T> {
    fn value_at<'a>(&'a self, id: ValueId) -> ValueRef<'a, 'src, T> {
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

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct ValueRef<'a, 'src, T>(ValueId, &'a Value<'src, T>);

impl<'a, 'src, T> ValueRef<'a, 'src, T> {
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
        arguments: &[ValueRef<'_, 'src, Expr<'src>>],
        scenario: &Scenario<'src>,
    ) -> Option<InnerValue<'src, Expr<'src>>> {
        let x = match self {
            Expr::Quantifier {
                quantifier,
                var_type,
            } => todo!(),
            Expr::Unary(MonOp::Iota(a_o_e)) => todo!(),
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
        Some(InnerValue::Base(x))
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
        let mut node_to_value_id: Vec<Option<ValueId>> = vec![None; expression.pool.0.len()];
        let mut value: Value<'src, Expr<'src>> = Value(vec![]);

        while let Some(x) = stack.pop() {
            match x {
                ValueBuilder::Search(nx) => {
                    stack.push(ValueBuilder::Build(nx));
                    stack.extend(expression.get(nx).get_children().map(ValueBuilder::Search));
                }

                ValueBuilder::Build(nx) => {
                    let node = expression.get(nx);
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
                        } => {
                            let sub_id = node_to_value_id[subformula.0 as usize].unwrap();
                            let arg_id = node_to_value_id[argument.0 as usize].unwrap();
                            let sub = &value.0[usize::from(sub_id)];
                            let arg = &value.0[usize::from(arg_id)];

                            let v = match (sub, arg) {
                                (InnerValue::Base(alpha), InnerValue::Base(beta)) => {
                                    InnerValue::Base(alpha.apply(beta))
                                }
                                (InnerValue::App(f, x_id), _) => {
                                    let mut arguments =
                                        vec![value.value_at(arg_id), value.value_at(*x_id)];
                                    let mut f = *f;
                                    while let InnerValue::App(new_f, new_arg) =
                                        value.0[usize::from(f)]
                                    {
                                        arguments.push(value.value_at(new_arg));
                                        f = new_f;
                                    }
                                    arguments.reverse();
                                    match &value.0[usize::from(f)] {
                                        InnerValue::Expr(e) => e.eval(&arguments, scenario)?,
                                        InnerValue::App(..) => {
                                            panic!("Impossible because of previous loop")
                                        }
                                        _ => todo!(),
                                    }
                                }
                                (InnerValue::Expr(e), x) => InnerValue::App(sub_id, arg_id),
                                //TODO: Figure out how to make it so that functions indicate when
                                //they can be evaluated (e.g. this will screw up if `e` takes only
                                //one argument!.
                                (InnerValue::Base(e), x) => InnerValue::App(sub_id, arg_id),
                                _ => todo!("Don't know how to combine {sub:?} and {arg:?}"),
                            };
                            value.0.push(v);
                            node_to_value_id[nx.0 as usize] =
                                Some(ValueId((value.0.len() - 1) as u32));
                        }
                        LambdaExpr::LanguageOfThoughtExpr(x, ExprType::NoVar) => {
                            if BaseValue::has_literal(x.typ()) {
                                value.0.push(x.eval(&[], scenario)?);
                                node_to_value_id[nx.0 as usize] =
                                    Some(ValueId((value.0.len() - 1) as u32));
                            } else {
                                value.0.push(InnerValue::Expr(*x));
                                node_to_value_id[nx.0 as usize] =
                                    Some(ValueId((value.0.len() - 1) as u32));
                            }
                        }
                        LambdaExpr::LanguageOfThoughtExpr(x, _) => {
                            todo!("figure out quantification")
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
        ];

        for (phi, val) in data {
            let phi = RootedLambdaPool::parse(phi)?;
            let calculated_value = phi.interp(&scenario).unwrap();
            println!("{phi:?} {calculated_value:?}");
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
