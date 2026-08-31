#![expect(dead_code)]

use std::borrow::Cow;

use crate::{
    Actor, Entity, Event, Scenario,
    lambda::{ExprType, FreeVar, LambdaExpr, LambdaExprRef, RootedLambdaPool, types::LambdaType},
    language::{
        ActorOrEvent::{self},
        BinOp, Constant,
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
    Expr(T),
    Neutral(Box<Value<'a, T>>),
    Var(usize),
    FreeVar(FreeVar<'a>),
    App(Box<Value<'a, T>>, Box<Value<'a, T>>),
}

impl<'src> Value<'src, Expr<'src>> {
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

impl<'src> TryFrom<Value<'src, Expr<'src>>> for bool {
    type Error = ValueConversionError;
    fn try_from(value: Value<'src, Expr<'src>>) -> Result<Self, Self::Error> {
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

    fn can_eval(&self, arguments: &[&Value<'src, Expr<'src>>]) -> bool {
        match self {
            Expr::Quantifier { .. } => arguments
                .iter()
                .all(|x| matches!(x, Value::Base(_) | Value::Function(..))),
            Expr::Binary(_) => arguments.iter().all(|x| matches!(x, Value::Base(_))),
            Expr::Unary(MonOp::Not) => matches!(arguments.first().unwrap(), Value::Base(_)),
            Expr::Unary(MonOp::Iota(_)) => todo!(),
            Expr::Constant(_) | Expr::Actor(_) | Expr::Event(_) => true,
        }
    }

    fn eval(
        &self,
        mut arguments: Vec<Value<'src, Expr<'src>>>,
        scenario: &Scenario<'src>,
    ) -> Option<Value<'src, Expr<'src>>> {
        let x = match self {
            Expr::Quantifier { .. } => {
                println!("Quantifier args!!");
                let predicate = arguments.pop().unwrap();
                let restrictor = arguments.pop().unwrap();
                println!("{predicate:?} {restrictor:?}");
                todo!()
            }
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
                    .pop()
                    .unwrap()
                    .into_base_value()
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

impl<'src> Value<'src, Expr<'src>> {
    fn primitive_head(&self, last_arg: &Value<'src, Expr<'src>>) -> bool {
        let mut x = self;
        let mut args = vec![last_arg];
        if let Value::Expr(t) = x {
            return t.n_arguments() == args.len() && t.can_eval(&args);
        }

        while let Value::App(y, arg) = x {
            args.push(&**arg);
            if let Value::Expr(x) = &**y {
                args.reverse();
                return x.n_arguments() == args.len() && x.can_eval(&args);
            }
            x = y;
        }
        false
    }

    fn primitive_head_and_arguments(
        mut self,
        last_arg: Value<'src, Expr<'src>>,
    ) -> Option<(Expr<'src>, Vec<Value<'src, Expr<'src>>>)> {
        self = Value::App(Box::new(self), Box::new(last_arg));
        let mut arguments = vec![];
        while let Value::App(x, arg) = self {
            arguments.push(*arg);
            if let Value::Expr(x) = *x {
                arguments.reverse();
                return Some((x, arguments));
            }
            self = *x
        }
        None
    }

    fn reduce(
        self,
        variable: &Value<'src, Expr<'src>>,
        depth: usize,
        scenario: &Scenario<'src>,
    ) -> Option<Value<'src, Expr<'src>>> {
        println!("VARIABLE MUST BE ADJUSTED IF IT HAS DEBRUIJN INDICIES");
        match self {
            Value::Function(value) => value.reduce(variable, depth + 1, scenario),
            Value::App(f, arg) => {
                let f = f.reduce(variable, depth, scenario)?;
                let arg = arg.reduce(variable, depth, scenario)?;
                f.apply(arg, scenario)
            }
            Value::Neutral(_) => todo!(),
            Value::Var(x) if x == depth => Some(variable.clone()),
            Value::Var(x) if x > depth => Some(Value::Var(x - 1)),
            v @ (Value::Var(_) | Value::FreeVar(_) | Value::Base(_) | Value::Expr(_)) => Some(v),
        }
    }

    fn apply(self, other: Self, scenario: &Scenario<'src>) -> Option<Self> {
        Some(match (self, other) {
            (Value::Base(alpha), Value::Base(beta)) => Value::Base(alpha.apply(&beta)),
            (x, y) if x.primitive_head(&y) => {
                let (head, arguments) = x
                    .primitive_head_and_arguments(y)
                    .expect("Already checked the head was primitive!");
                head.eval(arguments, scenario)?
            }
            (Value::Function(x), variable) => x.reduce(&variable, 0, scenario)?,
            (x, y) => Value::App(Box::new(x), Box::new(y)),
        })
    }

    fn highest_var(&self) -> Option<usize> {
        todo!("Figure out what the highest var used in this expression is!");
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
        expression.interp_inner(expression.root, vec![], scenario)
    }

    fn interp_inner(
        &self,
        index: LambdaExprRef,
        mut variables: Vec<Option<Value<'src, Expr<'src>>>>,
        scenario: &Scenario<'src>,
    ) -> Option<Value<'src, Expr<'src>>> {
        match self.get(index) {
            LambdaExpr::Lambda(body, t) => {
                variables.push(None);
                let body = self.interp_inner(*body, variables, scenario)?;

                if BaseValue::has_literal(t) && matches!(body.highest_var(), None | Some(0)) {
                    todo!("write automatic converter from these types to literals");
                } else {
                    Some(Value::Function(Box::new(body)))
                }
            }
            LambdaExpr::BoundVariable(x, _) => {
                Some(match variables[variables.len() - 1 - *x].as_ref() {
                    Some(x) => x.clone(),
                    None => Value::Var(*x),
                })
            }
            LambdaExpr::FreeVariable(..) => {
                todo!("No support for free variables yet.")
            }
            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                let subformula = self.interp_inner(*subformula, variables.clone(), scenario)?;
                let argument = self.interp_inner(*argument, variables, scenario)?;
                subformula.apply(argument, scenario)
            }
            LambdaExpr::LanguageOfThoughtExpr(x, ExprType::NoVar) => {
                if x.n_arguments() == 0 {
                    x.eval(vec![], scenario)
                } else {
                    Some(Value::Expr(*x))
                }
            }
            LambdaExpr::LanguageOfThoughtExpr(
                _,
                ExprType::BindVar(_) | ExprType::BindVarTwoBodies(..),
            ) => todo!("Binding vars is for later!"),
        }
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
            (
                "some(lambda a x pa_kind(x) | ~pa_kind(x), pa_kind)",
                BaseValue::Bool(true),
            ),
            ("some(all_a, pa_kind)", BaseValue::Bool(true)),
            ("every(all_a, pa_kind)", BaseValue::Bool(false)),
            ("some(x, all_a(x), pa_kind(x))", BaseValue::Bool(true)),
            ("every(x, all_a(x), pa_kind(x))", BaseValue::Bool(false)),
        ];

        for (phi, val) in data {
            println!("{phi}");
            let phi = RootedLambdaPool::parse(phi)?;
            let calculated_value = phi.interp(&scenario).unwrap();
            println!("{calculated_value:#?}");
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
