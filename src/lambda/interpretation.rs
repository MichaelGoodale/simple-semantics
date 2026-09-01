#![expect(dead_code)]

use std::{borrow::Cow, fmt::Display, iter::repeat_n};

use crate::{
    Actor, Entity, Event, Scenario,
    lambda::{
        ExprType, FreeVar, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, RootedLambdaPool,
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
use itertools::{Either, Itertools};
use thiserror::Error;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct ValueId(u32);

impl From<ValueId> for usize {
    fn from(value: ValueId) -> Self {
        value.0 as usize
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Literal<'a> {
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
            Literal::TruthTable(on_true, on_false) => {
                write!(f, "False → {on_false}, True → {on_true}")
            }
        }
    }
}

impl<'src> Literal<'src> {
    fn into_actor_set(self) -> Option<Vec<Actor<'src>>> {
        let Literal::ActorSet(x) = self else {
            return None;
        };
        Some(x)
    }

    fn into_event_set(self) -> Option<Vec<Event>> {
        let Literal::EventSet(x) = self else {
            return None;
        };
        Some(x)
    }

    fn has_literal(typ: &LambdaType) -> bool {
        !typ.is_function() || typ.is_one_place_function()
    }

    fn make_function_literal(
        body: Value<'src, Expr<'src>>,
        var_type: &LambdaType,
        expr_type: &LambdaType,
        scenario: &Scenario<'src>,
    ) -> Literal<'src> {
        //This is a closed expression that can be turned into a literal (check for neutral too)

        let f = Value::Function(Box::new(body), var_type.clone(), expr_type.clone());
        let bool_apply = |f: Value<'src, Expr<'src>>, x| {
            let v = f.apply(Value::Base(x), vec![], scenario).unwrap();
            v.into_base_value().unwrap().as_bool().unwrap()
        };

        match var_type {
            LambdaType::T => Literal::TruthTable(
                bool_apply(f.clone(), Literal::Bool(true)),
                bool_apply(f, Literal::Bool(false)),
            ),
            LambdaType::A => {
                let mut set = vec![];
                for (actor, f) in scenario
                    .actors
                    .iter()
                    .copied()
                    .zip(repeat_n(f, scenario.actors.len()))
                {
                    if bool_apply(f.clone(), Literal::Actor(actor)) {
                        set.push(actor);
                    }
                }
                Literal::ActorSet(set)
            }
            LambdaType::E => {
                let mut set = vec![];
                for (event, f) in scenario.events().zip(repeat_n(f, scenario.events().len())) {
                    if bool_apply(f.clone(), Literal::Event(event)) {
                        set.push(event);
                    }
                }
                Literal::EventSet(set)
            }
            _ => panic!("Cannot make something with var_type={var_type} a literal"),
        }
    }

    fn typ(&self) -> &LambdaType {
        match self {
            Literal::Bool(_) => &LambdaType::T,
            Literal::Actor(_) => &LambdaType::A,
            Literal::Event(_) => &LambdaType::E,
            Literal::ActorSet(_) => LambdaType::at(),
            Literal::EventSet(_) => LambdaType::et(),
            Literal::TruthTable(_, _) => LambdaType::tt(),
        }
    }

    fn apply(&self, other: &Literal<'src>) -> Literal<'src> {
        match (self, other) {
            (Literal::ActorSet(items), Literal::Actor(a)) => Literal::Bool(items.contains(a)),
            (Literal::EventSet(items), Literal::Event(e)) => Literal::Bool(items.contains(e)),
            (Literal::TruthTable(t, f), Literal::Bool(b)) => {
                Literal::Bool(if *b { *t } else { *f })
            }
            _ => panic!("Type error that shouldn't occur!"),
        }
    }

    fn as_bool(&self) -> Option<bool> {
        if let Literal::Bool(b) = self {
            Some(*b)
        } else {
            None
        }
    }

    fn as_entity(&self) -> Option<Entity<'src>> {
        match self {
            Literal::Actor(a) => Some(Entity::Actor(a)),
            Literal::Event(e) => Some(Entity::Event(*e)),
            _ => None,
        }
    }

    fn as_actor(&self) -> Option<Actor<'src>> {
        match self {
            Literal::Actor(a) => Some(a),
            _ => None,
        }
    }

    fn as_event(&self) -> Option<Event> {
        match self {
            Literal::Event(e) => Some(*e),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Ord, Eq)]
pub enum Value<'a, T> {
    Base(Literal<'a>),
    Function(Box<Value<'a, T>>, LambdaType, LambdaType),
    Expr(T),
    Neutral(Box<Value<'a, T>>),
    Var(usize),
    FreeVar(FreeVar<'a>, LambdaType),
    App(Box<Value<'a, T>>, Box<Value<'a, T>>),
}

impl<'src> Value<'src, Expr<'src>> {
    fn to_base_value(&self) -> Option<&Literal<'src>> {
        if let Value::Base(b) = self {
            Some(b)
        } else {
            None
        }
    }

    fn into_base_value(self) -> Option<Literal<'src>> {
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
            Expr::Quantifier { .. } => arguments.iter().all(|x| matches!(x, Value::Base(_))),
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
            Expr::Quantifier {
                quantifier,
                var_type,
            } => {
                let predicate = arguments.pop().unwrap().into_base_value().unwrap();
                let restrictor = arguments.pop().unwrap().into_base_value().unwrap();
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
            Expr::Unary(MonOp::Iota(_)) => todo!(),
            Expr::Actor(a) => Literal::Actor(a),
            Expr::Event(e) => Literal::Event(*e),
            Expr::Binary(op @ (BinOp::AgentOf | BinOp::PatientOf), ..) => {
                let a = arguments[0].to_base_value().unwrap().as_actor().unwrap();
                let e = arguments[1].to_base_value().unwrap().as_event().unwrap();
                let e = scenario.thematic_relations[usize::from(e)];
                Literal::Bool(match op {
                    BinOp::AgentOf => e.agent.is_some_and(|x| x == a),
                    BinOp::PatientOf => e.patient.is_some_and(|x| x == a),
                    _ => panic!("impossible bc of prior check!"),
                })
            }
            Expr::Binary(BinOp::And) => Literal::Bool(arguments.iter().all(|x| {
                x.to_base_value()
                    .unwrap()
                    .as_bool()
                    .expect("Type inference error!")
            })),
            Expr::Binary(BinOp::Or) => Literal::Bool(arguments.iter().any(|x| {
                x.to_base_value()
                    .unwrap()
                    .as_bool()
                    .expect("Type inference error!")
            })),
            Expr::Unary(MonOp::Not) => Literal::Bool(
                !arguments
                    .pop()
                    .unwrap()
                    .into_base_value()
                    .unwrap()
                    .as_bool()
                    .unwrap(),
            ),
            Expr::Constant(Constant::Everyone) => Literal::ActorSet(scenario.actors.clone()),
            Expr::Constant(Constant::EveryEvent) => Literal::EventSet(scenario.events().collect()),
            Expr::Constant(Constant::Tautology) => Literal::Bool(true),
            Expr::Constant(Constant::Contradiction) => Literal::Bool(false),
            Expr::Constant(Constant::Property(p, a_or_e)) => {
                let x = scenario.properties.get(p)?;
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
        Some(Value::Base(x))
    }
}

impl<'src> Value<'src, Expr<'src>> {
    fn children<'a>(&'a self) -> impl Iterator<Item = &'a Value<'src, Expr<'src>>> {
        match self {
            Value::Base(_) | Value::Expr(_) | Value::Var(_) | Value::FreeVar(_, _) => {
                Either::Left(std::iter::empty())
            }
            Value::Function(value, _, _) | Value::Neutral(value) => {
                Either::Right(Either::Left(std::iter::once(&**value)))
            }
            Value::App(v1, v2) => Either::Right(Either::Right([&**v1, &**v2].into_iter())),
        }
    }

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

    fn reduce_fully(self, scenario: &Scenario<'src>) {
        let mut stack = vec![self];
        while let Some(x) = stack.pop() {
            match x {
                Value::Base(literal) => todo!(),
                Value::Function(value, lambda_type, lambda_type1) => todo!(),
                Value::Expr(_) => todo!(),
                Value::Neutral(value) => todo!(),
                Value::Var(_) => todo!(),
                Value::FreeVar(free_var, lambda_type) => todo!(),
                Value::App(value, value1) => todo!(),
            }
        }
    }

    fn reduce(
        self,
        mut variables: Vec<Option<Value<'src, Expr<'src>>>>,
        scenario: &Scenario<'src>,
    ) -> Option<Value<'src, Expr<'src>>> {
        match self {
            Value::Function(body, var_type, expr_type) => {
                variables.push(None);
                let body = body.reduce(variables, scenario)?;
                if Literal::has_literal(&expr_type) && !body.open_var() {
                    Some(Value::Base(Literal::make_function_literal(
                        body, &var_type, &expr_type, scenario,
                    )))
                } else {
                    Some(Value::Function(Box::new(body), var_type, expr_type))
                }
            }
            Value::App(f, arg) => f.apply(*arg, variables, scenario),
            Value::Neutral(_) => todo!(),
            Value::Var(x) => Some(match variables[variables.len() - 1 - x].as_ref() {
                Some(x) => x.clone(),
                None => Value::Var(x),
            }),
            v @ (Value::FreeVar(..) | Value::Base(_) | Value::Expr(_)) => Some(v),
        }
    }

    fn apply(
        self,
        other: Self,
        mut variables: Vec<Option<Value<'src, Expr<'src>>>>,
        scenario: &Scenario<'src>,
    ) -> Option<Self> {
        Some(match (self, other) {
            (Value::Base(alpha), Value::Base(beta)) => Value::Base(alpha.apply(&beta)),
            (x, y) if x.primitive_head(&y) => {
                let (head, arguments) = x
                    .primitive_head_and_arguments(y)
                    .expect("Already checked the head was primitive!");
                head.eval(arguments, scenario)?
            }
            (Value::Function(x, _, _), variable) => {
                let v = variable.reduce(variables.clone(), scenario)?;
                variables.push(Some(v));
                x.reduce(variables, scenario)?
            }
            (x, y) => {
                let x = x.reduce(variables.clone(), scenario)?;
                let y = y.reduce(variables.clone(), scenario)?;
                match (x, y) {
                    (Value::Base(alpha), Value::Base(beta)) => Value::Base(alpha.apply(&beta)),
                    (x, y) if x.primitive_head(&y) => {
                        let (head, arguments) = x
                            .primitive_head_and_arguments(y)
                            .expect("Already checked the head was primitive!");
                        head.eval(arguments, scenario)?
                    }
                    (Value::Function(x, _, _), variable) => {
                        let v = variable.reduce(variables.clone(), scenario)?;
                        variables.push(Some(v));
                        x.reduce(variables, scenario)?
                    }
                    (x, y) => Value::App(Box::new(x), Box::new(y)),
                }
            }
        })
    }

    fn open_var(&self) -> bool {
        let mut stack = vec![(self, 0)];

        while let Some((s, mut d)) = stack.pop() {
            if let Value::Var(n) = s {
                if *n > d {
                    return true;
                }
            } else if matches!(s, Value::Function(..)) {
                d += 1;
            }
            stack.extend(s.children().map(|x| (x, d)))
        }
        false
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
            LambdaExpr::Lambda(body, var_type) => {
                variables.push(None);
                let expr_type = self.pool.get_type(index).unwrap();
                let body = self.interp_inner(*body, variables, scenario)?;

                if Literal::has_literal(&expr_type) && !body.open_var() {
                    Some(Value::Base(Literal::make_function_literal(
                        body, var_type, &expr_type, scenario,
                    )))
                } else {
                    Some(Value::Function(
                        Box::new(body),
                        var_type.clone(),
                        expr_type.clone(),
                    ))
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
                let argument = self.interp_inner(*argument, variables.clone(), scenario)?;
                let subformula = self.interp_inner(*subformula, variables.clone(), scenario)?;
                subformula.apply(argument, variables, scenario)
            }
            LambdaExpr::LanguageOfThoughtExpr(x, ExprType::NoVar) => {
                if x.n_arguments() == 0 {
                    x.eval(vec![], scenario)
                } else {
                    Some(Value::Expr(*x))
                }
            }

            LambdaExpr::LanguageOfThoughtExpr(expr, ExprType::BindVarTwoBodies(x, y)) => {
                variables.push(None);
                let x = Value::Function(
                    Box::new(self.interp_inner(*x, variables.clone(), scenario)?),
                    expr.var_type().unwrap().clone(),
                    expr.typ().clone().lhs().unwrap().clone(),
                );
                let y = Value::Function(
                    Box::new(self.interp_inner(*y, variables.clone(), scenario)?),
                    expr.var_type().unwrap().clone(),
                    expr.typ().clone().lhs().unwrap().clone(),
                );
                variables.pop();

                Some(
                    Value::App(
                        Box::new(Value::App(Box::new(Value::Expr(*expr)), Box::new(x))),
                        Box::new(y),
                    )
                    .reduce(variables, scenario)?,
                )
            }
            LambdaExpr::LanguageOfThoughtExpr(_, ExprType::BindVar(_)) => {
                todo!("Binding vars is for later!")
            }
        }
    }
}

#[cfg(test)]
mod test {
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
            let calculated_value = phi.interp(&scenario).unwrap();
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

        let mut phi = RootedLambdaPool::parse("lambda a x lambda a y pa_kind(x)")?;
        let v = phi.interp(&scenario).unwrap();
        println!("{v:?}");

        Ok(())
    }
}
