use std::fmt::Display;

use crate::lambda::RootedLambdaPool;
use crate::lambda::types::LambdaType;
use crate::{Actor, Entity, Event, PropertyLabel, Scenario};
use lambda_implementation::to_var;

use thiserror;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum BinOp {
    AgentOf,
    PatientOf,
    And,
    Or,
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                BinOp::AgentOf => "AgentOf",
                BinOp::PatientOf => "PatientOf",
                BinOp::And => "&",
                BinOp::Or => "|",
            }
        )
    }
}

impl BinOp {
    fn get_argument_type(&self) -> [&LambdaType; 2] {
        match self {
            BinOp::AgentOf | BinOp::PatientOf => [LambdaType::a(), LambdaType::e()],
            BinOp::And | BinOp::Or => [LambdaType::t(), LambdaType::t()],
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum MonOp<'a> {
    Not,
    Property(PropertyLabel<'a>, ActorOrEvent),
    Tautology,
    Contradiction,
}

impl MonOp<'_> {
    fn get_argument_type(&self) -> &LambdaType {
        match self {
            MonOp::Property(_, ActorOrEvent::Actor) => LambdaType::a(),
            MonOp::Property(_, ActorOrEvent::Event) => LambdaType::e(),
            MonOp::Tautology | MonOp::Contradiction | MonOp::Not => LambdaType::t(),
        }
    }
}

impl<'a> Display for MonOp<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MonOp::Not => write!(f, "~"),
            MonOp::Property(x, ActorOrEvent::Actor) => write!(f, "pa_{x}"),
            MonOp::Property(x, ActorOrEvent::Event) => write!(f, "pe_{x}"),
            MonOp::Tautology => write!(f, "True"),
            MonOp::Contradiction => write!(f, "False"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActorOrEvent {
    Actor,
    Event,
}

impl Display for ActorOrEvent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ActorOrEvent::Actor => write!(f, "a"),
            ActorOrEvent::Event => write!(f, "e"),
        }
    }
}

impl ActorOrEvent {
    fn to_variable(self, n: u32) -> Variable {
        match self {
            ActorOrEvent::Actor => Variable::Actor(n),
            ActorOrEvent::Event => Variable::Event(n),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Constant<'a> {
    Everyone,
    EveryEvent,
    Tautology,
    Contradiction,
    Property(PropertyLabel<'a>, ActorOrEvent),
}

impl Display for Constant<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Constant::Everyone => write!(f, "all_a"),
            Constant::EveryEvent => write!(f, "all_e"),
            Constant::Tautology => write!(f, "True"),
            Constant::Contradiction => write!(f, "False"),
            Constant::Property(x, ActorOrEvent::Actor) => write!(f, "pa_{x}"),
            Constant::Property(x, ActorOrEvent::Event) => write!(f, "pe_{x}"),
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum Variable {
    Actor(u32),
    Event(u32),
}

impl Variable {
    fn to_var_string(self) -> String {
        match self {
            Variable::Actor(a) | Variable::Event(a) => to_var(a as usize, None),
        }
    }

    fn id(&self) -> u32 {
        match self {
            Variable::Actor(a) | Variable::Event(a) => *a,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Quantifier {
    Universal,
    Existential,
}

impl Display for Quantifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Quantifier::Universal => write!(f, "every"),
            Quantifier::Existential => write!(f, "some"),
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Expr<'a> {
    Quantifier {
        quantifier: Quantifier,
        var: Variable,
        restrictor: ExprRef,
        subformula: ExprRef,
    },
    Variable(Variable),
    Actor(Actor<'a>),
    Event(Event),
    Binary(BinOp, ExprRef, ExprRef),
    Unary(MonOp<'a>, ExprRef),
    Constant(Constant<'a>),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct ExprRef(pub u32);

#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct ExprPool<'a>(Vec<Expr<'a>>);

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LanguageExpression<'a> {
    pool: ExprPool<'a>,
    start: ExprRef,
}

impl Display for LanguageExpression<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let x: RootedLambdaPool<Expr> = self.clone().into();
        write!(f, "{x}")
    }
}

impl<'a> LanguageExpression<'a> {
    pub fn run(&self, scenario: &Scenario<'a>) -> Result<LanguageResult<'a>, LanguageTypeError> {
        let mut variables = VariableBuffer::default();
        self.pool.interp(self.start, scenario, &mut variables)
    }

    pub fn parse(s: &'a str) -> Result<LanguageExpression<'a>, LambdaParseError> {
        Ok(RootedLambdaPool::parse(s)?.into_pool()?)
    }

    pub fn new(pool: ExprPool<'a>, start: ExprRef) -> Self {
        LanguageExpression { pool, start }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct VariableBuffer<'a>(Vec<Option<Entity<'a>>>);

impl<'a> VariableBuffer<'a> {
    fn set(&mut self, v: Variable, x: Entity<'a>) {
        let i = v.id() as usize;
        if self.0.len() <= i {
            self.0.resize(i + 1, None);
        }
        self.0[i] = Some(x);
    }

    fn get(&self, v: Variable) -> Option<LanguageResult<'a>> {
        match self.0.get(v.id() as usize) {
            Some(x) => match (v, x) {
                (Variable::Actor(_), Some(Entity::Actor(a))) => Some(LanguageResult::Actor(a)),
                (Variable::Event(_), Some(Entity::Event(e))) => Some(LanguageResult::Event(*e)),
                _ => None,
            },
            None => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LanguageResult<'a> {
    Bool(bool),
    Actor(Actor<'a>),
    Event(Event),
    ActorSet(Vec<Actor<'a>>),
    EventSet(Vec<Event>),
}

impl LanguageResult<'_> {
    fn to_language_result_type(&self) -> LanguageResultType {
        match self {
            LanguageResult::Bool(_) => LanguageResultType::Bool,
            LanguageResult::Actor(_) => LanguageResultType::Actor,
            LanguageResult::Event(_) => LanguageResultType::Event,
            LanguageResult::ActorSet(_) => LanguageResultType::ActorSet,
            LanguageResult::EventSet(_) => LanguageResultType::EventSet,
        }
    }
}

impl Display for LanguageResult<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LanguageResult::Bool(b) => write!(f, "{b}"),
            LanguageResult::Actor(a) => write!(f, "a_{a}"),
            LanguageResult::Event(e) => write!(f, "e_{e}"),
            LanguageResult::ActorSet(items) => {
                write!(
                    f,
                    "{{{}}}",
                    items
                        .iter()
                        .map(|x| format!("a_{x}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            LanguageResult::EventSet(items) => write!(
                f,
                "{{{}}}",
                items
                    .iter()
                    .map(|x| format!("e{x}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LanguageResultType {
    Bool,
    Actor,
    ActorSet,
    Event,
    EventSet,
}

impl Display for LanguageResultType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                LanguageResultType::Bool => "t",
                LanguageResultType::Actor => "a",
                LanguageResultType::ActorSet => "<a,t>",
                LanguageResultType::Event => "e",
                LanguageResultType::EventSet => "<e,t>",
            }
        )
    }
}

#[derive(Error, Debug, PartialEq, Eq)]
pub enum LanguageTypeError {
    #[error("The referenced object does not exist in the current scenario")]
    PresuppositionError,

    #[error("The referenced variable ({0:?}) does not exist in the current scenario")]
    MissingVariable(Variable),

    #[error("Can't convert from {input} to {output}")]
    WrongType {
        input: LanguageResultType,
        output: LanguageResultType,
    },
}

impl TryFrom<LanguageResult<'_>> for Event {
    type Error = LanguageTypeError;

    fn try_from(value: LanguageResult) -> Result<Self, Self::Error> {
        match value {
            LanguageResult::Event(x) => Ok(x),
            _ => Err(LanguageTypeError::WrongType {
                input: value.to_language_result_type(),
                output: LanguageResultType::Event,
            }),
        }
    }
}

impl<'a> TryFrom<LanguageResult<'a>> for Actor<'a> {
    type Error = LanguageTypeError;

    fn try_from(value: LanguageResult<'a>) -> Result<Self, Self::Error> {
        match value {
            LanguageResult::Actor(x) => Ok(x),
            _ => Err(LanguageTypeError::WrongType {
                input: value.to_language_result_type(),
                output: LanguageResultType::Actor,
            }),
        }
    }
}

impl TryFrom<LanguageResult<'_>> for bool {
    type Error = LanguageTypeError;

    fn try_from(value: LanguageResult) -> Result<Self, Self::Error> {
        match value {
            LanguageResult::Bool(x) => Ok(x),
            _ => Err(LanguageTypeError::WrongType {
                input: value.to_language_result_type(),
                output: LanguageResultType::Bool,
            }),
        }
    }
}

impl<'a> TryFrom<LanguageResult<'a>> for Vec<Actor<'a>> {
    type Error = LanguageTypeError;

    fn try_from(value: LanguageResult<'a>) -> Result<Self, Self::Error> {
        match value {
            LanguageResult::ActorSet(x) => Ok(x),
            _ => Err(LanguageTypeError::WrongType {
                input: value.to_language_result_type(),
                output: LanguageResultType::ActorSet,
            }),
        }
    }
}

impl TryFrom<LanguageResult<'_>> for Vec<Event> {
    type Error = LanguageTypeError;

    fn try_from(value: LanguageResult) -> Result<Self, Self::Error> {
        match value {
            LanguageResult::EventSet(x) => Ok(x),
            _ => Err(LanguageTypeError::WrongType {
                input: value.to_language_result_type(),
                output: LanguageResultType::EventSet,
            }),
        }
    }
}

impl<'a> ExprPool<'a> {
    pub fn new() -> ExprPool<'a> {
        ExprPool(vec![])
    }

    pub fn from(x: Vec<Expr<'a>>) -> ExprPool<'a> {
        ExprPool(x)
    }

    fn checked_get(&self, expr: ExprRef) -> Option<&Expr<'a>> {
        self.0.get(expr.0 as usize)
    }

    fn get(&self, expr: ExprRef) -> &Expr<'a> {
        &self.0[expr.0 as usize]
    }

    fn get_mut(&mut self, expr: ExprRef) -> &mut Expr<'a> {
        &mut self.0[expr.0 as usize]
    }

    pub fn add(&mut self, expr: Expr<'a>) -> ExprRef {
        let idx = self.0.len();
        self.0.push(expr);
        ExprRef(idx.try_into().expect("Too many exprs in the pool"))
    }

    fn get_type(&self, expr: ExprRef) -> LanguageResultType {
        match self.get(expr) {
            Expr::Quantifier { .. } => LanguageResultType::Bool,
            Expr::Variable(Variable::Event(_)) => LanguageResultType::Event,
            Expr::Variable(Variable::Actor(_)) => LanguageResultType::Actor,
            Expr::Actor(_) => LanguageResultType::Actor,
            Expr::Event(_) => LanguageResultType::Event,
            Expr::Binary(..) => LanguageResultType::Bool,
            Expr::Unary(..) => LanguageResultType::Bool,
            Expr::Constant(constant) => match constant {
                Constant::Everyone | Constant::Property(_, ActorOrEvent::Actor) => {
                    LanguageResultType::ActorSet
                }
                Constant::EveryEvent | Constant::Property(_, ActorOrEvent::Event) => {
                    LanguageResultType::EventSet
                }
                Constant::Tautology | Constant::Contradiction => LanguageResultType::Bool,
            },
        }
    }

    fn quantification(
        &self,
        quantifier: &Quantifier,
        var: &Variable,
        restrictor: ExprRef,
        subformula: ExprRef,
        scenario: &Scenario,
        variables: &mut VariableBuffer<'a>,
    ) -> Result<LanguageResult<'a>, LanguageTypeError> {
        let mut variables = variables.clone();
        let domain: Vec<Entity> = match self.get_type(restrictor) {
            LanguageResultType::Bool => {
                let mut domain = vec![];
                match var {
                    Variable::Actor(_) => {
                        for e in scenario.actors.iter() {
                            variables.set(*var, Entity::Actor(e));
                            let truth_value_for_e: bool = self
                                .interp(restrictor, scenario, &mut variables)?
                                .try_into()?;
                            if truth_value_for_e {
                                domain.push(Entity::Actor(e))
                            }
                        }
                    }
                    Variable::Event(_) => {
                        for e in scenario.events() {
                            variables.set(*var, Entity::Event(e));
                            let truth_value_for_e: bool = self
                                .interp(restrictor, scenario, &mut variables)?
                                .try_into()?;
                            if truth_value_for_e {
                                domain.push(Entity::Event(e))
                            }
                        }
                    }
                }
                domain
            }
            LanguageResultType::Actor => {
                let e: Actor = self
                    .interp(restrictor, scenario, &mut variables)?
                    .try_into()?;
                vec![Entity::Actor(e)]
            }
            LanguageResultType::ActorSet => {
                let a: Vec<Actor> = self
                    .interp(restrictor, scenario, &mut variables)?
                    .try_into()?;
                a.into_iter().map(Entity::Actor).collect()
            }
            LanguageResultType::Event => {
                let e: Event = self
                    .interp(restrictor, scenario, &mut variables)?
                    .try_into()?;
                vec![Entity::Event(e)]
            }
            LanguageResultType::EventSet => {
                let a: Vec<Event> = self
                    .interp(restrictor, scenario, &mut variables)?
                    .try_into()?;
                a.into_iter().map(Entity::Event).collect()
            }
        };

        if domain.is_empty() {
            return Err(LanguageTypeError::PresuppositionError);
        }

        let mut result = match quantifier {
            Quantifier::Universal => true,
            Quantifier::Existential => false,
        };
        for e in domain {
            variables.set(*var, e);
            let subformula_value: bool = self
                .interp(subformula, scenario, &mut variables)?
                .try_into()?;
            result = match quantifier {
                Quantifier::Universal => subformula_value && result,
                Quantifier::Existential => subformula_value || result,
            };
        }
        Ok(LanguageResult::Bool(result))
    }

    pub fn interp(
        &self,
        expr: ExprRef,
        scenario: &Scenario<'a>,
        variables: &mut VariableBuffer<'a>,
    ) -> Result<LanguageResult<'a>, LanguageTypeError> {
        Ok(match self.get(expr) {
            Expr::Quantifier {
                quantifier,
                var,
                restrictor,
                subformula,
            } => self.quantification(
                quantifier,
                var,
                *restrictor,
                *subformula,
                scenario,
                variables,
            )?,
            Expr::Variable(i) => variables
                .get(*i)
                .ok_or(LanguageTypeError::MissingVariable(*i))?,
            Expr::Actor(a) => LanguageResult::Actor(a),
            Expr::Event(a) => LanguageResult::Event(*a),
            Expr::Binary(bin_op, lhs, rhs) => {
                let lhs = self.interp(*lhs, scenario, variables)?;
                let rhs = self.interp(*rhs, scenario, variables)?;
                match bin_op {
                    BinOp::PatientOf | BinOp::AgentOf => {
                        let a: Actor = lhs.try_into()?;
                        let e: Event = rhs.try_into()?;
                        match bin_op {
                            BinOp::AgentOf => match scenario.thematic_relations[e as usize].agent {
                                Some(x) => LanguageResult::Bool(x == a),
                                None => return Err(LanguageTypeError::PresuppositionError),
                            },
                            BinOp::PatientOf => {
                                match scenario.thematic_relations[e as usize].patient {
                                    Some(x) => LanguageResult::Bool(x == a),
                                    None => return Err(LanguageTypeError::PresuppositionError),
                                }
                            }
                            _ => panic!("impossible because of previous check"),
                        }
                    }
                    BinOp::Or | BinOp::And => {
                        let phi: bool = lhs.try_into()?;
                        let psi: bool = rhs.try_into()?;
                        LanguageResult::Bool(match bin_op {
                            BinOp::And => phi && psi,
                            BinOp::Or => phi || psi,
                            _ => panic!("impossible because of previous check"),
                        })
                    }
                }
            }
            Expr::Constant(constant) => match constant {
                Constant::Everyone => LanguageResult::ActorSet(scenario.actors.clone()),
                Constant::EveryEvent => LanguageResult::EventSet(
                    (0..scenario.thematic_relations.len())
                        .map(|x| x.try_into().unwrap())
                        .collect(),
                ),
                Constant::Tautology => LanguageResult::Bool(true),
                Constant::Contradiction => LanguageResult::Bool(false),
                Constant::Property(p, ActorOrEvent::Actor) => match scenario.properties.get(p) {
                    Some(property_members) => LanguageResult::ActorSet(
                        property_members
                            .iter()
                            .filter_map(|x| match x {
                                Entity::Actor(a) => Some(*a),
                                Entity::Event(_) => None,
                            })
                            .collect(),
                    ),
                    None => LanguageResult::ActorSet(vec![]),
                },
                Constant::Property(p, ActorOrEvent::Event) => match scenario.properties.get(p) {
                    Some(property_members) => LanguageResult::EventSet(
                        property_members
                            .iter()
                            .filter_map(|x| match x {
                                Entity::Actor(_) => None,
                                Entity::Event(e) => Some(*e),
                            })
                            .collect(),
                    ),
                    None => LanguageResult::EventSet(vec![]),
                },
            },
            Expr::Unary(mon_op, arg) => {
                let arg = self.interp(*arg, scenario, variables)?;
                match mon_op {
                    MonOp::Not => LanguageResult::Bool(!TryInto::<bool>::try_into(arg)?),
                    MonOp::Contradiction => LanguageResult::Bool(false),
                    MonOp::Tautology => LanguageResult::Bool(true),
                    MonOp::Property(e, ActorOrEvent::Actor) => {
                        let arg: Actor = arg.try_into()?;
                        match scenario.properties.get(e) {
                            Some(property_members) => {
                                LanguageResult::Bool(property_members.contains(&Entity::Actor(arg)))
                            }
                            None => LanguageResult::Bool(false),
                        }
                    }
                    MonOp::Property(e, ActorOrEvent::Event) => {
                        let arg: Event = arg.try_into()?;
                        match scenario.properties.get(e) {
                            Some(property_members) => {
                                LanguageResult::Bool(property_members.contains(&Entity::Event(arg)))
                            }
                            None => LanguageResult::Bool(false),
                        }
                    }
                }
            }
        })
    }
}

mod parser;
pub use parser::LambdaParseError;
pub use parser::UnprocessedParseTree;
pub use parser::lot_parser;
pub use parser::parse_executable;
use thiserror::Error;

mod lambda_implementation;

#[cfg(feature = "sampling")]
mod mutations;

mod serializations;

#[cfg(test)]
mod tests {
    use crate::ScenarioDataset;
    use std::collections::HashMap;

    use ahash::RandomState;
    use chumsky::{Parser, error::Rich, extra};

    use super::*;
    use crate::ThetaRoles;

    #[test]
    fn agent_of_and_patient_of() -> anyhow::Result<()> {
        let mut variables = VariableBuffer(vec![]);
        let simple_scenario = Scenario {
            question: None,
            actors: vec!["0", "1"],
            thematic_relations: vec![ThetaRoles {
                agent: Some("0"),
                patient: None,
            }],
            properties: HashMap::default(),
        };

        let simple_expr = ExprPool(vec![
            Expr::Actor("0"),
            Expr::Event(0),
            Expr::Binary(BinOp::AgentOf, ExprRef(0), ExprRef(1)),
        ]);

        assert_eq!(
            simple_expr.interp(ExprRef(2), &simple_scenario, &mut variables)?,
            LanguageResult::Bool(true)
        );

        let simple_expr = ExprPool(vec![
            Expr::Actor("0"),
            Expr::Event(0),
            Expr::Binary(BinOp::PatientOf, ExprRef(0), ExprRef(1)),
        ]);
        assert_eq!(
            simple_expr
                .interp(ExprRef(2), &simple_scenario, &mut variables)
                .unwrap_err(),
            LanguageTypeError::PresuppositionError
        );
        Ok(())
    }

    #[test]
    fn quantification() -> anyhow::Result<()> {
        let mut variables = VariableBuffer(vec![]);
        let simple_scenario = Scenario {
            question: None,
            actors: vec!["0", "1"],
            thematic_relations: vec![
                ThetaRoles {
                    agent: Some("0"),
                    patient: Some("0"),
                },
                ThetaRoles {
                    agent: Some("1"),
                    patient: Some("0"),
                },
            ],
            properties: HashMap::default(),
        };

        //For all actors there exists an event such that they are its agent.
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var: Variable::Actor(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Everyone),
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var: Variable::Event(1),
                restrictor: ExprRef(3),
                subformula: ExprRef(4),
            },
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::AgentOf, ExprRef(5), ExprRef(6)),
            Expr::Variable(Variable::Actor(0)),
            Expr::Variable(Variable::Event(1)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables)?,
            LanguageResult::Bool(true)
        );

        //For all actors there exists an event such that they are its patient.
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var: Variable::Actor(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Everyone),
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var: Variable::Event(1),
                restrictor: ExprRef(3),
                subformula: ExprRef(4),
            },
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::PatientOf, ExprRef(5), ExprRef(6)),
            Expr::Variable(Variable::Actor(0)),
            Expr::Variable(Variable::Event(1)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables)?,
            LanguageResult::Bool(false)
        );
        Ok(())
    }

    #[test]
    fn logic() -> anyhow::Result<()> {
        let mut variables = VariableBuffer(vec![]);
        let simple_scenario = Scenario {
            question: None,
            actors: vec!["0", "1"],
            thematic_relations: vec![
                ThetaRoles {
                    agent: Some("0"),
                    patient: Some("0"),
                },
                ThetaRoles {
                    agent: Some("1"),
                    patient: Some("0"),
                },
            ],
            properties: HashMap::default(),
        };

        assert_eq!(
            ExprPool(vec![Expr::Constant(Constant::Contradiction)]).interp(
                ExprRef(0),
                &simple_scenario,
                &mut variables
            )?,
            LanguageResult::Bool(false)
        );

        assert_eq!(
            ExprPool(vec![Expr::Constant(Constant::Tautology)]).interp(
                ExprRef(0),
                &simple_scenario,
                &mut variables
            )?,
            LanguageResult::Bool(true)
        );

        //\neg \bot
        let simple_expr = ExprPool(vec![
            Expr::Unary(MonOp::Not, ExprRef(1)),
            Expr::Constant(Constant::Contradiction),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables)?,
            LanguageResult::Bool(true)
        );

        //\neg \top
        let simple_expr = ExprPool(vec![
            Expr::Unary(MonOp::Not, ExprRef(1)),
            Expr::Constant(Constant::Tautology),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables)?,
            LanguageResult::Bool(false)
        );

        //(\neg \bot) \lor (\bot)
        let simple_expr = ExprPool(vec![
            Expr::Binary(BinOp::Or, ExprRef(1), ExprRef(3)),
            Expr::Unary(MonOp::Not, ExprRef(2)),
            Expr::Constant(Constant::Contradiction),
            Expr::Constant(Constant::Contradiction),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables)?,
            LanguageResult::Bool(true)
        );

        //(\neg \bot) \and (\bot)
        let simple_expr = ExprPool(vec![
            Expr::Binary(BinOp::And, ExprRef(1), ExprRef(3)),
            Expr::Unary(MonOp::Not, ExprRef(2)),
            Expr::Constant(Constant::Contradiction),
            Expr::Constant(Constant::Contradiction),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables)?,
            LanguageResult::Bool(false)
        );

        //For all actors there exists an event such that they are its patient and TOP.
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var: Variable::Actor(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Everyone),
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var: Variable::Event(1),
                restrictor: ExprRef(3),
                subformula: ExprRef(4),
            },
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::And, ExprRef(5), ExprRef(8)),
            Expr::Binary(BinOp::PatientOf, ExprRef(6), ExprRef(7)),
            Expr::Variable(Variable::Actor(0)),
            Expr::Variable(Variable::Event(1)),
            Expr::Constant(Constant::Tautology),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables)?,
            LanguageResult::Bool(false)
        );
        Ok(())
    }

    #[test]
    fn properties() -> anyhow::Result<()> {
        let mut variables = VariableBuffer(vec![]);
        let mut properties: HashMap<_, _, RandomState> = HashMap::default();
        properties.insert("1", vec![Entity::Actor("0"), Entity::Actor("1")]);
        properties.insert("534", vec![Entity::Actor("1")]);
        let simple_scenario = Scenario {
            question: None,
            actors: vec!["0", "1"],
            thematic_relations: vec![
                ThetaRoles {
                    agent: Some("0"),
                    patient: Some("0"),
                },
                ThetaRoles {
                    agent: Some("1"),
                    patient: Some("0"),
                },
            ],
            properties,
        };

        // everyone is of property type one.
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var: Variable::Actor(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Everyone),
            Expr::Unary(MonOp::Property("1", ActorOrEvent::Actor), ExprRef(3)),
            Expr::Variable(Variable::Actor(0)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables)?,
            LanguageResult::Bool(true)
        );
        // someone is of property type 534.
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var: Variable::Actor(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Everyone),
            Expr::Unary(MonOp::Property("534", ActorOrEvent::Actor), ExprRef(3)),
            Expr::Variable(Variable::Actor(0)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables)?,
            LanguageResult::Bool(true)
        );
        Ok(())
    }

    #[test]
    fn complicated_restrictors() -> anyhow::Result<()> {
        let mut variables = VariableBuffer(vec![]);
        let mut properties: HashMap<_, _, RandomState> = HashMap::default();
        properties.insert("534", vec![Entity::Actor("1")]);
        properties.insert("235", vec![Entity::Event(0)]);
        properties.insert("2", vec![Entity::Actor("0")]);
        let simple_scenario = Scenario {
            question: None,
            actors: vec!["0", "1"],
            thematic_relations: vec![ThetaRoles {
                agent: Some("1"),
                patient: Some("0"),
            }],
            properties,
        };

        // all property type 534 objects are agents of a 235-event
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var: Variable::Actor(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Property("534", ActorOrEvent::Actor)),
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var: Variable::Event(1),
                restrictor: ExprRef(3),
                subformula: ExprRef(4),
            },
            Expr::Constant(Constant::Property("235", ActorOrEvent::Event)),
            Expr::Binary(BinOp::AgentOf, ExprRef(5), ExprRef(6)),
            Expr::Variable(Variable::Actor(0)),
            Expr::Variable(Variable::Event(1)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables)?,
            LanguageResult::Bool(true)
        );
        // all property type 2 objects are agents of a 235-event (which is false)
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var: Variable::Actor(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Property("2", ActorOrEvent::Actor)),
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var: Variable::Event(1),
                restrictor: ExprRef(3),
                subformula: ExprRef(4),
            },
            Expr::Constant(Constant::Property("235", ActorOrEvent::Event)),
            Expr::Binary(BinOp::AgentOf, ExprRef(5), ExprRef(6)),
            Expr::Variable(Variable::Actor(0)),
            Expr::Variable(Variable::Event(1)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables)?,
            LanguageResult::Bool(false)
        );

        let mut properties: HashMap<_, _, RandomState> = HashMap::default();
        properties.insert("3", vec![Entity::Actor("1"), Entity::Actor("2")]);
        properties.insert("2", vec![Entity::Actor("1"), Entity::Actor("3")]);
        properties.insert("4", vec![Entity::Event(0)]);
        let simple_scenario = Scenario {
            question: None,
            actors: vec!["0", "1", "2", "3", "4"],
            thematic_relations: vec![ThetaRoles {
                agent: Some("1"),
                patient: Some("0"),
            }],
            properties,
        };
        //All property type 2 and property type 3 actors are an agent of an event
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var: Variable::Actor(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(6),
            },
            Expr::Binary(BinOp::And, ExprRef(2), ExprRef(4)),
            Expr::Unary(MonOp::Property("2", ActorOrEvent::Actor), ExprRef(3)),
            Expr::Variable(Variable::Actor(0)),
            Expr::Unary(MonOp::Property("3", ActorOrEvent::Actor), ExprRef(5)),
            Expr::Variable(Variable::Actor(0)), //5
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var: Variable::Actor(1),
                restrictor: ExprRef(7),
                subformula: ExprRef(8),
            },
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::AgentOf, ExprRef(9), ExprRef(10)),
            Expr::Variable(Variable::Actor(0)),
            Expr::Variable(Variable::Event(1)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables)?,
            LanguageResult::Bool(true)
        );
        //All property type 2 and property type 3 actors are patients of an event
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var: Variable::Actor(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(6),
            },
            Expr::Binary(BinOp::And, ExprRef(2), ExprRef(4)),
            Expr::Unary(MonOp::Property("2", ActorOrEvent::Actor), ExprRef(3)),
            Expr::Variable(Variable::Actor(0)),
            Expr::Unary(MonOp::Property("3", ActorOrEvent::Actor), ExprRef(5)),
            Expr::Variable(Variable::Actor(0)), //5
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var: Variable::Event(1),
                restrictor: ExprRef(7),
                subformula: ExprRef(8),
            },
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::PatientOf, ExprRef(9), ExprRef(10)),
            Expr::Variable(Variable::Actor(0)),
            Expr::Variable(Variable::Event(1)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables)?,
            LanguageResult::Bool(false)
        );
        Ok(())
    }

    #[test]
    fn error_handling() -> anyhow::Result<()> {
        let p = lot_parser::<extra::Err<Rich<_>>>();

        let expr = p
            .parse("some_e(y,pe_1,PatientOf(a_1,y))")
            .unwrap()
            .to_pool()?
            .into_pool()?;

        let a = Scenario {
            question: None,
            actors: vec!["1", "0"],
            thematic_relations: vec![ThetaRoles {
                agent: Some("0"),
                patient: Some("1"),
            }],
            properties: vec![("1", vec![Entity::Event(0)])].into_iter().collect(),
        };

        let b = Scenario {
            question: None,
            actors: vec!["1"],
            thematic_relations: vec![ThetaRoles {
                agent: Some("1"),
                patient: None,
            }],
            properties: vec![("0", vec![Entity::Event(0)])].into_iter().collect(),
        };
        assert_eq!(expr.run(&b), Err(LanguageTypeError::PresuppositionError));
        expr.run(&a)?;

        Ok(())
    }

    #[test]
    fn weird_and_not_behaviour() -> anyhow::Result<()> {
        let scenario = "\"Phil danced\" <John (man), Mary (woman), Susan (woman), Phil (man); {A: Phil (dance)}, {A: Mary (run)}>";

        let labels = ScenarioDataset::parse(scenario)?;

        let a = LanguageExpression::parse("every_e(x,pe_dance,AgentOf(a_Phil,x))")?;
        let b = LanguageExpression::parse("every_e(x,pe_dance,AgentOf(a_Mary,x))")?;
        let c = LanguageExpression::parse(
            "(every_e(x,pe_dance,AgentOf(a_Phil,x)))&~(every_e(x,pe_dance,AgentOf(a_Mary,x)))",
        )?;
        let scenario = labels.iter_scenarios().next().unwrap();
        assert_eq!(a.run(scenario)?, LanguageResult::Bool(true));
        assert_eq!(b.run(scenario)?, LanguageResult::Bool(false));
        assert_eq!(c.run(scenario)?, LanguageResult::Bool(true));

        Ok(())
    }
}
