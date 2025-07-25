//! Defines the core language of thought of the model and a simple virtual machine.

use std::fmt::Display;

#[cfg(not(target_arch = "wasm32"))]
use std::time::{Duration, Instant};

use crate::lambda::RootedLambdaPool;
use crate::lambda::types::LambdaType;
use crate::{Actor, Entity, Event, PropertyLabel, Scenario};

use thiserror;

///All binary operations
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum BinOp {
    ///<a,<e,t>> function that returns whether the first argument is the agent of the second
    ///argument.
    AgentOf,
    ///<a,<e,t>> function that returns whether the first argument is the patient of the second
    ///argument.
    PatientOf,
    ///Logical AND
    And,
    ///Logical OR
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

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
///All unary operations
pub enum MonOp<'a> {
    ///Logical not
    Not,
    ///Returns whether an actor or event is a member of a predicate defined by the label.
    Property(PropertyLabel<'a>, ActorOrEvent),
}

impl MonOp<'_> {
    fn get_argument_type(&self) -> &LambdaType {
        match self {
            MonOp::Property(_, ActorOrEvent::Actor) => LambdaType::a(),
            MonOp::Property(_, ActorOrEvent::Event) => LambdaType::e(),
            MonOp::Not => LambdaType::t(),
        }
    }
}

impl<'a> Display for MonOp<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MonOp::Not => write!(f, "~"),
            MonOp::Property(x, ActorOrEvent::Actor) => write!(f, "pa_{x}"),
            MonOp::Property(x, ActorOrEvent::Event) => write!(f, "pe_{x}"),
        }
    }
}

///Whether something refers to an actor or event.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(missing_docs)]
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

impl From<ActorOrEvent> for LambdaType {
    fn from(value: ActorOrEvent) -> Self {
        match value {
            ActorOrEvent::Actor => LambdaType::A,
            ActorOrEvent::Event => LambdaType::E,
        }
    }
}

///Any valid constant in the language.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Constant<'a> {
    ///The set of all actors in the [`Scenario`].
    Everyone,
    ///The set of all events in the [`Scenario`].
    EveryEvent,
    ///Truth
    Tautology,
    ///Falsity
    Contradiction,
    ///Any predicate as a set
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

///The ID of a given variable bound by quantification
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum Variable {
    ///The variable is over actors.
    Actor(u32),
    ///The variable is over events.
    Event(u32),
}

impl Variable {
    fn id(&self) -> u32 {
        match self {
            Variable::Actor(a) | Variable::Event(a) => *a,
        }
    }

    fn as_lambda_type(&self) -> &'static LambdaType {
        match self {
            Variable::Actor(_) => LambdaType::a(),
            Variable::Event(_) => LambdaType::e(),
        }
    }
}

///An enum which represents all possible quantifiers in the language.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum Quantifier {
    ///Universal Quantification
    Universal,
    ///Existential quantification
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

///The basic expression type of the language of thought.
///Note that it *does not* include free variables or any of the machinery of the lambda calculus
///which is handled elsewhere.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum Expr<'a> {
    ///A quantified expression. Variables are implemented with DeBruijn indices.
    Quantifier {
        ///What kind of quantifier
        quantifier: Quantifier,
        ///The type of bound variable
        var_type: ActorOrEvent,
        ///An expression defining the restrictor of the quantifier.
        restrictor: ExprRef,
        ///An expression defining the subformula of the quantifier.
        subformula: ExprRef,
    },
    ///See [`Variable`]
    Variable(Variable),
    ///See [`Actor`]. Written `a_NAME`
    Actor(Actor<'a>),
    ///See [`Event`]. Written `e_N` where `N` is an integer.
    Event(Event),
    ///Any binary function.
    Binary(BinOp, ExprRef, ExprRef),
    ///Any unary function.
    Unary(MonOp<'a>, ExprRef),
    ///All constants.
    Constant(Constant<'a>),
}

///An index for a specific [`Expr`] in a [`LanguageExpression`]
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct ExprRef(pub u32);

///An arena allocated tree which represents an expression in the language of thought built out of
///[`Expr`].
#[derive(Debug, Clone, Default, Eq, PartialEq, Hash)]
pub(crate) struct ExprPool<'a>(Vec<Expr<'a>>);

///An expression pool with a defined root.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
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

#[derive(Debug, Clone, Default, Copy, Eq, PartialEq, PartialOrd, Ord)]
///A configuration struct to limit the time of execution of a given language expression
pub struct ExecutionConfig {
    max_steps: Option<usize>,
    #[cfg(not(target_arch = "wasm32"))]
    timeout: Option<Duration>,
}

impl ExecutionConfig {
    ///Create a new [`ExecutionConfig`]
    pub const fn new(
        max_steps: Option<usize>,
        #[cfg(not(target_arch = "wasm32"))] timeout: Option<Duration>,
    ) -> Self {
        ExecutionConfig {
            max_steps,
            #[cfg(not(target_arch = "wasm32"))]
            timeout,
        }
    }

    ///Set max_steps on a config
    pub const fn with_max_steps(mut self, max_steps: usize) -> Self {
        self.max_steps = Some(max_steps);
        self
    }

    ///Set max_duration on a config
    #[cfg(not(target_arch = "wasm32"))]
    pub const fn with_timeout(mut self, time_out: Duration) -> Self {
        self.timeout = Some(time_out);
        self
    }
}

impl<'a> LanguageExpression<'a> {
    ///Run a [`LanguageExpression`] in the language of thought and return the [`LanguageResult`]
    pub fn run(
        &self,
        scenario: &Scenario<'a>,
        config: Option<ExecutionConfig>,
    ) -> Result<LanguageResult<'a>, LanguageTypeError> {
        let mut variables = VariableBuffer::default();
        Execution {
            pool: &self.pool,
            n_steps: 0,

            #[cfg(not(target_arch = "wasm32"))]
            start: Instant::now(),

            config: &config.unwrap_or_default(),
            quantifier_depth: 0,
        }
        .interp(self.start, scenario, &mut variables)
    }

    ///Parse a given language of thought expression and return the [`LanguageExpression`]. This
    ///does not support tools from the lambda calculus, see [`RootedLambdaPool`].
    pub fn parse(s: &'a str) -> Result<LanguageExpression<'a>, LambdaParseError> {
        Ok(RootedLambdaPool::parse(s)?.into_pool()?)
    }

    #[allow(dead_code)]
    ///Create a `LanguageExpression` out of a [`ExprRef`] and a [`ExprPool`]
    pub(crate) fn new(pool: ExprPool<'a>, start: ExprRef) -> Self {
        LanguageExpression { pool, start }
    }
}

struct Execution<'a, 'b> {
    pool: &'b ExprPool<'a>,
    n_steps: usize,
    #[cfg(not(target_arch = "wasm32"))]
    start: Instant,
    config: &'b ExecutionConfig,

    quantifier_depth: usize,
}

impl Execution<'_, '_> {
    fn check_if_good_to_continue(&mut self) -> Result<(), LanguageTypeError> {
        if let Some(max_steps) = self.config.max_steps
            && self.n_steps > max_steps
        {
            return Err(LanguageTypeError::TooManySteps(max_steps));
        }

        #[cfg(not(target_arch = "wasm32"))]
        if let Some(max_time) = self.config.timeout
            && self.start.elapsed() > max_time
        {
            return Err(LanguageTypeError::TimeOut);
        }

        self.n_steps += 1;
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Hash)]
struct VariableBuffer<'a>(Vec<Option<Entity<'a>>>);

impl<'a> VariableBuffer<'a> {
    fn set(&mut self, i: usize, x: Entity<'a>) {
        if self.0.len() <= i {
            self.0.resize(i + 1, None);
        }
        self.0[i] = Some(x);
    }

    fn get(&self, v: Variable, quantifier_depth: usize) -> Option<LanguageResult<'a>> {
        let pos = (quantifier_depth).checked_sub(v.id() as usize + 1)?;
        match self.0.get(pos) {
            Some(x) => match (v, x) {
                (Variable::Actor(_), Some(Entity::Actor(a))) => Some(LanguageResult::Actor(a)),
                (Variable::Event(_), Some(Entity::Event(e))) => Some(LanguageResult::Event(*e)),
                _ => None,
            },
            None => None,
        }
    }
}

///The result of running a [`LanguageExpression`], see [`LanguageExpression::run`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[allow(missing_docs)]
pub enum LanguageResult<'a> {
    Bool(bool),
    Actor(Actor<'a>),
    Event(Event),
    ///A set of actors (represented as a vector).
    ActorSet(Vec<Actor<'a>>),
    ///A set of events (represented as a vector).
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

///The basic atomic types of the LOT. See [`LanguageResult`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[allow(missing_docs)]
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

///Possible errors that can be generated when running a [`LanguageExpression`]
#[derive(Error, Debug, PartialEq, Eq)]
pub enum LanguageTypeError {
    ///A presupposition error in the semantics; occurs when a non-existent entity is referenced.
    #[error("The referenced object does not exist in the current scenario")]
    PresuppositionError,

    ///A variable that is not bound that was used.
    #[error("The referenced variable ({0:?}) does not exist in the current scenario")]
    MissingVariable(Variable),

    ///A type conversion which is violated.
    #[error("Can't convert from {input} to {output}")]
    WrongType {
        ///The input type of the conversion
        input: LanguageResultType,
        ///The output type of the conversion
        output: LanguageResultType,
    },

    ///The execution ran out of steps
    #[error("The execution took more than {0} steps")]
    TooManySteps(usize),

    ///The execution ran out of time (unavailable on wasm).
    #[error("The execution ran out of time")]
    TimeOut,
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

impl<'a> From<Vec<Expr<'a>>> for ExprPool<'a> {
    fn from(value: Vec<Expr<'a>>) -> Self {
        ExprPool(value)
    }
}

impl<'a> ExprPool<'a> {
    fn get(&self, expr: ExprRef) -> &Expr<'a> {
        &self.0[expr.0 as usize]
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
}

impl<'a, 'b> Execution<'a, 'b> {
    fn quantification(
        &mut self,
        quantifier: &Quantifier,
        var_type: &ActorOrEvent,
        restrictor: ExprRef,
        subformula: ExprRef,
        scenario: &Scenario<'a>,
        variables: &mut VariableBuffer<'a>,
    ) -> Result<LanguageResult<'a>, LanguageTypeError> {
        self.quantifier_depth += 1;
        let mut variables = variables.clone();
        let domain: Vec<Entity> = match self.pool.get_type(restrictor) {
            LanguageResultType::Bool => {
                let mut domain = vec![];
                match var_type {
                    ActorOrEvent::Actor => {
                        for e in scenario.actors.iter() {
                            variables.set(self.quantifier_depth - 1, Entity::Actor(e));
                            let truth_value_for_e: bool = self
                                .interp(restrictor, scenario, &mut variables)?
                                .try_into()?;
                            if truth_value_for_e {
                                domain.push(Entity::Actor(e))
                            }
                        }
                    }
                    ActorOrEvent::Event => {
                        for e in scenario.events() {
                            variables.set(self.quantifier_depth - 1, Entity::Event(e));
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
            variables.set(self.quantifier_depth - 1, e);
            let subformula_value: bool = self
                .interp(subformula, scenario, &mut variables)?
                .try_into()?;
            result = match quantifier {
                Quantifier::Universal => subformula_value && result,
                Quantifier::Existential => subformula_value || result,
            };
        }
        self.quantifier_depth -= 1;
        Ok(LanguageResult::Bool(result))
    }

    fn interp(
        &mut self,
        expr: ExprRef,
        scenario: &Scenario<'a>,
        variables: &mut VariableBuffer<'a>,
    ) -> Result<LanguageResult<'a>, LanguageTypeError> {
        self.check_if_good_to_continue()?;
        Ok(match self.pool.get(expr) {
            Expr::Quantifier {
                quantifier,
                var_type,
                restrictor,
                subformula,
            } => self.quantification(
                quantifier,
                var_type,
                *restrictor,
                *subformula,
                scenario,
                variables,
            )?,
            Expr::Variable(i) => variables
                .get(*i, self.quantifier_depth)
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
pub use parser::parse_executable;
use thiserror::Error;

mod lambda_implementation;

#[cfg(feature = "sampling")]
mod mutations;

#[cfg(feature = "sampling")]
pub use mutations::{LambdaEnumerator, LambdaSampler, PossibleExpressions, TypeAgnosticSampler};

mod serializations;

#[cfg(test)]
mod tests {
    use crate::ScenarioDataset;
    use std::collections::HashMap;

    use ahash::RandomState;

    use super::*;
    use crate::ThetaRoles;

    #[test]
    fn agent_of_and_patient_of() -> anyhow::Result<()> {
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

        let expr = LanguageExpression {
            pool: simple_expr,
            start: ExprRef(2),
        };
        assert_eq!(
            expr.run(&simple_scenario, None)?,
            LanguageResult::Bool(true)
        );

        let simple_expr = ExprPool(vec![
            Expr::Actor("0"),
            Expr::Event(0),
            Expr::Binary(BinOp::PatientOf, ExprRef(0), ExprRef(1)),
        ]);

        let expr = LanguageExpression {
            pool: simple_expr,
            start: ExprRef(2),
        };
        assert_eq!(
            expr.run(&simple_scenario, None).unwrap_err(),
            LanguageTypeError::PresuppositionError
        );
        Ok(())
    }

    #[test]
    fn quantification() -> anyhow::Result<()> {
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
                var_type: ActorOrEvent::Actor,
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Everyone),
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var_type: ActorOrEvent::Event,
                restrictor: ExprRef(3),
                subformula: ExprRef(4),
            },
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::AgentOf, ExprRef(5), ExprRef(6)),
            Expr::Variable(Variable::Actor(1)),
            Expr::Variable(Variable::Event(0)),
        ]);

        let expr = LanguageExpression {
            pool: simple_expr,
            start: ExprRef(0),
        };
        assert_eq!(
            expr.run(&simple_scenario, None)?,
            LanguageResult::Bool(true)
        );

        //For all actors there exists an event such that they are its patient.
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var_type: ActorOrEvent::Actor,
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Everyone),
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var_type: ActorOrEvent::Event,
                restrictor: ExprRef(3),
                subformula: ExprRef(4),
            },
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::PatientOf, ExprRef(5), ExprRef(6)),
            Expr::Variable(Variable::Actor(1)),
            Expr::Variable(Variable::Event(0)),
        ]);
        let expr = LanguageExpression {
            pool: simple_expr,
            start: ExprRef(0),
        };
        assert_eq!(
            expr.run(&simple_scenario, None)?,
            LanguageResult::Bool(false)
        );
        Ok(())
    }

    #[test]
    fn logic() -> anyhow::Result<()> {
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
            LanguageExpression {
                pool: ExprPool(vec![Expr::Constant(Constant::Contradiction)]),
                start: ExprRef(0)
            }
            .run(&simple_scenario, None)?,
            LanguageResult::Bool(false)
        );

        assert_eq!(
            LanguageExpression {
                pool: ExprPool(vec![Expr::Constant(Constant::Tautology)]),
                start: ExprRef(0)
            }
            .run(&simple_scenario, None)?,
            LanguageResult::Bool(true)
        );

        //\neg \bot
        let simple_expr = ExprPool(vec![
            Expr::Unary(MonOp::Not, ExprRef(1)),
            Expr::Constant(Constant::Contradiction),
        ]);
        let expr = LanguageExpression {
            pool: simple_expr,
            start: ExprRef(0),
        };
        assert_eq!(
            expr.run(&simple_scenario, None)?,
            LanguageResult::Bool(true)
        );

        //\neg \top
        let simple_expr = ExprPool(vec![
            Expr::Unary(MonOp::Not, ExprRef(1)),
            Expr::Constant(Constant::Tautology),
        ]);
        let expr = LanguageExpression {
            pool: simple_expr,
            start: ExprRef(0),
        };
        assert_eq!(
            expr.run(&simple_scenario, None)?,
            LanguageResult::Bool(false)
        );

        //(\neg \bot) \lor (\bot)
        let simple_expr = ExprPool(vec![
            Expr::Binary(BinOp::Or, ExprRef(1), ExprRef(3)),
            Expr::Unary(MonOp::Not, ExprRef(2)),
            Expr::Constant(Constant::Contradiction),
            Expr::Constant(Constant::Contradiction),
        ]);
        let expr = LanguageExpression {
            pool: simple_expr,
            start: ExprRef(0),
        };
        assert_eq!(
            expr.run(&simple_scenario, None)?,
            LanguageResult::Bool(true)
        );

        //(\neg \bot) \and (\bot)
        let simple_expr = ExprPool(vec![
            Expr::Binary(BinOp::And, ExprRef(1), ExprRef(3)),
            Expr::Unary(MonOp::Not, ExprRef(2)),
            Expr::Constant(Constant::Contradiction),
            Expr::Constant(Constant::Contradiction),
        ]);
        let expr = LanguageExpression {
            pool: simple_expr,
            start: ExprRef(0),
        };
        assert_eq!(
            expr.run(&simple_scenario, None)?,
            LanguageResult::Bool(false)
        );

        //For all actors there exists an event such that they are its patient and TOP.
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var_type: ActorOrEvent::Actor,
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Everyone),
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var_type: ActorOrEvent::Event,
                restrictor: ExprRef(3),
                subformula: ExprRef(4),
            },
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::And, ExprRef(5), ExprRef(8)),
            Expr::Binary(BinOp::PatientOf, ExprRef(6), ExprRef(7)),
            Expr::Variable(Variable::Actor(1)),
            Expr::Variable(Variable::Event(0)),
            Expr::Constant(Constant::Tautology),
        ]);
        let expr = LanguageExpression {
            pool: simple_expr,
            start: ExprRef(0),
        };
        assert_eq!(
            expr.run(&simple_scenario, None)?,
            LanguageResult::Bool(false)
        );
        Ok(())
    }

    #[test]
    fn properties() -> anyhow::Result<()> {
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
                var_type: ActorOrEvent::Actor,
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Everyone),
            Expr::Unary(MonOp::Property("1", ActorOrEvent::Actor), ExprRef(3)),
            Expr::Variable(Variable::Actor(0)),
        ]);
        let expr = LanguageExpression {
            pool: simple_expr,
            start: ExprRef(0),
        };
        assert_eq!(
            expr.run(&simple_scenario, None)?,
            LanguageResult::Bool(true)
        );
        // someone is of property type 534.
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var_type: ActorOrEvent::Actor,
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Everyone),
            Expr::Unary(MonOp::Property("534", ActorOrEvent::Actor), ExprRef(3)),
            Expr::Variable(Variable::Actor(0)),
        ]);
        let expr = LanguageExpression {
            pool: simple_expr,
            start: ExprRef(0),
        };
        assert_eq!(
            expr.run(&simple_scenario, None)?,
            LanguageResult::Bool(true)
        );
        Ok(())
    }

    #[test]
    fn complicated_restrictors() -> anyhow::Result<()> {
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
                var_type: ActorOrEvent::Actor,
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Property("534", ActorOrEvent::Actor)),
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var_type: ActorOrEvent::Event,
                restrictor: ExprRef(3),
                subformula: ExprRef(4),
            },
            Expr::Constant(Constant::Property("235", ActorOrEvent::Event)),
            Expr::Binary(BinOp::AgentOf, ExprRef(5), ExprRef(6)),
            Expr::Variable(Variable::Actor(1)),
            Expr::Variable(Variable::Event(0)),
        ]);

        let expr = LanguageExpression {
            pool: simple_expr,
            start: ExprRef(0),
        };
        assert_eq!(
            expr.run(&simple_scenario, None)?,
            LanguageResult::Bool(true)
        );
        // all property type 2 objects are agents of a 235-event (which is false)
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var_type: ActorOrEvent::Actor,
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Property("2", ActorOrEvent::Actor)),
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var_type: ActorOrEvent::Event,
                restrictor: ExprRef(3),
                subformula: ExprRef(4),
            },
            Expr::Constant(Constant::Property("235", ActorOrEvent::Event)),
            Expr::Binary(BinOp::AgentOf, ExprRef(5), ExprRef(6)),
            Expr::Variable(Variable::Actor(1)),
            Expr::Variable(Variable::Event(0)),
        ]);
        let expr = LanguageExpression {
            pool: simple_expr,
            start: ExprRef(0),
        };
        assert_eq!(
            expr.run(&simple_scenario, None)?,
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
                var_type: ActorOrEvent::Actor,
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
                var_type: ActorOrEvent::Actor,
                restrictor: ExprRef(7),
                subformula: ExprRef(8),
            },
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::AgentOf, ExprRef(9), ExprRef(10)),
            Expr::Variable(Variable::Actor(1)),
            Expr::Variable(Variable::Event(0)),
        ]);
        let expr = LanguageExpression {
            pool: simple_expr,
            start: ExprRef(0),
        };
        assert_eq!(
            expr.run(&simple_scenario, None)?,
            LanguageResult::Bool(true)
        );
        //All property type 2 and property type 3 actors are patients of an event
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var_type: ActorOrEvent::Actor,
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
                var_type: ActorOrEvent::Event,
                restrictor: ExprRef(7),
                subformula: ExprRef(8),
            },
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::PatientOf, ExprRef(9), ExprRef(10)),
            Expr::Variable(Variable::Actor(1)),
            Expr::Variable(Variable::Event(0)),
        ]);
        let expr = LanguageExpression {
            pool: simple_expr,
            start: ExprRef(0),
        };
        assert_eq!(
            expr.run(&simple_scenario, None)?,
            LanguageResult::Bool(false)
        );
        Ok(())
    }

    #[test]
    fn error_handling() -> anyhow::Result<()> {
        let expr = parse_executable("some_e(y,pe_1,PatientOf(a_1,y))")?;

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
        assert_eq!(
            expr.run(&b, None),
            Err(LanguageTypeError::PresuppositionError)
        );
        expr.run(&a, None)?;

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
        assert_eq!(a.run(scenario, None)?, LanguageResult::Bool(true));
        assert_eq!(b.run(scenario, None)?, LanguageResult::Bool(false));
        assert_eq!(c.run(scenario, None)?, LanguageResult::Bool(true));

        Ok(())
    }
}
