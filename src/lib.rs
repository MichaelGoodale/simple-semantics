//! # Simple semantics
//! This crate defines a simple language of thought with a lambda calculus and a randomization
//! procedure to learn simple montagovian grammars.
#![warn(missing_docs)]
use ahash::HashSet;
use chumsky::prelude::*;
use lambda::RootedLambdaPool;
use language::{Expr, LambdaParseError};
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, fmt::Display};
use thiserror::Error;

///The representation of an entity that can receive theta roles (e.g. a human, a cup, a thought).
pub type Actor<'a> = &'a str;
///The representation of an entity that can assign theta roles (e.g. a runnning even, when its raining, etc.)
///They are representated as indices to the relevant [`ThetaRoles`] in a given [`Scenario`].
pub type Event = u8;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
///The union of [`Actor`] and [`Event`]
pub enum Entity<'a> {
    ///See [`Actor`]
    #[serde(borrow)]
    Actor(Actor<'a>),
    ///See [`Event`]
    Event(Event),
}

impl Display for Entity<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Entity::Actor(a) => write!(f, "a_{a}"),
            Entity::Event(a) => write!(f, "e_{a}"),
        }
    }
}

///The representation of the theta roles of a given event.
#[derive(Debug, Clone, Copy, PartialEq, Default, Eq, Hash, Serialize, Deserialize)]
pub struct ThetaRoles<'a> {
    ///The agent of the event.
    #[serde(borrow)]
    pub agent: Option<Actor<'a>>,
    ///The patient of the event.
    pub patient: Option<Actor<'a>>,
}

type PropertyLabel<'a> = &'a str;

///The representation of a scenario. A moment consisting of various events, the present actors and
///any predicates that apply to either.
#[derive(Debug, Clone, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Scenario<'a> {
    #[serde(borrow)]
    actors: Vec<Actor<'a>>,
    thematic_relations: Vec<ThetaRoles<'a>>,
    properties: BTreeMap<PropertyLabel<'a>, Vec<Entity<'a>>>,
    question: Vec<RootedLambdaPool<'a, Expr<'a>>>,
}

impl<'a> Scenario<'a> {
    ///Create a new scenario.
    #[must_use]
    pub fn new(
        actors: Vec<Actor<'a>>,
        thematic_relations: Vec<ThetaRoles<'a>>,
        properties: BTreeMap<PropertyLabel<'a>, Vec<Entity<'a>>>,
    ) -> Scenario<'a> {
        Scenario {
            actors,
            thematic_relations,
            properties,
            question: vec![],
        }
    }

    ///Get the representation of all events as a slice of [`ThetaRoles`].
    #[must_use]
    pub fn thematic_relations(&self) -> &[ThetaRoles<'a>] {
        &self.thematic_relations
    }

    ///Get the properties (e.g. what predicates apply) of the entities in a scenario.
    #[must_use]
    pub fn properties(&self) -> &BTreeMap<PropertyLabel<'a>, Vec<Entity<'a>>> {
        &self.properties
    }

    ///Get a slice of all [`Actor`]s in the [`Scenario`]
    #[must_use]
    pub fn actors(&self) -> &[Actor<'_>] {
        &self.actors
    }

    ///Get the questions associated with a scenario (which may be empty if there are no questions).
    ///Questions are representated as [`RootedLambdaPool`] which return a truth value.
    #[must_use]
    pub fn questions(&self) -> &[RootedLambdaPool<'a, Expr<'a>>] {
        &self.question
    }

    ///Get a mutable reference to the questions of a scenario.
    ///See [`Scenario::questions`]
    pub fn question_mut(&mut self) -> &mut Vec<RootedLambdaPool<'a, Expr<'a>>> {
        &mut self.question
    }

    fn events(&self) -> impl Iterator<Item = Event> {
        0..(self.thematic_relations.len() as Event)
    }
}

///A struct defining a dataset of different [`Scenario`]s as well as their associated sentences all
///lemmas in the dataset.
#[derive(Debug, Default, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct ScenarioDataset<'a> {
    #[serde(borrow)]
    scenarios: Vec<Scenario<'a>>,
    sentences: Vec<Vec<&'a str>>,
    lemmas: Vec<&'a str>,
}

///Error for creating a dataset without equal sentences and scenarios.
#[derive(Debug, Default, Clone, Eq, PartialEq, Error)]
pub struct DatasetError {}

impl Display for DatasetError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Scenario and sentences not of equal length!")
    }
}

impl<'a> ScenarioDataset<'a> {
    ///Create a new [`ScenarioDataset`]
    pub fn new(
        scenarios: Vec<Scenario<'a>>,
        sentences: Vec<Vec<&'a str>>,
        lemmas: HashSet<&'a str>,
    ) -> Result<Self, DatasetError> {
        if scenarios.len() != sentences.len() {
            return Err(DatasetError {});
        }

        let mut lemmas: Vec<_> = lemmas.into_iter().collect();
        lemmas.sort_unstable();
        Ok(ScenarioDataset {
            scenarios,
            sentences,
            lemmas,
        })
    }

    ///Is the dataset empty?
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.scenarios.is_empty()
    }

    ///The number of scenarios in the [`ScenarioDataset`].
    #[must_use]
    pub fn len(&self) -> usize {
        self.scenarios.len()
    }

    ///Iterate over all scenarios with a mutable reference.
    pub fn iter_scenarios_mut(&mut self) -> impl Iterator<Item = &mut Scenario<'a>> {
        self.scenarios.iter_mut()
    }

    ///Iterate over all scenarios
    pub fn iter_scenarios(&self) -> impl Iterator<Item = &Scenario<'a>> {
        self.scenarios.iter()
    }

    ///Iterate over all scenarios and sentences with a mutable reference.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&mut Scenario<'a>, &mut Vec<&'a str>)> {
        self.scenarios.iter_mut().zip(self.sentences.iter_mut())
    }

    ///Iterate over all scenarios and sentences
    pub fn iter(&self) -> impl Iterator<Item = (&Scenario<'a>, &Vec<&'a str>)> {
        self.scenarios.iter().zip(self.sentences.iter())
    }

    ///Get the available lemmas of a dataset.
    #[must_use]
    pub fn lemmas(&self) -> &[&'a str] {
        &self.lemmas
    }

    ///Parse a list of sentences and scenarios and return the dataset.
    pub fn parse(s: &'a str) -> Result<Self, LambdaParseError> {
        let parser = scenario::scenario_parser();
        let parse = parser.parse(s).into_result();
        parse?
    }
}

pub mod lambda;
pub mod language;
mod utils;
pub use language::{LanguageExpression, LanguageResult, parse_executable};
mod scenario;
