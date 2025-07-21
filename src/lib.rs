//! # Simple semantics
//! This crate defines a simple language of thought with a lambda calculus and a randomization
//! procedure to learn simple montagovian grammars.
#![warn(missing_docs)]
use ahash::{HashSet, RandomState};
use chumsky::prelude::*;
use lambda::RootedLambdaPool;
use language::{Expr, LambdaParseError};
use std::{collections::HashMap, fmt::Display};
use thiserror::Error;

///The representation of an entity that can receive theta roles (e.g. a human, a cup, a thought).
pub type Actor<'a> = &'a str;
///The representation of an entity that can assign theta roles (e.g. a runnning even, when its raining, etc.)
///They are representated as indices to the relevant [`ThetaRoles`] in a given [`Scenario`].
pub type Event = u8;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
///The union of [`Actor`] and [`Event`]
pub enum Entity<'a> {
    ///See [`Actor`]
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
#[derive(Debug, Clone, Copy, PartialEq, Default, Eq)]
pub struct ThetaRoles<'a> {
    ///The agent of the event.
    pub agent: Option<Actor<'a>>,
    ///The patient of the event.
    pub patient: Option<Actor<'a>>,
}

type PropertyLabel<'a> = &'a str;

///The representation of a scenario. A moment consisting of various events, the present actors and
///any predicates that apply to either.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Scenario<'a> {
    actors: Vec<Actor<'a>>,
    thematic_relations: Vec<ThetaRoles<'a>>,
    properties: HashMap<PropertyLabel<'a>, Vec<Entity<'a>>, RandomState>,
    question: Option<RootedLambdaPool<'a, Expr<'a>>>,
}

impl<'a> Scenario<'a> {
    ///Create a new scenario.
    pub fn new(
        actors: Vec<Actor<'a>>,
        thematic_relations: Vec<ThetaRoles<'a>>,
        properties: HashMap<PropertyLabel<'a>, Vec<Entity<'a>>, RandomState>,
    ) -> Scenario<'a> {
        Scenario {
            actors,
            thematic_relations,
            properties,
            question: None,
        }
    }

    ///Get the representation of all events as a slice of [`ThetaRoles`].
    pub fn thematic_relations(&self) -> &[ThetaRoles] {
        &self.thematic_relations
    }

    ///Get the properties (e.g. what predicates apply) of the entities in a scenario.
    pub fn properties(&self) -> &HashMap<PropertyLabel, Vec<Entity>, RandomState> {
        &self.properties
    }

    ///Get a slice of all [`Actor`]s in the [`Scenario`]
    pub fn actors(&self) -> &[Actor] {
        &self.actors
    }

    ///Get the question associated with a scenario (which may be [`None`] if there is no question).
    ///Questions are representated as [`RootedLambdaPool`] which return a truth value.
    pub fn question(&self) -> Option<&RootedLambdaPool<Expr>> {
        self.question.as_ref()
    }

    ///Get a mutable reference to the question of a scenario.
    ///See [`Scenario::question`]
    pub fn question_mut(&mut self) -> &mut Option<RootedLambdaPool<'a, Expr<'a>>> {
        &mut self.question
    }

    fn events(&self) -> impl Iterator<Item = Event> {
        0..(self.thematic_relations.len() as Event)
    }
}

///A struct defining a dataset of different [`Scenario`]s as well as their associated sentences all
///lemmas in the dataset.
#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct ScenarioDataset<'a> {
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
        lemmas.sort();
        Ok(ScenarioDataset {
            scenarios,
            sentences,
            lemmas,
        })
    }

    ///Is the dataset empty?
    pub fn is_empty(&self) -> bool {
        self.scenarios.is_empty()
    }

    ///The number of scenarios in the [`ScenarioDataset`].
    pub fn len(&self) -> usize {
        self.scenarios.len()
    }

    ///Iterate over all scenarios with a mutable reference.
    pub fn iter_scenarios_mut(&mut self) -> impl Iterator<Item = &mut Scenario<'a>> {
        self.scenarios.iter_mut()
    }

    ///Iterate over all scenarios
    pub fn iter_scenarios(&self) -> impl Iterator<Item = &Scenario> {
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
