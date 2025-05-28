#![allow(dead_code)]
use ahash::{HashSet, RandomState};
use chumsky::prelude::*;
use lambda::{Fvar, RootedLambdaPool};
use language::Expr;
use std::{collections::HashMap, fmt::Display, path::Path};

pub type Actor = u16;
pub type Event = u8;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Entity {
    Actor(Actor),
    Event(Event),
}

impl Display for Entity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Entity::Actor(a) => write!(f, "a{a}"),
            Entity::Event(a) => write!(f, "e{a}"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ThetaRoles {
    pub agent: Option<Actor>,
    pub patient: Option<Actor>,
}

pub type PropertyLabel = u32;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Scenario {
    actors: Vec<Actor>,
    thematic_relations: Vec<ThetaRoles>,
    properties: HashMap<PropertyLabel, Vec<Entity>, RandomState>,
    question: Option<RootedLambdaPool<Expr>>,
}

impl Scenario {
    pub fn new(
        actors: Vec<Actor>,
        thematic_relations: Vec<ThetaRoles>,
        properties: HashMap<PropertyLabel, Vec<Entity>, RandomState>,
    ) -> Scenario {
        Scenario {
            actors,
            thematic_relations,
            properties,
            question: None,
        }
    }
    pub fn thematic_relations(&self) -> &[ThetaRoles] {
        &self.thematic_relations
    }

    pub fn properties(&self) -> &HashMap<PropertyLabel, Vec<Entity>, RandomState> {
        &self.properties
    }

    pub fn actors(&self) -> &[Actor] {
        &self.actors
    }

    pub fn question(&self) -> Option<&RootedLambdaPool<Expr>> {
        self.question.as_ref()
    }

    fn events(&self) -> impl Iterator<Item = Event> {
        0..(self.thematic_relations.len() as Event)
    }
}

#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct LabelledScenarios {
    scenarios: Vec<Scenario>,
    sentences: Vec<Vec<String>>,
    lemmas: Vec<String>,
    property_labels: HashMap<String, PropertyLabel, RandomState>,
    actor_labels: HashMap<String, Actor, RandomState>,
    free_variables: HashMap<String, Fvar, RandomState>,
}

impl LabelledScenarios {
    pub fn new(
        scenarios: Vec<Scenario>,
        sentences: Vec<Vec<String>>,
        lemmas: HashSet<String>,
        property_labels: HashMap<String, PropertyLabel, RandomState>,
        actor_labels: HashMap<String, Actor, RandomState>,
        free_variables: HashMap<String, Fvar, RandomState>,
    ) -> Self {
        let mut lemmas: Vec<String> = lemmas.into_iter().collect();
        lemmas.sort();
        LabelledScenarios {
            scenarios,
            sentences,
            lemmas,
            property_labels,
            actor_labels,
            free_variables,
        }
    }

    pub fn iter_scenarios(&self) -> impl Iterator<Item = &Scenario> {
        self.scenarios.iter()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Scenario, &Vec<String>)> {
        self.scenarios.iter().zip(self.sentences.iter())
    }

    pub fn lemmas(&self) -> &[String] {
        &self.lemmas
    }

    pub fn from_file<P: AsRef<Path>>(path: P) -> anyhow::Result<Self> {
        let file_data = std::fs::read_to_string(path).unwrap();
        let parser = scenario::scenario_parser();
        let parse = parser.parse(&file_data).into_result();
        parse.map_err(|x| {
            anyhow::Error::msg(
                x.into_iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join("\n"),
            )
        })?
    }

    pub fn parse(s: &str) -> anyhow::Result<Self> {
        let parser = scenario::scenario_parser();
        let parse = parser.parse(s).into_result();
        parse.map_err(|x| {
            anyhow::Error::msg(
                x.into_iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join("\n"),
            )
        })?
    }
}

pub mod lambda;
pub mod language;
pub use language::{LanguageExpression, LanguageResult, parse_executable};
mod scenario;
