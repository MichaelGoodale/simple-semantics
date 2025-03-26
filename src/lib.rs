#![allow(dead_code)]
use ahash::RandomState;
use chumsky::prelude::*;
use lambda::Fvar;
use std::{collections::HashMap, fmt::Display, path::Path};

use serde::{Deserialize, Serialize};

pub type Actor = u16;
pub type Event = u8;

#[derive(Serialize, Deserialize, Debug, Clone, Copy, PartialEq, Eq)]
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

#[derive(Serialize, Deserialize, Debug, Clone, Copy, PartialEq, Eq)]
pub struct ThetaRoles {
    pub agent: Option<Actor>,
    pub patient: Option<Actor>,
}

pub type PropertyLabel = u32;

#[derive(Serialize, Deserialize, Debug, Clone, Eq, PartialEq)]
pub struct Scenario {
    actors: Vec<Actor>,
    thematic_relations: Vec<ThetaRoles>,
    properties: HashMap<PropertyLabel, Vec<Entity>, RandomState>,
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
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LabelledScenarios {
    scenarios: Vec<Scenario>,
    property_labels: HashMap<String, PropertyLabel, RandomState>,
    actor_labels: HashMap<String, Actor, RandomState>,
    free_variables: HashMap<String, Fvar, RandomState>,
}

impl LabelledScenarios {
    pub fn new(
        scenarios: Vec<Scenario>,
        property_labels: HashMap<String, PropertyLabel, RandomState>,
        actor_labels: HashMap<String, Actor, RandomState>,
        free_variables: HashMap<String, Fvar, RandomState>,
    ) -> Self {
        LabelledScenarios {
            scenarios,
            property_labels,
            actor_labels,
            free_variables,
        }
    }

    pub fn iter_scenarios(&self) -> impl Iterator<Item = &Scenario> {
        self.scenarios.iter()
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
        })
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
        })
    }
}

mod lambda;
mod language;
pub use language::{parse_executable, LanguageExpression, LanguageResult};
mod scenario;
