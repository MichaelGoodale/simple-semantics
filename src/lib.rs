#![allow(dead_code)]
use ahash::{HashSet, RandomState};
use chumsky::prelude::*;
use lambda::RootedLambdaPool;
use language::{Expr, LambdaParseError};
use std::{collections::HashMap, fmt::Display};

pub type Actor<'a> = &'a str;
pub type Event = u8;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Entity<'a> {
    Actor(Actor<'a>),
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

#[derive(Debug, Clone, Copy, PartialEq, Default, Eq)]
pub struct ThetaRoles<'a> {
    pub agent: Option<Actor<'a>>,
    pub patient: Option<Actor<'a>>,
}

pub type PropertyLabel<'a> = &'a str;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Scenario<'a> {
    actors: Vec<Actor<'a>>,
    thematic_relations: Vec<ThetaRoles<'a>>,
    properties: HashMap<PropertyLabel<'a>, Vec<Entity<'a>>, RandomState>,
    question: Option<RootedLambdaPool<'a, Expr<'a>>>,
}

impl<'a> Scenario<'a> {
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

    pub fn question_mut(&mut self) -> &mut Option<RootedLambdaPool<'a, Expr<'a>>> {
        &mut self.question
    }

    fn events(&self) -> impl Iterator<Item = Event> {
        0..(self.thematic_relations.len() as Event)
    }
}

#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct LabelledScenarios<'a> {
    scenarios: Vec<Scenario<'a>>,
    sentences: Vec<Vec<&'a str>>,
    lemmas: Vec<&'a str>,
}

impl<'a> LabelledScenarios<'a> {
    pub fn new(
        scenarios: Vec<Scenario<'a>>,
        sentences: Vec<Vec<&'a str>>,
        lemmas: HashSet<&'a str>,
    ) -> Self {
        let mut lemmas: Vec<_> = lemmas.into_iter().collect();
        lemmas.sort();
        LabelledScenarios {
            scenarios,
            sentences,
            lemmas,
        }
    }

    pub fn iter_scenarios_mut(&mut self) -> impl Iterator<Item = &mut Scenario<'a>> {
        self.scenarios.iter_mut()
    }

    pub fn iter_scenarios(&self) -> impl Iterator<Item = &Scenario> {
        self.scenarios.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&mut Scenario<'a>, &mut Vec<&'a str>)> {
        self.scenarios.iter_mut().zip(self.sentences.iter_mut())
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Scenario<'a>, &Vec<&'a str>)> {
        self.scenarios.iter().zip(self.sentences.iter())
    }

    pub fn lemmas(&self) -> &[&'a str] {
        &self.lemmas
    }

    pub fn parse(s: &'a str) -> Result<Self, LambdaParseError> {
        let parser = scenario::scenario_parser();
        let parse = parser.parse(s).into_result();
        parse?
    }
}

pub mod lambda;
pub mod language;
pub use language::{LanguageExpression, LanguageResult, parse_executable};
mod scenario;
