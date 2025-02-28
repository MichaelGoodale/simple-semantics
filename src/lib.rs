#![allow(dead_code)]
use ahash::RandomState;
use std::collections::HashMap;

use serde::{Deserialize, Serialize};

pub type Actor = u16;
pub type Event = u8;

#[derive(Serialize, Deserialize, Debug, Clone, Copy, PartialEq, Eq)]
pub enum Entity {
    Actor(Actor),
    Event(Event),
}

#[derive(Serialize, Deserialize, Debug, Clone, Copy, PartialEq, Eq)]
pub struct ThetaRoles {
    agent: Option<Actor>,
    patient: Option<Actor>,
}

pub type PropertyLabel = u32;

#[derive(Serialize, Deserialize, Debug, Clone, Eq, PartialEq)]
pub struct Scenario {
    actors: Vec<Actor>,
    thematic_relations: Vec<ThetaRoles>,
    properties: HashMap<PropertyLabel, Vec<Entity>, RandomState>,
}

pub struct TrainingDataset {
    scenarios: Vec<Scenario>,
    property_labels: HashMap<String, PropertyLabel, RandomState>,
    actor_labels: HashMap<String, Actor, RandomState>,
}

mod language;
mod scenario;
