#![allow(dead_code)]
use serde::{Deserialize, Serialize};

pub type Actor = u16;
pub type Event = u8;

#[derive(Serialize, Deserialize, Debug, Clone, Copy, PartialEq, Eq)]
pub enum Entity {
    Actor(Actor),
    Event(Event),
}

#[derive(Serialize, Deserialize, Debug, Clone, Copy)]
pub struct ThetaRoles {
    agent: Option<Actor>,
    patient: Option<Actor>,
}

pub type PropertyLabel = u32;

#[derive(Serialize, Deserialize, Debug)]
pub struct Scenario {
    actors: Vec<Actor>,
    thematic_relations: Vec<ThetaRoles>,
    properties: Vec<(PropertyLabel, Vec<Entity>)>,
}

mod ops;
