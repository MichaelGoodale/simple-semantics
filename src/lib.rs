pub type Actor = u16;
pub type Event = u8;
pub enum ThetaRole {
    Agent,
    Patient,
}
pub type ThematicRelation = (Actor, Event, ThetaRole);
pub type PropertyLabel = u32;

pub struct Scenario {
    actors: Vec<Actor>,
    events: Vec<Event>,
    thematic_relations: Vec<ThematicRelation>,
    actor_properties: Vec<(PropertyLabel, Vec<Actor>)>,
    event_properties: Vec<(PropertyLabel, Vec<Event>)>,
}

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
