use ahash::RandomState;
use chumsky::prelude::*;
use std::collections::HashMap;

use crate::{Actor, Entity, Event, PropertyLabel, Scenario, ThetaRoles};

fn scenario_parser<'a>() -> impl Parser<'a, &'a str, Scenario> {
    let properties = text::int::<&str, _>(10)
        .map(|n| n.parse().unwrap())
        .padded()
        .separated_by(just(','))
        .collect::<Vec<PropertyLabel>>()
        .delimited_by(just('('), just(')'));

    let actor = text::int(10)
        .padded()
        .map(|n: &str| n.parse().unwrap())
        .then(properties.or_not());

    let actors = actor
        .map(|(a, p)| {
            let actors: Vec<Actor> = vec![a];
            let mut properties: HashMap<PropertyLabel, Vec<Entity>, RandomState> =
                HashMap::default();
            if let Some(property_labels) = p {
                for property in property_labels {
                    properties.insert(property, vec![Entity::Actor(a)]);
                }
            }
            (actors, properties)
        })
        .foldl(
            just(',').ignore_then(actor).repeated(),
            |(mut actors, mut properties), (actor, actor_props)| {
                actors.push(actor);

                if let Some(property_labels) = actor_props {
                    for property in property_labels {
                        properties
                            .entry(property)
                            .and_modify(|x| x.push(Entity::Actor(actor)))
                            .or_insert(vec![Entity::Actor(actor)]);
                    }
                }

                (actors, properties)
            },
        );

    let theta_role = |c: char| {
        just(c)
            .ignore_then(text::int::<&str, _>(10))
            .map(|n| n.parse::<Actor>().unwrap())
            .padded()
    };

    let event = choice((
        theta_role('A')
            .then_ignore(just(','))
            .then(theta_role('P'))
            .map(|(a, p)| ThetaRoles {
                agent: Some(a),
                patient: Some(p),
            }),
        theta_role('P')
            .then_ignore(just(','))
            .then(theta_role('A'))
            .map(|(p, a)| ThetaRoles {
                agent: Some(a),
                patient: Some(p),
            }),
        theta_role('P').map(|n| ThetaRoles {
            agent: None,
            patient: Some(n),
        }),
        theta_role('A').map(|n| ThetaRoles {
            agent: Some(n),
            patient: None,
        }),
        empty().map(|_| ThetaRoles {
            agent: None,
            patient: None,
        }),
    ))
    .then(properties.or_not())
    .delimited_by(just('{'), just('}'));

    let events = event
        .or_not()
        .map(|event_data| {
            let mut properties: HashMap<PropertyLabel, Vec<Entity>, RandomState> =
                HashMap::default();

            let events = match event_data {
                Some((e, None)) => {
                    vec![e]
                }
                Some((e, Some(p))) => {
                    for property_label in p {
                        properties.insert(property_label, vec![Entity::Event(0)]);
                    }

                    vec![e]
                }
                None => vec![],
            };

            (events, properties)
        })
        .foldl(
            just(',').ignore_then(event).repeated().enumerate(),
            |(mut events, mut properties), (i, (event, event_props))| {
                events.push(event);
                if let Some(event_props) = event_props {
                    for property_label in event_props {
                        properties
                            .entry(property_label)
                            .and_modify(|x| x.push(Entity::Event((i + 1) as Event)))
                            .or_insert(vec![Entity::Event((i + 1) as Event)]);
                    }
                }
                (events, properties)
            },
        );

    just('<')
        .ignore_then(actors)
        .then((just(';')).ignore_then(events).or_not())
        .then_ignore(just('>'))
        .padded()
        .then_ignore(end())
        .map(|((actors, mut actor_props), events)| {
            let (events, event_props) =
                events.unwrap_or_else(|| (Vec::default(), HashMap::default()));

            for (k, mut v) in event_props.into_iter() {
                actor_props
                    .entry(k)
                    .and_modify(|value| value.append(&mut v))
                    .or_insert(v);
            }

            Scenario {
                actors,
                thematic_relations: events,
                properties: actor_props,
            }
        })
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse_scenario() -> anyhow::Result<()> {
        let scenario = Scenario {
            actors: vec![3],
            thematic_relations: vec![],
            properties: HashMap::default(),
        };

        assert_eq!(scenario, scenario_parser().parse("<3>").unwrap());
        assert_eq!(scenario, scenario_parser().parse("<3;>").unwrap());

        let scenario = Scenario {
            actors: vec![3],
            thematic_relations: vec![ThetaRoles {
                agent: None,
                patient: None,
            }],
            properties: HashMap::default(),
        };
        assert_eq!(scenario, scenario_parser().parse("<3;{}>").unwrap());

        let scenario = Scenario {
            actors: vec![3, 4, 5],
            thematic_relations: vec![
                ThetaRoles {
                    agent: Some(3),
                    patient: Some(4),
                },
                ThetaRoles {
                    agent: Some(2),
                    patient: None,
                },
                ThetaRoles {
                    agent: None,
                    patient: Some(4),
                },
            ],
            properties: HashMap::default(),
        };

        assert_eq!(
            scenario,
            scenario_parser()
                .parse("<3,4,5;{A3,P4},{A2},{P4}>")
                .unwrap()
        );

        let scenario = Scenario {
            actors: vec![8, 2, 1],
            thematic_relations: vec![
                ThetaRoles {
                    agent: None,
                    patient: None,
                },
                ThetaRoles {
                    agent: Some(8),
                    patient: None,
                },
                ThetaRoles {
                    agent: None,
                    patient: Some(1),
                },
            ],
            properties: HashMap::from_iter([
                (34, vec![Entity::Actor(8), Entity::Actor(1)]),
                (32, vec![Entity::Event(0)]),
                (1234, vec![Entity::Actor(1), Entity::Event(2)]),
            ]),
        };

        assert_eq!(
            scenario,
            scenario_parser()
                .parse("<8 (34),2,1 (1234, 34);{(32)},{A8},{P1 (1234)}>")
                .unwrap()
        );
        Ok(())
    }
}
