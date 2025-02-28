use ahash::RandomState;
use chumsky::prelude::*;
use std::collections::HashMap;

use crate::{Actor, Entity, Event, PropertyLabel, Scenario, ThetaRoles};

struct StringThetaRole<'a> {
    agent: Option<&'a str>,
    patient: Option<&'a str>,
}

fn scenario_parser<'a>() -> impl Parser<'a, &'a str, Scenario> {
    let properties = text::int::<&str, _>(10)
        .map(|n| n.parse().unwrap())
        .padded()
        .separated_by(just(','))
        .collect::<Vec<PropertyLabel>>()
        .delimited_by(just('('), just(')'));

    let actor = text::ident().padded().then(properties.or_not());

    let actors = actor
        .map(|(a, p)| {
            let mut properties: HashMap<PropertyLabel, Vec<&str>, RandomState> = HashMap::default();
            if let Some(property_labels) = p {
                for property in property_labels {
                    properties.insert(property, vec![a]);
                }
            }
            (vec![a], properties)
        })
        .foldl(
            just(',').ignore_then(actor).repeated(),
            |(mut actors, mut properties), (actor, actor_props)| {
                if let Some(property_labels) = actor_props {
                    for property in property_labels {
                        properties
                            .entry(property)
                            .and_modify(|x| x.push(actor))
                            .or_insert(vec![actor]);
                    }
                }

                actors.push(actor);
                (actors, properties)
            },
        );

    let theta_role = |c: char| {
        just(c)
            .padded()
            .ignore_then(just(':'))
            .ignore_then(text::ident().padded())
            .padded()
    };

    let event = choice((
        theta_role('A')
            .then_ignore(just(','))
            .then(theta_role('P'))
            .map(|(a, p)| StringThetaRole {
                agent: Some(a),
                patient: Some(p),
            }),
        theta_role('P')
            .then_ignore(just(','))
            .then(theta_role('A'))
            .map(|(p, a)| StringThetaRole {
                agent: Some(a),
                patient: Some(p),
            }),
        theta_role('P').map(|n| StringThetaRole {
            agent: None,
            patient: Some(n),
        }),
        theta_role('A').map(|n| StringThetaRole {
            agent: Some(n),
            patient: None,
        }),
        empty().map(|_| StringThetaRole {
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
        .map(|((actors, actor_props), events)| {
            let mut keywords: HashMap<&str, usize> = HashMap::default();

            let actors: Vec<Actor> = actors
                .into_iter()
                .map(|x| {
                    let n = keywords.len();
                    *keywords.entry(x).or_insert(n) as u16
                })
                .collect();

            let (events, event_props) =
                events.unwrap_or_else(|| (Vec::default(), HashMap::default()));

            let mut properties: HashMap<PropertyLabel, Vec<Entity>, _> = actor_props
                .into_iter()
                .map(|(k, v)| {
                    (
                        k,
                        v.into_iter()
                            .map(|x| {
                                let n = keywords.len();
                                Entity::Actor(*keywords.entry(x).or_insert(n) as u16)
                            })
                            .collect(),
                    )
                })
                .collect();

            for (k, mut v) in event_props.into_iter() {
                properties
                    .entry(k)
                    .and_modify(|value| value.append(&mut v))
                    .or_insert(v);
            }

            let thematic_relations = events
                .into_iter()
                .map(|x| ThetaRoles {
                    agent: x.agent.map(|x| {
                        let n = keywords.len();
                        *keywords.entry(x).or_insert(n) as u16
                    }),
                    patient: x.patient.map(|x| {
                        let n = keywords.len();
                        *keywords.entry(x).or_insert(n) as u16
                    }),
                })
                .collect();

            Scenario {
                actors,
                thematic_relations,
                properties,
            }
        })
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse_scenario() -> anyhow::Result<()> {
        let scenario = Scenario {
            actors: vec![0],
            thematic_relations: vec![],
            properties: HashMap::default(),
        };

        assert_eq!(scenario, scenario_parser().parse("<John>").unwrap());
        assert_eq!(scenario, scenario_parser().parse("<John;>").unwrap());

        let scenario = Scenario {
            actors: vec![0],
            thematic_relations: vec![ThetaRoles {
                agent: None,
                patient: None,
            }],
            properties: HashMap::default(),
        };
        assert_eq!(scenario, scenario_parser().parse("<john;{}>").unwrap());

        let scenario = Scenario {
            actors: vec![0, 1, 2],
            thematic_relations: vec![
                ThetaRoles {
                    agent: Some(0),
                    patient: Some(1),
                },
                ThetaRoles {
                    agent: Some(1),
                    patient: None,
                },
                ThetaRoles {
                    agent: None,
                    patient: Some(2),
                },
            ],
            properties: HashMap::default(),
        };

        assert_eq!(
            scenario,
            scenario_parser()
                .parse("<john,mary,phil;{A: john,P: mary},{A: mary},{P: phil}>")
                .unwrap()
        );

        let scenario = Scenario {
            actors: vec![0, 1, 2],
            thematic_relations: vec![
                ThetaRoles {
                    agent: None,
                    patient: None,
                },
                ThetaRoles {
                    agent: Some(0),
                    patient: None,
                },
                ThetaRoles {
                    agent: None,
                    patient: Some(2),
                },
            ],
            properties: HashMap::from_iter([
                (34, vec![Entity::Actor(0), Entity::Actor(2)]),
                (32, vec![Entity::Event(0)]),
                (1234, vec![Entity::Actor(2), Entity::Event(2)]),
            ]),
        };

        assert_eq!(
            scenario,
            scenario_parser()
                .parse("<a (34),b,c (1234, 34);{(32)},{A: a},{P: c (1234)}>")
                .unwrap()
        );
        Ok(())
    }
}
