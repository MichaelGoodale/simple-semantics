use ahash::RandomState;
use chumsky::prelude::*;
use std::collections::{BTreeMap, HashMap};

use crate::{Actor, Entity, Event, LabelledScenarios, PropertyLabel, Scenario, ThetaRoles};

struct StringThetaRole<'a> {
    agent: Option<&'a str>,
    patient: Option<&'a str>,
}

struct StringEvents<'a> {
    events: Vec<StringThetaRole<'a>>,
    event_props: ahash::HashMap<&'a str, Vec<Entity>>,
}

fn scenario_parser<'a>() -> impl Parser<'a, &'a str, LabelledScenarios> {
    let properties = text::ident()
        .padded()
        .separated_by(just(','))
        .collect::<Vec<&str>>()
        .delimited_by(just('('), just(')'))
        .padded();

    let actor = text::ident().padded().then(properties.or_not());

    let actors = actor
        .map(|(a, p)| {
            let mut properties: HashMap<&str, Vec<&str>, RandomState> = HashMap::default();
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
    .delimited_by(just('{'), just('}'))
    .padded();

    let events = event
        .or_not()
        .map(|event_data| {
            let mut properties: HashMap<&str, Vec<Entity>, RandomState> = HashMap::default();

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

            StringEvents {
                events,
                event_props: properties,
            }
        })
        .foldl(
            just(',').ignore_then(event).repeated().enumerate(),
            |mut string_events, (i, (event, event_props))| {
                string_events.events.push(event);
                if let Some(event_props) = event_props {
                    for property_label in event_props {
                        string_events
                            .event_props
                            .entry(property_label)
                            .and_modify(|x| x.push(Entity::Event((i + 1) as Event)))
                            .or_insert(vec![Entity::Event((i + 1) as Event)]);
                    }
                }
                string_events
            },
        );

    let scenario = actors
        .then((just(';')).ignore_then(events).or_not())
        .padded()
        .delimited_by(just('<'), just('>'));

    scenario
        .map(|((actors, actor_props), events)| {
            let mut dataset = LabelledScenarios {
                scenarios: vec![],
                actor_labels: HashMap::default(),
                property_labels: HashMap::default(),
            };
            add_scenario(&mut dataset, actors, actor_props, events);
            dataset
        })
        .foldl(
            text::newline().ignore_then(scenario).repeated(),
            |mut dataset, ((actors, actor_props), events)| {
                add_scenario(&mut dataset, actors, actor_props, events);
                dataset
            },
        )
        .then_ignore(end())
}

fn add_scenario<'a>(
    training_dataset: &mut LabelledScenarios,
    actors: Vec<&'a str>,
    actor_props: HashMap<&'a str, Vec<&'a str>, RandomState>,
    events: Option<StringEvents>,
) {
    let actors: Vec<Actor> = actors
        .into_iter()
        .map(|x| {
            let n = training_dataset.actor_labels.len();
            *training_dataset
                .actor_labels
                .entry(x.to_string())
                .or_insert(n as u16)
        })
        .collect();

    let events = events.unwrap_or_else(|| StringEvents {
        events: Vec::default(),
        event_props: HashMap::default(),
    });

    let mut properties: BTreeMap<&str, Vec<Entity>> = actor_props
        .into_iter()
        .map(|(k, v)| {
            (
                k,
                v.into_iter()
                    .map(|x| Entity::Actor(training_dataset.get_actor_label(x)))
                    .collect(),
            )
        })
        .collect();

    for (k, mut v) in events.event_props.into_iter() {
        properties
            .entry(k)
            .and_modify(|value| value.append(&mut v))
            .or_insert(v);
    }

    let thematic_relations = events
        .events
        .into_iter()
        .map(|x| ThetaRoles {
            agent: x.agent.map(|x| training_dataset.get_actor_label(x)),
            patient: x.patient.map(|x| training_dataset.get_actor_label(x)),
        })
        .collect();

    let properties = properties
        .into_iter()
        .map(|(k, v)| (training_dataset.get_property_label(k), v))
        .collect();

    training_dataset.scenarios.push(Scenario {
        actors,
        thematic_relations,
        properties,
    });
}

impl LabelledScenarios {
    fn get_property_label(&mut self, label: &str) -> PropertyLabel {
        let n = self.property_labels.len();
        *self
            .property_labels
            .entry(label.to_string())
            .or_insert(n as u32)
    }

    fn get_actor_label(&mut self, label: &str) -> Actor {
        let n = self.actor_labels.len();
        *self
            .actor_labels
            .entry(label.to_string())
            .or_insert(n as u16)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[should_panic]
    fn parse_trailing() {
        scenario_parser().parse("<John>trailing").unwrap();
    }

    #[test]
    fn white_space_shenanigans() {
        scenario_parser().parse("<John; {A: John (run)}>").unwrap();
        scenario_parser().parse("<John ; {A: John (run)}>").unwrap();
        scenario_parser()
            .parse("< John ; { A : John (run)}>")
            .unwrap();
        scenario_parser()
            .parse("< John ; { A :  John ( run )  } >")
            .unwrap();
        scenario_parser()
            .parse("< John; {A: John ( run)}>")
            .unwrap();
    }

    #[test]
    fn parse_multiple_scenarios() -> anyhow::Result<()> {
        let scenarios = vec![
            Scenario {
                actors: vec![0],
                thematic_relations: vec![],
                properties: HashMap::default(),
            },
            Scenario {
                actors: vec![1],
                thematic_relations: vec![],
                properties: HashMap::default(),
            },
            Scenario {
                actors: vec![0],
                thematic_relations: vec![],
                properties: HashMap::default(),
            },
        ];

        assert_eq!(
            scenarios,
            *scenario_parser()
                .parse("<John>\n<Mary>\n<John>")
                .unwrap()
                .scenarios
        );

        let scenarios = vec![
            Scenario {
                actors: vec![0],
                thematic_relations: vec![ThetaRoles {
                    agent: Some(0),
                    patient: None,
                }],
                properties: HashMap::from_iter([(0, vec![Entity::Event(0)])]),
            },
            Scenario {
                actors: vec![1],
                thematic_relations: vec![ThetaRoles {
                    agent: Some(1),
                    patient: None,
                }],
                properties: HashMap::from_iter([(0, vec![Entity::Event(0)])]),
            },
            Scenario {
                actors: vec![1, 0],
                thematic_relations: vec![ThetaRoles {
                    agent: Some(0),
                    patient: Some(1),
                }],
                properties: HashMap::from_iter([(1, vec![Entity::Event(0)])]),
            },
        ];

        assert_eq!(
            scenarios,
            *scenario_parser()
                .parse("<John; {A: John (run)}>\n<Mary; {A: Mary (run)}>\n<Mary, John; {A: John, P: Mary (see)}>")
                .unwrap()
                .scenarios
        );
        Ok(())
    }

    #[test]
    fn parse_scenario() -> anyhow::Result<()> {
        let scenario = Scenario {
            actors: vec![0],
            thematic_relations: vec![],
            properties: HashMap::default(),
        };

        assert_eq!(
            scenario,
            *scenario_parser()
                .parse("<John>")
                .unwrap()
                .scenarios
                .first()
                .unwrap()
        );
        assert_eq!(
            scenario,
            *scenario_parser()
                .parse("<John;>")
                .unwrap()
                .scenarios
                .first()
                .unwrap()
        );
        assert_eq!(
            scenario,
            *scenario_parser()
                .parse("< John; >")
                .unwrap()
                .scenarios
                .first()
                .unwrap()
        );

        let scenario = Scenario {
            actors: vec![0],
            thematic_relations: vec![ThetaRoles {
                agent: None,
                patient: None,
            }],
            properties: HashMap::default(),
        };
        assert_eq!(
            scenario,
            *scenario_parser()
                .parse("<john;{}>")
                .unwrap()
                .scenarios
                .first()
                .unwrap()
        );

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
            *scenario_parser()
                .parse("<john,mary,phil;{A: john,P: mary},{A: mary},{P: phil}>")
                .unwrap()
                .scenarios
                .first()
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
                (2, vec![Entity::Actor(0), Entity::Actor(2)]),
                (1, vec![Entity::Event(0)]),
                (0, vec![Entity::Actor(2), Entity::Event(2)]),
            ]),
        };

        assert_eq!(
            scenario,
            *scenario_parser()
                .parse("<a (Red),b,c (Blue, Red);{(Green)},{A: a},{P: c (Blue)}>")
                .unwrap()
                .scenarios
                .first()
                .unwrap()
        );
        Ok(())
    }
}
