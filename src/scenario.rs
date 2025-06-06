use ahash::{HashSet, RandomState};
use chumsky::{prelude::*, text::inline_whitespace};
use std::collections::HashMap;

use crate::language::{LambdaParseError, lot_parser};
use crate::{Actor, Entity, Event, Scenario, ScenarioDataset, ThetaRoles};

pub fn scenario_parser<'a>()
-> impl Parser<'a, &'a str, Result<ScenarioDataset<'a>, LambdaParseError>, extra::Err<Rich<'a, char>>>
{
    let string = none_of("\"")
        .repeated()
        .to_slice()
        .delimited_by(just('"'), just('"'));

    let properties = text::ident()
        .padded()
        .separated_by(just(','))
        .collect::<Vec<&str>>()
        .delimited_by(just('('), just(')'))
        .padded();

    let actor = text::ident().padded().then(properties.or_not());

    let actors = actor
        .map(|(a, p)| {
            let mut properties: HashMap<&str, Vec<_>, RandomState> = HashMap::default();
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

            (events, properties)
        })
        .foldl(
            just(',').ignore_then(event).repeated().enumerate(),
            |(mut acc_event, mut acc_props), (i, (event, event_props))| {
                acc_event.push(event);
                if let Some(event_props) = event_props {
                    for property_label in event_props {
                        acc_props
                            .entry(property_label)
                            .and_modify(|x| x.push(Entity::Event((i + 1) as Event)))
                            .or_insert(vec![Entity::Event((i + 1) as Event)]);
                    }
                }
                (acc_event, acc_props)
            },
        );

    let scenario = string
        .then_ignore(inline_whitespace().at_least(1))
        .then(
            actors
                .then((just(';')).ignore_then(events).or_not())
                .padded()
                .delimited_by(just('<'), just('>')),
        )
        .map(|(s, ((actors, actor_props), events))| (s, actors, actor_props, events));

    let lot = lot_parser();

    let scenario = scenario.then(inline_whitespace().at_least(1).ignore_then(lot).or_not());

    scenario
        .clone()
        .map(|((s, actors, actor_props, events), lot)| {
            let mut dataset = (ScenarioDataset::default(), HashSet::default());
            add_scenario(&mut dataset, s, actors, actor_props, events);
            (dataset, vec![lot])
        })
        .foldl(
            text::newline().ignore_then(scenario).repeated(),
            |(mut dataset, mut lot_vec), ((s, actors, actor_props, events), lot)| {
                add_scenario(&mut dataset, s, actors, actor_props, events);
                lot_vec.push(lot);
                (dataset, lot_vec)
            },
        )
        .padded()
        .then_ignore(end())
        .map(|((mut data, lemmas), lot_vec)| {
            data.lemmas = lemmas.into_iter().collect();
            data.lemmas.sort();
            let lot_vec = lot_vec
                .into_iter()
                .enumerate()
                .filter_map(|(i, x)| {
                    x.map(|x| match x.to_pool() {
                        Ok(x) => Ok((i, x)),
                        Err(e) => Err(e),
                    })
                })
                .collect::<Result<Vec<_>, LambdaParseError>>();

            match lot_vec {
                Ok(lot_vec) => {
                    lot_vec
                        .into_iter()
                        .for_each(|(i, x)| data.scenarios[i].question = Some(x));
                    Ok(data)
                }
                Err(e) => Err(e),
            }
        })
}

type EventParseType<'a> = Option<(
    Vec<ThetaRoles<'a>>,
    HashMap<&'a str, Vec<Entity<'a>>, ahash::RandomState>,
)>;

fn add_scenario<'a>(
    training_dataset: &mut (ScenarioDataset<'a>, HashSet<&'a str>),
    s: &'a str,
    actors: Vec<Actor<'a>>,
    actor_props: HashMap<&'a str, Vec<&'a str>, RandomState>,
    events: EventParseType<'a>,
) {
    let (events, event_props) = events.unwrap_or_else(|| (Vec::default(), HashMap::default()));

    let mut properties: HashMap<&str, Vec<Entity>, _> = actor_props
        .into_iter()
        .map(|(k, v)| (k, v.into_iter().map(Entity::Actor).collect()))
        .collect();

    for (k, mut v) in event_props.into_iter() {
        properties
            .entry(k)
            .and_modify(|value| value.append(&mut v))
            .or_insert(v);
    }

    training_dataset.0.scenarios.push(Scenario {
        question: None,
        actors,
        thematic_relations: events,
        properties,
    });

    let s: Vec<&str> = s.split(" ").collect();

    training_dataset.1.extend(s.clone());
    training_dataset.0.sentences.push(s);
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[should_panic]
    fn parse_trailing() {
        scenario_parser().parse("<John>trailing").unwrap().unwrap();
    }

    #[test]
    fn white_space_shenanigans() -> anyhow::Result<()> {
        scenario_parser()
            .parse("\"blah\" <John; {A: John (run)}>")
            .unwrap()?;
        scenario_parser()
            .parse("\" s\" <John ; {A: John (run)}>")
            .unwrap()?;
        scenario_parser()
            .parse("\"\" < John ; { A : John (run)}>")
            .unwrap()?;
        scenario_parser()
            .parse("\"aaa\"      < John ; { A :  John ( run )  } >")
            .unwrap()?;
        scenario_parser()
            .parse("\"aaa\" < John; {A: John ( run)}>")
            .unwrap()?;
        Ok(())
    }

    #[test]
    fn parse_multiple_scenarios() -> anyhow::Result<()> {
        let scenarios = vec![
            Scenario {
                question: None,
                actors: vec!["John"],
                thematic_relations: vec![],
                properties: HashMap::default(),
            },
            Scenario {
                question: None,
                actors: vec!["Mary"],
                thematic_relations: vec![],
                properties: HashMap::default(),
            },
            Scenario {
                question: None,
                actors: vec!["John"],
                thematic_relations: vec![],
                properties: HashMap::default(),
            },
        ];

        assert_eq!(
            scenarios,
            *scenario_parser()
                .parse("\"John\" <John>\n\"Mary\" <Mary>\n\"John\" <John>")
                .unwrap()?
                .scenarios
        );

        let scenarios = vec![
            Scenario {
                question: None,
                actors: vec!["John"],
                thematic_relations: vec![ThetaRoles {
                    agent: Some("John"),
                    patient: None,
                }],
                properties: HashMap::from_iter([("run", vec![Entity::Event(0)])]),
            },
            Scenario {
                question: None,
                actors: vec!["Mary"],
                thematic_relations: vec![ThetaRoles {
                    agent: Some("Mary"),
                    patient: None,
                }],
                properties: HashMap::from_iter([("run", vec![Entity::Event(0)])]),
            },
            Scenario {
                question: None,
                actors: vec!["Mary", "John"],
                thematic_relations: vec![ThetaRoles {
                    agent: Some("John"),
                    patient: Some("Mary"),
                }],
                properties: HashMap::from_iter([("see", vec![Entity::Event(0)])]),
            },
        ];

        assert_eq!(
            scenarios,
            *scenario_parser()
                .parse("\"John runs\" <John; {A: John (run)}>\n\"Mary runs\" <Mary; {A: Mary (run)}>\n\"John sees Mary\" <Mary, John; {A: John, P: Mary (see)}>")
                .unwrap()?
                .scenarios
        );
        Ok(())
    }

    #[test]
    fn parse_scenarios_with_questions() -> anyhow::Result<()> {
        let scenarios = scenario_parser()
                .parse("\"John runs\" <John; {A: John (run)}> lambda a x (x)\n\"Mary runs\" <Mary; {A: Mary (run)}>\n\"John sees Mary\" <Mary, John; {A: John, P: Mary (see)}>  a_0")
                .unwrap()?;

        assert_eq!(
            scenarios.scenarios[0]
                .question
                .as_ref()
                .unwrap()
                .to_string(),
            "lambda a x (x)"
        );
        assert_eq!(scenarios.scenarios[1].question, None);
        assert_eq!(
            scenarios.scenarios[2]
                .question
                .as_ref()
                .unwrap()
                .to_string(),
            "a_0"
        );

        Ok(())
    }

    #[test]
    fn parse_scenario() -> anyhow::Result<()> {
        let scenario = Scenario {
            question: None,
            actors: vec!["John"],
            thematic_relations: vec![],
            properties: HashMap::default(),
        };

        assert_eq!(
            scenario,
            *scenario_parser()
                .parse("\"John\" <John>")
                .unwrap()?
                .scenarios
                .first()
                .unwrap()
        );
        assert_eq!(
            scenario,
            *scenario_parser()
                .parse("\"John\" <John;>")
                .unwrap()?
                .scenarios
                .first()
                .unwrap()
        );
        assert_eq!(
            scenario,
            *scenario_parser()
                .parse("\"John\" < John; >")
                .unwrap()?
                .scenarios
                .first()
                .unwrap()
        );

        let scenario = Scenario {
            question: None,
            actors: vec!["john"],
            thematic_relations: vec![ThetaRoles {
                agent: None,
                patient: None,
            }],
            properties: HashMap::default(),
        };
        assert_eq!(
            scenario,
            *scenario_parser()
                .parse("\"john\" <john;{}>")
                .unwrap()?
                .scenarios
                .first()
                .unwrap()
        );

        let scenario = Scenario {
            question: None,
            actors: vec!["john", "mary", "phil"],
            thematic_relations: vec![
                ThetaRoles {
                    agent: Some("john"),
                    patient: Some("mary"),
                },
                ThetaRoles {
                    agent: Some("mary"),
                    patient: None,
                },
                ThetaRoles {
                    agent: None,
                    patient: Some("phil"),
                },
            ],
            properties: HashMap::default(),
        };

        assert_eq!(
            scenario,
            *scenario_parser()
                .parse("\"john sees mary\" <john,mary,phil;{A: john,P: mary},{A: mary},{P: phil}>")
                .unwrap()?
                .scenarios
                .first()
                .unwrap()
        );

        let scenario = Scenario {
            question: None,
            actors: vec!["a", "b", "c"],
            thematic_relations: vec![
                ThetaRoles {
                    agent: None,
                    patient: None,
                },
                ThetaRoles {
                    agent: Some("a"),
                    patient: None,
                },
                ThetaRoles {
                    agent: None,
                    patient: Some("c"),
                },
            ],
            properties: HashMap::from_iter([
                ("Red", vec![Entity::Actor("a"), Entity::Actor("c")]),
                ("Green", vec![Entity::Event(0)]),
                ("Blue", vec![Entity::Actor("c"), Entity::Event(2)]),
            ]),
        };

        assert_eq!(
            scenario,
            *scenario_parser()
                .parse("\"blue is blued\" <a (Red),b,c (Blue, Red);{(Green)},{A: a},{P: c (Blue)}>")
                .unwrap()?
                .scenarios
                .first()
                .unwrap()
        );
        Ok(())
    }
}
