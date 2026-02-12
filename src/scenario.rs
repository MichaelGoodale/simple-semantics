use ahash::HashSet;
use chumsky::text::newline;
use chumsky::{prelude::*, text::inline_whitespace};
use std::collections::BTreeMap;

use crate::lambda::RootedLambdaPool;
use crate::language::LambdaParseError;
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
            let mut properties: BTreeMap<&str, Vec<_>> = BTreeMap::default();
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
        empty().map(|()| ThetaRoles {
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
            let mut properties: BTreeMap<&str, Vec<Entity>> = BTreeMap::default();

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
                        let e = Entity::Event(Event::try_from(i + 1).unwrap());
                        acc_props
                            .entry(property_label)
                            .and_modify(|x| x.push(e))
                            .or_insert_with(|| vec![e]);
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

    let scenario = scenario.then(
        inline_whitespace()
            .at_least(1)
            .ignore_then(any().and_is(newline().not()).repeated().to_slice())
            .or_not(),
    );

    scenario
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
            data.lemmas.sort_unstable();
            let lot_vec = lot_vec
                .into_iter()
                .enumerate()
                .filter_map(|(i, x)| {
                    x.map(|s: &str| {
                        s.split(';')
                            .map(|s| match RootedLambdaPool::parse(s) {
                                Ok(x) => Ok(x),
                                Err(e) => Err(e),
                            })
                            .collect::<Result<Vec<_>, LambdaParseError>>()
                            .map(|s| (s, i))
                    })
                })
                .collect::<Result<Vec<(Vec<_>, usize)>, LambdaParseError>>();

            match lot_vec {
                Ok(lot_vec) => {
                    for (x, i) in lot_vec {
                        data.scenarios[i].question.extend(x);
                    }
                    Ok(data)
                }
                Err(e) => Err(e),
            }
        })
}

type EventParseType<'a> = Option<(Vec<ThetaRoles<'a>>, BTreeMap<&'a str, Vec<Entity<'a>>>)>;

fn add_scenario<'a>(
    training_dataset: &mut (ScenarioDataset<'a>, HashSet<&'a str>),
    s: &'a str,
    actors: Vec<Actor<'a>>,
    actor_props: BTreeMap<&'a str, Vec<&'a str>>,
    events: EventParseType<'a>,
) {
    let (events, event_props) = events.unwrap_or_else(|| (Vec::default(), BTreeMap::default()));

    let mut properties: BTreeMap<&str, Vec<Entity>> = actor_props
        .into_iter()
        .map(|(k, v)| (k, v.into_iter().map(Entity::Actor).collect()))
        .collect();

    for (k, mut v) in event_props {
        properties
            .entry(k)
            .and_modify(|value| value.append(&mut v))
            .or_insert(v);
    }

    training_dataset.0.scenarios.push(Scenario {
        question: vec![],
        actors,
        thematic_relations: events,
        properties,
    });

    let s: Vec<&str> = s.split(' ').collect();

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
                question: vec![],
                actors: vec!["John"],
                thematic_relations: vec![],
                properties: BTreeMap::default(),
            },
            Scenario {
                question: vec![],
                actors: vec!["Mary"],
                thematic_relations: vec![],
                properties: BTreeMap::default(),
            },
            Scenario {
                question: vec![],
                actors: vec!["John"],
                thematic_relations: vec![],
                properties: BTreeMap::default(),
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
                question: vec![],
                actors: vec!["John"],
                thematic_relations: vec![ThetaRoles {
                    agent: Some("John"),
                    patient: None,
                }],
                properties: BTreeMap::from_iter([("run", vec![Entity::Event(0)])]),
            },
            Scenario {
                question: vec![],
                actors: vec!["Mary"],
                thematic_relations: vec![ThetaRoles {
                    agent: Some("Mary"),
                    patient: None,
                }],
                properties: BTreeMap::from_iter([("run", vec![Entity::Event(0)])]),
            },
            Scenario {
                question: vec![],
                actors: vec!["Mary", "John"],
                thematic_relations: vec![ThetaRoles {
                    agent: Some("John"),
                    patient: Some("Mary"),
                }],
                properties: BTreeMap::from_iter([("see", vec![Entity::Event(0)])]),
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
            scenarios.scenarios[0].question.first().unwrap().to_string(),
            "lambda a x x"
        );
        assert_eq!(scenarios.scenarios[1].question, vec![]);
        assert_eq!(
            scenarios.scenarios[2].question.first().unwrap().to_string(),
            "a_0"
        );

        let scenarios = scenario_parser()
                .parse("\"John runs\" <John; {A: John (run)}> lambda a x (x)\n\"Mary runs\" <Mary; {A: Mary (run)}>\n\"John sees Mary\" <Mary, John; {A: John, P: Mary (see)}>  a_0; a_1; a_3")
                .unwrap()?;
        assert_eq!(scenarios.scenarios[2].question.len(), 3);

        assert_eq!(
            scenarios.scenarios[2].question.last().unwrap().to_string(),
            "a_3"
        );
        Ok(())
    }

    #[test]
    fn parse_scenario() -> anyhow::Result<()> {
        let scenario = Scenario {
            question: vec![],
            actors: vec!["John"],
            thematic_relations: vec![],
            properties: BTreeMap::default(),
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
            question: vec![],
            actors: vec!["john"],
            thematic_relations: vec![ThetaRoles {
                agent: None,
                patient: None,
            }],
            properties: BTreeMap::default(),
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
            question: vec![],
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
            properties: BTreeMap::default(),
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
            question: vec![],
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
            properties: BTreeMap::from_iter([
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
        let s = serde_json::to_string(&scenario)?;
        let scenario_2: Scenario = serde_json::from_str(s.as_str())?;
        assert_eq!(scenario, scenario_2);

        Ok(())
    }
}
