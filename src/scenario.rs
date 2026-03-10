use crate::{ScenarioParsingError, lambda::RootedLambdaPool};
use chumsky::{prelude::*, text::inline_whitespace};
use itertools::{Itertools, MultiProduct};
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, fmt::Display};

use crate::{Actor, Entity, Event, PropertyLabel, Scenario, ScenarioDataset, ThetaRoles};

impl Display for Scenario<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<")?;
        let mut first = true;
        for actor in &self.actors {
            if !first {
                write!(f, ", ")?;
            }

            write!(f, "{actor}")?;
            let mut first_property = true;
            for (property, prop_actors) in &self.properties {
                if prop_actors.contains(&Entity::Actor(actor)) {
                    if first_property {
                        first_property = false;
                        write!(f, " (")?;
                    } else {
                        write!(f, ", ")?;
                    }
                    write!(f, "{property}")?;
                }
            }
            if !first_property {
                write!(f, ")")?;
            }

            first = false;
        }
        if self.thematic_relations.is_empty() {
            return write!(f, ">");
        }

        write!(f, ";")?;
        let mut first = true;

        for (i, e) in self.thematic_relations.iter().enumerate() {
            if !first {
                write!(f, ", ")?;
            } else {
                write!(f, " ")?;
            }
            first = false;

            write!(f, "{{")?;

            if let Some(a) = e.agent {
                write!(f, "A: {a}")?;
                if e.patient.is_some() {
                    write!(f, " ")?;
                }
            }

            if let Some(p) = e.patient {
                write!(f, "P: {p}")?;
            }

            let mut first_property = true;
            for (property, prop_actors) in &self.properties {
                if prop_actors.contains(&Entity::Event(u8::try_from(i).unwrap())) {
                    if first_property {
                        first_property = false;
                        if e.agent.is_some() || e.patient.is_some() {
                            write!(f, " (")?;
                        } else {
                            write!(f, "(")?;
                        }
                    } else {
                        write!(f, ", ")?;
                    }
                    write!(f, "{property}")?;
                }
            }
            if !first_property {
                write!(f, ")")?;
            }

            write!(f, "}}")?;
        }

        write!(f, ">")?;

        let mut first = true;
        for q in self.questions() {
            if !first {
                write!(f, "; {q}")?;
            } else {
                write!(f, " {q}")?;
            }
            first = false;
        }
        Ok(())
    }
}

impl<'a> Scenario<'a> {
    ///Parses a scenario from a string.
    ///```
    ///# use simple_semantics::Scenario;
    ///let s = "<a (Red), b, c (Blue, Red); {(Green)}, {A: a}, {P: c (Blue)}> lambda a x pa_Blue(x); lambda a x pa_Red(x)";
    ///let scenario = Scenario::parse(s).unwrap();
    ///assert_eq!(scenario.to_string(), s);
    ///```
    ///
    ///# Errors
    ///Will return an error if the [`Scenario`] is incorrectly formatted.
    pub fn parse(s: &'a str) -> Result<Self, ScenarioParsingError> {
        Ok(scenario_parser()
            .padded()
            .then_ignore(end())
            .parse(s)
            .into_result()?)
    }
}

pub fn theta_role_parser<'a>()
-> impl Parser<'a, &'a str, ThetaRoles<'a>, extra::Err<Rich<'a, char>>> + Copy {
    let theta_role = |c: char| {
        just(c)
            .padded()
            .ignore_then(just(':'))
            .ignore_then(text::ident().padded())
            .padded()
    };

    choice((
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
}

pub fn scenario_parser<'a>() -> impl Parser<'a, &'a str, Scenario<'a>, extra::Err<Rich<'a, char>>> {
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

    let event = theta_role_parser()
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

    let scenario = actors
        .then((just(';')).ignore_then(events).or_not())
        .padded()
        .delimited_by(just('<'), just('>'))
        .map(|((actors, actor_props), events)| new_scenario(actors, actor_props, events));

    let scenario = scenario.then(
        inline_whitespace()
            .at_least(1)
            .ignore_then(
                none_of("\n;")
                    .repeated()
                    .to_slice()
                    .try_map(|x, s| RootedLambdaPool::parse(x).map_err(|e| Rich::custom(s, e)))
                    .separated_by(just(';'))
                    .collect::<Vec<_>>(),
            )
            .or_not(),
    );

    scenario.map(|(mut scenario, questions)| {
        if let Some(question) = questions {
            scenario.question = question;
        }
        scenario
    })
}

#[allow(clippy::too_many_lines)]
pub fn scenario_dataset_parser<'a>()
-> impl Parser<'a, &'a str, ScenarioDataset<'a>, extra::Err<Rich<'a, char>>> {
    let string_scenario_pair = none_of("\"")
        .repeated()
        .to_slice()
        .delimited_by(just('"'), just('"'))
        .map(|x: &str| x.split(' '))
        .then_ignore(inline_whitespace().at_least(1))
        .then(scenario_parser());

    string_scenario_pair
        .separated_by(text::newline())
        .at_least(1)
        .collect::<Vec<_>>()
        .map(|v| {
            let mut scenarios = vec![];
            let mut sentences = vec![];
            for (a, b) in v {
                sentences.push(a.collect());
                scenarios.push(b);
            }
            ScenarioDataset::new(scenarios, sentences).unwrap()
        })
        .padded()
        .then_ignore(end())
}

type EventParseType<'a> = Option<(Vec<ThetaRoles<'a>>, BTreeMap<&'a str, Vec<Entity<'a>>>)>;

fn new_scenario<'a>(
    actors: Vec<Actor<'a>>,
    actor_props: BTreeMap<&'a str, Vec<&'a str>>,
    events: EventParseType<'a>,
) -> Scenario<'a> {
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

    Scenario {
        question: vec![],
        actors,
        thematic_relations: events,
        properties,
    }
}

mod utilities;
use utilities::SetCounter;

///Generates all scenarios that can be generated with a given set of primitives
#[derive(Debug, Clone)]
pub struct ScenarioIterator<'a> {
    actors: ActorSetGenerator<'a>,
    current_actors: Vec<Actor<'a>>,
    current_props: BTreeMap<PropertyLabel<'a>, Vec<Entity<'a>>>,
    current_event_set: Vec<(ThetaRoles<'a>, PropertyLabel<'a>)>,
    event_kinds: Vec<PossibleEvent<'a>>,
    counter: SetCounter,
    max_number_of_events: Option<usize>,
}

///The kinds of possible events
#[derive(Debug, Clone, Eq, PartialEq, Copy, Ord, PartialOrd, Hash, Serialize, Deserialize)]
pub enum EventType {
    ///An intransitive with only an agent
    Unergative,

    ///An intransitive with only a patient
    Unaccusative,

    ///A transitive verb which cannot be reflexive
    TransitiveNonReflexive,

    ///A transitive verb
    Transitive,

    ///No possible theta role (e.g. rains)
    Avalent,
}

///A description of a possible kind of event (e.g. kind of verb)
#[derive(Debug, Clone, Eq, PartialEq, Copy, Ord, PartialOrd, Hash, Serialize, Deserialize)]
pub struct PossibleEvent<'a> {
    ///Name of the event predicate
    #[serde(borrow)]
    pub label: PropertyLabel<'a>,
    ///What kind of theta roles can be assigned to this event
    pub event_type: EventType,
}

impl<'a> Scenario<'a> {
    ///Returns a [`ScenarioIterator`] which goes over all possible scenarios with the provided
    ///actors and event descriptions
    ///
    #[must_use]
    pub fn all_scenarios(
        actors: &[Actor<'a>],
        event_kinds: &[PossibleEvent<'a>],
        actor_properties: &[PropertyLabel<'a>],
        max_number_of_events: Option<usize>,
        max_number_of_actors: Option<usize>,
        max_number_of_properties: Option<usize>,
    ) -> ScenarioIterator<'a> {
        let mut actors = ActorSetGenerator::new(
            actors,
            actor_properties,
            max_number_of_actors,
            max_number_of_properties,
        );
        let (current_actors, current_props) = actors.next().unwrap();
        let current_event_set = generate_all_events(&current_actors, event_kinds);
        let counter = SetCounter::new(current_event_set.len(), max_number_of_events);

        ScenarioIterator {
            actors,
            current_actors,
            current_event_set,
            current_props,
            event_kinds: event_kinds.to_vec(),
            counter,
            max_number_of_events,
        }
    }
}

impl<'a> Iterator for ScenarioIterator<'a> {
    type Item = Scenario<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.counter.done() {
            if let Some((new_actors, new_props)) = self.actors.next() {
                self.current_actors = new_actors;
                self.current_props = new_props;
                self.current_event_set =
                    generate_all_events(&self.current_actors, &self.event_kinds);
                self.counter =
                    SetCounter::new(self.current_event_set.len(), self.max_number_of_events);
            } else {
                return None;
            }
        }

        let mut properties = self.current_props.clone();
        let mut thematic_relations = vec![];
        for (i, (theta, label)) in self
            .counter
            .as_set(self.current_event_set.iter().copied())
            .enumerate()
        {
            properties
                .entry(label)
                .or_default()
                .push(Entity::Event(Event::try_from(i).expect("Too many events!")));
            thematic_relations.push(theta);
        }
        self.counter.increment();
        Some(Scenario::new(
            self.current_actors.clone(),
            thematic_relations,
            properties,
        ))
    }
}

fn generate_all_events<'a>(
    actors: &[Actor<'a>],
    event_kinds: &[PossibleEvent<'a>],
) -> Vec<(ThetaRoles<'a>, PropertyLabel<'a>)> {
    let mut all_events = vec![];
    for e in event_kinds {
        match e.event_type {
            EventType::Unergative => all_events.extend(actors.iter().copied().map(|x| {
                (
                    ThetaRoles {
                        agent: Some(x),
                        patient: None,
                    },
                    e.label,
                )
            })),
            EventType::Unaccusative => all_events.extend(actors.iter().copied().map(|x| {
                (
                    ThetaRoles {
                        agent: None,
                        patient: Some(x),
                    },
                    e.label,
                )
            })),
            EventType::TransitiveNonReflexive => {
                all_events.extend(actors.iter().copied().permutations(2).map(|mut x| {
                    let a = x.pop().unwrap();
                    let b = x.pop().unwrap();
                    (
                        ThetaRoles {
                            agent: Some(a),
                            patient: Some(b),
                        },
                        e.label,
                    )
                }));
            }
            EventType::Transitive => all_events.extend(
                itertools::repeat_n(actors.iter().copied(), 2)
                    .multi_cartesian_product()
                    .map(|mut x| {
                        let a = x.pop().unwrap();
                        let b = x.pop().unwrap();
                        (
                            ThetaRoles {
                                agent: Some(a),
                                patient: Some(b),
                            },
                            e.label,
                        )
                    }),
            ),
            EventType::Avalent => {
                all_events.push((
                    ThetaRoles {
                        agent: None,
                        patient: None,
                    },
                    e.label,
                ));
            }
        }
    }

    all_events
}

#[derive(Debug, Clone)]
struct ActorSetGenerator<'a> {
    actors: Vec<Actor<'a>>,
    actor_properties: Vec<PropertyLabel<'a>>,
    property_counter: MultiProduct<SetCounter>,
    max_number_of_properties: Option<usize>,
    included: SetCounter,
}

impl<'a> ActorSetGenerator<'a> {
    fn new(
        actors: &[Actor<'a>],
        actor_properties: &[PropertyLabel<'a>],
        max_number_of_actors: Option<usize>,
        max_number_of_properties: Option<usize>,
    ) -> Self {
        ActorSetGenerator {
            property_counter: std::iter::empty::<SetCounter>().multi_cartesian_product(),
            included: SetCounter::new(actors.len(), max_number_of_actors),
            actors: actors.to_vec(),
            max_number_of_properties,
            actor_properties: actor_properties.to_vec(),
        }
    }
}

impl<'a> Iterator for ActorSetGenerator<'a> {
    type Item = (Vec<Actor<'a>>, BTreeMap<PropertyLabel<'a>, Vec<Entity<'a>>>);

    fn next(&mut self) -> Option<Self::Item> {
        let props = self.property_counter.next().unwrap_or_else(|| {
            self.included.increment();
            let n_actors = self.included.current_size();
            self.property_counter = (0..n_actors)
                .map(|_| {
                    SetCounter::new(self.actor_properties.len(), self.max_number_of_properties)
                })
                .multi_cartesian_product();
            self.property_counter.next().unwrap()
        });

        if self.included.done() {
            return None;
        }

        let mut actor_properties: BTreeMap<_, Vec<_>> = BTreeMap::new();

        let actors: Vec<Actor<'a>> = self
            .included
            .included()
            .as_set(&self.actors)
            .copied()
            .zip(props)
            .map(|(x, props)| {
                for prop in props.as_set(&self.actor_properties) {
                    actor_properties
                        .entry(*prop)
                        .or_default()
                        .push(Entity::Actor(x));
                }
                x
            })
            .collect();

        Some((actors, actor_properties))
    }
}

#[cfg(test)]
mod test {
    use crate::scenario::generate_all_events;

    use super::*;
    use ahash::HashSet;

    #[test]
    fn generate_all_actors() {
        let s = ActorSetGenerator::new(&["John", "Mary"], &["man", "woman"], None, None);

        let mut set = HashSet::default();
        for p in s {
            println!("{p:?}");
            assert!(!set.contains(&p));
            set.insert(p);
        }
        assert_eq!(set.len(), 25);
    }

    #[test]
    fn generate_all_scenarios() {
        let actors = ["John", "Mary"];
        let event_kinds = [
            PossibleEvent {
                label: "rain",
                event_type: EventType::Avalent,
            },
            PossibleEvent {
                label: "runs",
                event_type: EventType::Unergative,
            },
            PossibleEvent {
                label: "falls",
                event_type: EventType::Unaccusative,
            },
            PossibleEvent {
                label: "loves",
                event_type: EventType::TransitiveNonReflexive,
            },
        ];

        let mut scenarios = HashSet::default();
        for x in Scenario::all_scenarios(&actors, &event_kinds, &["man", "woman"], None, None, None)
        {
            assert!(!scenarios.contains(&x));
            scenarios.insert(x);
        }
        assert_eq!(scenarios.len(), 2114);

        let mut scenarios = HashSet::default();
        let mut at_least_1 = false;
        let mut at_least_2 = false;
        for x in Scenario::all_scenarios(
            &actors,
            &event_kinds,
            &["man", "woman"],
            Some(2),
            Some(1),
            None,
        ) {
            assert!(!scenarios.contains(&x));
            assert!(x.actors.len() <= 1);
            if x.actors.len() == 1 {
                at_least_1 = true;
            }

            if x.events().count() == 2 {
                at_least_2 = true;
            }
            assert!(x.events().count() <= 2);
            scenarios.insert(x);
        }

        assert!(at_least_1);
        assert!(at_least_2);
        assert_eq!(scenarios.len(), 58);
    }

    #[test]
    fn generate_event_test() {
        let actors = ["John", "Mary", "Phil"];
        let event_kinds = [
            PossibleEvent {
                label: "rain",
                event_type: EventType::Avalent,
            },
            PossibleEvent {
                label: "runs",
                event_type: EventType::Unergative,
            },
            PossibleEvent {
                label: "falls",
                event_type: EventType::Unaccusative,
            },
            PossibleEvent {
                label: "likes",
                event_type: EventType::Transitive,
            },
            PossibleEvent {
                label: "loves",
                event_type: EventType::TransitiveNonReflexive,
            },
        ];

        let e = generate_all_events(&actors, &event_kinds);

        assert_eq!(
            e,
            [
                (
                    ThetaRoles {
                        agent: None,
                        patient: None
                    },
                    "rain"
                ),
                (
                    ThetaRoles {
                        agent: Some("John"),
                        patient: None
                    },
                    "runs"
                ),
                (
                    ThetaRoles {
                        agent: Some("Mary"),
                        patient: None
                    },
                    "runs"
                ),
                (
                    ThetaRoles {
                        agent: Some("Phil"),
                        patient: None
                    },
                    "runs"
                ),
                (
                    ThetaRoles {
                        agent: None,
                        patient: Some("John")
                    },
                    "falls"
                ),
                (
                    ThetaRoles {
                        agent: None,
                        patient: Some("Mary")
                    },
                    "falls"
                ),
                (
                    ThetaRoles {
                        agent: None,
                        patient: Some("Phil")
                    },
                    "falls"
                ),
                (
                    ThetaRoles {
                        agent: Some("John"),
                        patient: Some("John")
                    },
                    "likes"
                ),
                (
                    ThetaRoles {
                        agent: Some("Mary"),
                        patient: Some("John")
                    },
                    "likes"
                ),
                (
                    ThetaRoles {
                        agent: Some("Phil"),
                        patient: Some("John")
                    },
                    "likes"
                ),
                (
                    ThetaRoles {
                        agent: Some("John"),
                        patient: Some("Mary")
                    },
                    "likes"
                ),
                (
                    ThetaRoles {
                        agent: Some("Mary"),
                        patient: Some("Mary")
                    },
                    "likes"
                ),
                (
                    ThetaRoles {
                        agent: Some("Phil"),
                        patient: Some("Mary")
                    },
                    "likes"
                ),
                (
                    ThetaRoles {
                        agent: Some("John"),
                        patient: Some("Phil")
                    },
                    "likes"
                ),
                (
                    ThetaRoles {
                        agent: Some("Mary"),
                        patient: Some("Phil")
                    },
                    "likes"
                ),
                (
                    ThetaRoles {
                        agent: Some("Phil"),
                        patient: Some("Phil")
                    },
                    "likes"
                ),
                (
                    ThetaRoles {
                        agent: Some("Mary"),
                        patient: Some("John")
                    },
                    "loves"
                ),
                (
                    ThetaRoles {
                        agent: Some("Phil"),
                        patient: Some("John")
                    },
                    "loves"
                ),
                (
                    ThetaRoles {
                        agent: Some("John"),
                        patient: Some("Mary")
                    },
                    "loves"
                ),
                (
                    ThetaRoles {
                        agent: Some("Phil"),
                        patient: Some("Mary")
                    },
                    "loves"
                ),
                (
                    ThetaRoles {
                        agent: Some("John"),
                        patient: Some("Phil")
                    },
                    "loves"
                ),
                (
                    ThetaRoles {
                        agent: Some("Mary"),
                        patient: Some("Phil")
                    },
                    "loves"
                )
            ]
        );
    }

    #[test]
    #[should_panic]
    fn parse_trailing() {
        scenario_dataset_parser().parse("<John>trailing").unwrap();
    }

    #[test]
    fn white_space_shenanigans() -> anyhow::Result<()> {
        scenario_dataset_parser()
            .parse("\"blah\" <John; {A: John (run)}>")
            .unwrap();
        scenario_dataset_parser()
            .parse("\" s\" <John ; {A: John (run)}>")
            .unwrap();
        scenario_dataset_parser()
            .parse("\"\" < John ; { A : John (run)}>")
            .unwrap();
        scenario_dataset_parser()
            .parse("\"aaa\"      < John ; { A :  John ( run )  } >")
            .unwrap();
        scenario_dataset_parser()
            .parse("\"aaa\" < John; {A: John ( run)}>")
            .unwrap();
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
            *scenario_dataset_parser()
                .parse("\"John\" <John>\n\"Mary\" <Mary>\n\"John\" <John>")
                .unwrap()
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
            *scenario_dataset_parser()
                .parse("\"John runs\" <John; {A: John (run)}>\n\"Mary runs\" <Mary; {A: Mary (run)}>\n\"John sees Mary\" <Mary, John; {A: John, P: Mary (see)}>")
                .unwrap()
                .scenarios
        );
        Ok(())
    }

    #[test]
    fn parse_scenarios_with_questions() -> anyhow::Result<()> {
        let scenarios = scenario_dataset_parser()
                .parse("\"John runs\" <John; {A: John (run)}> lambda a x (x)\n\"Mary runs\" <Mary; {A: Mary (run)}>\n\"John sees Mary\" <Mary, John; {A: John, P: Mary (see)}>  a_0")
                .unwrap();

        assert_eq!(
            scenarios.scenarios[0].question.first().unwrap().to_string(),
            "lambda a x x"
        );
        assert_eq!(scenarios.scenarios[1].question, vec![]);
        assert_eq!(
            scenarios.scenarios[2].question.first().unwrap().to_string(),
            "a_0"
        );

        let scenarios = scenario_dataset_parser()
                .parse("\"John runs\" <John; {A: John (run)}> lambda a x (x)\n\"Mary runs\" <Mary; {A: Mary (run)}>\n\"John sees Mary\" <Mary, John; {A: John, P: Mary (see)}>  a_0; a_1; a_3")
                .unwrap();
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
            *scenario_dataset_parser()
                .parse("\"John\" <John>")
                .unwrap()
                .scenarios
                .first()
                .unwrap()
        );
        assert_eq!(
            scenario,
            *scenario_dataset_parser()
                .parse("\"John\" <John;>")
                .unwrap()
                .scenarios
                .first()
                .unwrap()
        );
        assert_eq!(
            scenario,
            *scenario_dataset_parser()
                .parse("\"John\" < John; >")
                .unwrap()
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
            *scenario_dataset_parser()
                .parse("\"john\" <john;{}>")
                .unwrap()
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
            *scenario_dataset_parser()
                .parse("\"john sees mary\" <john,mary,phil;{A: john,P: mary},{A: mary},{P: phil}>")
                .unwrap()
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
            *scenario_dataset_parser()
                .parse("\"blue is blued\" <a (Red),b,c (Blue, Red);{(Green)},{A: a},{P: c (Blue)}>")
                .unwrap()
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
