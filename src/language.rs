//! Defines the core language of thought of the model and a simple virtual machine.

use std::fmt::Display;

use crate::lambda::types::LambdaType;
use crate::{Actor, Event, PropertyLabel};

///All binary operations
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum BinOp {
    ///<a,<e,t>> function that returns whether the first argument is the agent of the second
    ///argument.
    AgentOf,
    ///<a,<e,t>> function that returns whether the first argument is the patient of the second
    ///argument.
    PatientOf,
    ///Logical AND
    And,
    ///Logical OR
    Or,
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                BinOp::AgentOf => "AgentOf",
                BinOp::PatientOf => "PatientOf",
                BinOp::And => "&",
                BinOp::Or => "|",
            }
        )
    }
}

impl BinOp {
    fn get_argument_type(&self) -> [&LambdaType; 2] {
        match self {
            BinOp::AgentOf | BinOp::PatientOf => [LambdaType::a(), LambdaType::e()],
            BinOp::And | BinOp::Or => [LambdaType::t(), LambdaType::t()],
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
///All unary operations
pub enum MonOp {
    ///Logical not
    Not,

    ///Takes an actor or event predicate and returns the one present example that has it.
    Iota(ActorOrEvent),
}

impl MonOp {
    fn get_argument_type(&self) -> &LambdaType {
        match self {
            MonOp::Iota(ActorOrEvent::Actor | ActorOrEvent::Event) | MonOp::Not => LambdaType::t(),
        }
    }
}

impl Display for MonOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MonOp::Not => write!(f, "~"),
            MonOp::Iota(ActorOrEvent::Actor) => write!(f, "iota"),
            MonOp::Iota(ActorOrEvent::Event) => write!(f, "iota_e"),
        }
    }
}

///Whether something refers to an actor or event.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[allow(missing_docs)]
pub enum ActorOrEvent {
    Actor,
    Event,
}

impl Display for ActorOrEvent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ActorOrEvent::Actor => write!(f, "a"),
            ActorOrEvent::Event => write!(f, "e"),
        }
    }
}

impl From<ActorOrEvent> for LambdaType {
    fn from(value: ActorOrEvent) -> Self {
        match value {
            ActorOrEvent::Actor => LambdaType::A,
            ActorOrEvent::Event => LambdaType::E,
        }
    }
}

///Any valid constant in the language.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Constant<'a> {
    ///The set of all actors in the [`Scenario`].
    Everyone,
    ///The set of all events in the [`Scenario`].
    EveryEvent,
    ///Truth
    Tautology,
    ///Falsity
    Contradiction,
    ///Any predicate as a set
    Property(PropertyLabel<'a>, ActorOrEvent),
}

impl Display for Constant<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Constant::Everyone => write!(f, "all_a"),
            Constant::EveryEvent => write!(f, "all_e"),
            Constant::Tautology => write!(f, "True"),
            Constant::Contradiction => write!(f, "False"),
            Constant::Property(x, ActorOrEvent::Actor) => write!(f, "pa_{x}"),
            Constant::Property(x, ActorOrEvent::Event) => write!(f, "pe_{x}"),
        }
    }
}

///An enum which represents all possible quantifiers in the language.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum Quantifier {
    ///Universal Quantification
    Universal,
    ///Existential quantification
    Existential,
}

impl Display for Quantifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Quantifier::Universal => write!(f, "every"),
            Quantifier::Existential => write!(f, "some"),
        }
    }
}

///The basic expression type of the language of thought.
///Note that it *does not* include free variables or any of the machinery of the lambda calculus
///which is handled elsewhere.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum Expr<'a> {
    ///A quantified expression. Variables are implemented with `DeBruijn` indices.
    Quantifier {
        ///What kind of quantifier
        quantifier: Quantifier,
        ///The type of bound variable
        var_type: ActorOrEvent,
    },
    ///See [`Actor`]. Written `a_NAME`
    Actor(Actor<'a>),
    ///See [`Event`]. Written `e_N` where `N` is an integer.
    Event(Event),
    ///Any binary function.
    Binary(BinOp),
    ///Any unary function.
    Unary(MonOp),
    ///All constants.
    Constant(Constant<'a>),
}

impl Display for Expr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Quantifier {
                quantifier,
                var_type: ActorOrEvent::Actor,
            } => write!(f, "{quantifier}"),
            Expr::Quantifier {
                quantifier,
                var_type: ActorOrEvent::Event,
            } => write!(f, "{quantifier}_e"),
            Expr::Actor(a) => write!(f, "a_{a}"),
            Expr::Event(e) => write!(f, "e_{e}"),
            Expr::Binary(bin_op) => write!(f, "{bin_op}"),
            Expr::Unary(mon_op) => write!(f, "{mon_op}"),
            Expr::Constant(constant) => write!(f, "{constant}"),
        }
    }
}

//mod parser;
//pub use parser::LambdaParseError;
//pub use parser::parse_executable;

mod lambda_implementation;
pub use lambda_implementation::ConjoiningError;

//#[cfg(feature = "sampling")]
//mod enumerator;

//#[cfg(feature = "sampling")]
//mod mutations;
//
//#[cfg(feature = "sampling")]
//pub use mutations::{
//    Context, LambdaEnumerator, LambdaSampler, PossibleExpressions, TypeAgnosticSampler,
//};

//mod serializations;

#[cfg(test)]
mod tests {
    use crate::{Entity, Scenario, ScenarioDataset, lambda::RootedLambdaPool};
    use std::collections::BTreeMap;

    use super::*;
    use crate::ThetaRoles;

    #[test]
    fn agent_of_and_patient_of() -> anyhow::Result<()> {
        let simple_scenario = Scenario {
            question: vec![],
            actors: vec!["0", "1"],
            thematic_relations: vec![ThetaRoles {
                agent: Some("0"),
                patient: None,
            }],
            properties: BTreeMap::default(),
        };

        let simple_expr = RootedLambdaPool::<Expr>::parse("AgentOf(a_0, e_0)")?;
        assert!(simple_expr.interp(&simple_scenario).unwrap().try_into()?);

        let simple_expr = RootedLambdaPool::<Expr>::parse("PatientOf(a_0, e_0)")?;
        assert!(!bool::try_from(
            simple_expr.interp(&simple_scenario).unwrap()
        )?);
        Ok(())
    }

    #[test]
    fn quantification() -> anyhow::Result<()> {
        let simple_scenario = Scenario {
            question: vec![],
            actors: vec!["0", "1"],
            thematic_relations: vec![
                ThetaRoles {
                    agent: Some("0"),
                    patient: Some("0"),
                },
                ThetaRoles {
                    agent: Some("1"),
                    patient: Some("0"),
                },
            ],
            properties: BTreeMap::default(),
        };

        //For all actors there exists an event such that they are its agent.
        let expr = RootedLambdaPool::<Expr>::parse(
            "every(x, all_a(x),  some_e(y,all_e(y), AgentOf(x,y)))",
        )?;
        assert!(bool::try_from(expr.interp(&simple_scenario).unwrap())?);

        //For all actors there exists an event such that they are its patient.
        let expr = RootedLambdaPool::<Expr>::parse(
            "every(x, all_a(x),  some_e(y,all_e(y), PatientOf(x,y)))",
        )?;
        assert!(!bool::try_from(expr.interp(&simple_scenario).unwrap())?);
        Ok(())
    }

    #[test]
    fn logic() -> anyhow::Result<()> {
        let simple_scenario = Scenario {
            question: vec![],
            actors: vec!["0", "1"],
            thematic_relations: vec![
                ThetaRoles {
                    agent: Some("0"),
                    patient: Some("0"),
                },
                ThetaRoles {
                    agent: Some("1"),
                    patient: Some("0"),
                },
            ],
            properties: BTreeMap::default(),
        };

        for (expr, val) in [
            ("False", false),
            ("True", true),
            ("~True", false),
            ("(~False) | False", true),
            ("(~False) & False", false),
            (
                "every(x, all_a(x), some_e(e, all_e(e), PatientOf(x, e) & True))",
                false,
            ),
        ] {
            assert_eq!(
                bool::try_from(
                    RootedLambdaPool::<Expr>::parse(expr)?
                        .interp(&simple_scenario)
                        .unwrap()
                )?,
                val
            );
        }

        Ok(())
    }

    #[test]
    fn properties() -> anyhow::Result<()> {
        let mut properties = BTreeMap::default();
        properties.insert("1", vec![Entity::Actor("0"), Entity::Actor("1")]);
        properties.insert("534", vec![Entity::Actor("1")]);
        let simple_scenario = Scenario {
            question: vec![],
            actors: vec!["0", "1"],
            thematic_relations: vec![
                ThetaRoles {
                    agent: Some("0"),
                    patient: Some("0"),
                },
                ThetaRoles {
                    agent: Some("1"),
                    patient: Some("0"),
                },
            ],
            properties,
        };
        for (expr, val) in [
            ("every(x, all_a(x), pa_1(x))", true),
            ("some(x, all_a(x), pa_534(x))", true),
        ] {
            assert_eq!(
                bool::try_from(
                    RootedLambdaPool::<Expr>::parse(expr)?
                        .interp(&simple_scenario)
                        .unwrap()
                )?,
                val
            );
        }
        Ok(())
    }

    #[test]
    fn complicated_restrictors() -> anyhow::Result<()> {
        let scenario_a = {
            let mut properties = BTreeMap::default();
            properties.insert("534", vec![Entity::Actor("1")]);
            properties.insert("235", vec![Entity::Event(0)]);
            properties.insert("2", vec![Entity::Actor("0")]);
            Scenario {
                question: vec![],
                actors: vec!["0", "1"],
                thematic_relations: vec![ThetaRoles {
                    agent: Some("1"),
                    patient: Some("0"),
                }],
                properties,
            }
        };

        let scenario_b = {
            let mut properties = BTreeMap::default();
            properties.insert("3", vec![Entity::Actor("1"), Entity::Actor("2")]);
            properties.insert("2", vec![Entity::Actor("1"), Entity::Actor("3")]);
            properties.insert("4", vec![Entity::Event(0)]);
            Scenario {
                question: vec![],
                actors: vec!["0", "1", "2", "3", "4"],
                thematic_relations: vec![ThetaRoles {
                    agent: Some("1"),
                    patient: Some("0"),
                }],
                properties,
            }
        };

        for (expr, val, scenario) in [
            (
                "every(x, pa_534(x), some_e(y, pe_235(y), AgentOf(x, y)))",
                true,
                &scenario_a,
            ),
            (
                "every(x, pa_2(x), some_e(y, pe_235(y), AgentOf(x, y)))",
                false,
                &scenario_a,
            ),
            (
                "every(x, pa_2(x) & pa_3(x), some_e(y, all_e(y), AgentOf(x, y)))",
                true,
                &scenario_b,
            ),
            (
                "every(x, pa_2(x) & pa_3(x), some_e(y, all_e(y), PatientOf(x, y)))",
                false,
                &scenario_b,
            ),
        ] {
            assert_eq!(
                bool::try_from(
                    RootedLambdaPool::<Expr>::parse(expr)?
                        .interp(scenario)
                        .unwrap()
                )?,
                val,
                "{expr} is not {val}",
            );
        }
        Ok(())
    }
    /*

    #[test]
    fn error_handling() -> anyhow::Result<()> {
        let expr = parse_executable("some_e(y,pe_1,PatientOf(a_1,y))")?;

        let a = Scenario {
            question: vec![],
            actors: vec!["1", "0"],
            thematic_relations: vec![ThetaRoles {
                agent: Some("0"),
                patient: Some("1"),
            }],
            properties: vec![("1", vec![Entity::Event(0)])].into_iter().collect(),
        };

        let b = Scenario {
            question: vec![],
            actors: vec!["1"],
            thematic_relations: vec![ThetaRoles {
                agent: Some("1"),
                patient: None,
            }],
            properties: vec![("0", vec![Entity::Event(0)])].into_iter().collect(),
        };
        assert_eq!(
            expr.run(&b, None),
            Err(LanguageTypeError::PresuppositionError)
        );
        expr.run(&a, None)?;

        Ok(())
    }

    #[test]
    fn weird_and_not_behaviour() -> anyhow::Result<()> {
        let scenario = "\"Phil danced\" <John (man), Mary (woman), Susan (woman), Phil (man); {A: Phil (dance)}, {A: Mary (run)}>";

        let labels = ScenarioDataset::parse(scenario)?;

        let a = LanguageExpression::parse("every_e(x,pe_dance,AgentOf(a_Phil,x))")?;
        let b = LanguageExpression::parse("every_e(x,pe_dance,AgentOf(a_Mary,x))")?;
        let c = LanguageExpression::parse(
            "(every_e(x,pe_dance,AgentOf(a_Phil,x)))&~(every_e(x,pe_dance,AgentOf(a_Mary,x)))",
        )?;
        let scenario = labels.iter_scenarios().next().unwrap();
        assert_eq!(a.run(scenario, None)?, LanguageResult::Bool(true));
        assert_eq!(b.run(scenario, None)?, LanguageResult::Bool(false));
        assert_eq!(c.run(scenario, None)?, LanguageResult::Bool(true));

        let pool = LanguageExpression::parse(
            "every_e(x, AgentOf(a_Mary, x), PatientOf(a_Phil, x)) & ~every_e(x, AgentOf(a_John, x), PatientOf(a_Phil, x)) & ~every_e(x, AgentOf(a_Phil, x), PatientOf(a_Phil, x)) & ~every_e(x, AgentOf(a_Sue, x), PatientOf(a_Phil, x))",
        )?;
        let labels = ScenarioDataset::parse(
            "\"Mary loves Phil\" <John (man), Mary (woman), Phil (man), Sue (woman); {A: Mary, P: Phil (loves)}> lambda a x some_e(e, pe_loves, AgentOf(x, e)); lambda a x some_e(e, pe_loves, PatientOf(x, e)); lambda <a,<a,t>> P P(a_Phil, a_Mary) & ~P(a_John, a_Mary) & ~P(a_Mary, a_Mary) & ~P(a_Sue, a_Mary); lambda <a,t> P P(a_Mary) & ~P(a_John) & ~P(a_Phil) & ~P(a_Sue)",
        )?;

        let config = ExecutionConfig::default().allow_empty_quantification();
        let scenario = labels.iter_scenarios().next().unwrap();

        pool.run(scenario, Some(config))?;

        let pool = LanguageExpression::parse(
            "some_e(x, all_e, AgentOf(a_John, x) & PatientOf(a_Mary, x) & pe_helps(x))",
        )?;
        let labels = ScenarioDataset::parse(
            "\"John helps Mary\" <John (man), Phil (man), Mary (woman); {A: John (sleeps)}, {A: John, P: Mary (helps)}> lambda a x AgentOf(x, e_1); lambda <a, t> P P(a_John) & ~P(a_Phil) & ~P(a_Mary); lambda a x PatientOf(x, e_1); lambda <a, <a, t>> P P(a_Mary, a_John) & ~P(a_John, a_John) & ~P(a_Phil, a_John)",
        )?;

        let config = ExecutionConfig::default().allow_empty_quantification();
        let scenario = labels.iter_scenarios().next().unwrap();

        assert_eq!(
            pool.run(scenario, Some(config))?,
            LanguageResult::Bool(true)
        );

        Ok(())
    }

    #[test]
    fn iota_tests() -> anyhow::Result<()> {
        let scenario = "\"The man danced\" <John (man), Mary (woman), Susan (woman); {A: John (dance)}, {A: Mary (run)}>";

        let labels = ScenarioDataset::parse(scenario)?;

        let a = LanguageExpression::parse("every_e(x,pe_dance,AgentOf(iota(x, pa_man(x)),x))")?;
        let b = LanguageExpression::parse("every_e(x,pe_dance,AgentOf(iota(x, pa_woman(x)),x))")?;
        let c = LanguageExpression::parse("every_e(x,pe_dance,AgentOf(iota(x, pa_red(x)),x))")?;

        let d = LanguageExpression::parse("iota_e(x, pe_dance(x))")?;
        let scenario = labels.iter_scenarios().next().unwrap();
        assert_eq!(
            a.to_string(),
            "every_e(x, pe_dance, AgentOf(iota(y, pa_man(y)), x))"
        );
        assert_eq!(a.run(scenario, None)?, LanguageResult::Bool(true));
        assert_eq!(
            b.run(scenario, None),
            Err(LanguageTypeError::PresuppositionError)
        );
        assert_eq!(
            c.run(scenario, None),
            Err(LanguageTypeError::PresuppositionError)
        );
        assert_eq!(d.run(scenario, None), Ok(LanguageResult::Event(0)));

        Ok(())
    }*/
}
