//! Fuzz tests for the parsers: check that anything the crate prints can be parsed back into an
//! equal value, and hunt for inputs that should parse but don't.

use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use std::collections::BTreeMap;

use simple_semantics::{
    Scenario, ScenarioDataset, ThetaRoles,
    lambda::{FreeVar, Literal, RootedLambdaPool, types::LambdaType},
    language::{ActorOrEvent, Constant, Expr},
};

fn base_expressions() -> Vec<Expr<'static>> {
    let mut expressions = vec![
        Expr::Constant(Constant::Literal(Literal::Actor("John"))),
        Expr::Constant(Constant::Literal(Literal::Event(3))),
        Expr::Constant(Constant::Literal(Literal::ActorSet(vec!["John", "Mary"]))),
        Expr::Constant(Constant::Property("a", ActorOrEvent::Actor)),
        Expr::Constant(Constant::Property("e", ActorOrEvent::Event)),
    ];
    expressions.extend(Expr::basic_ops().iter().cloned());
    expressions
}

fn free_vars() -> Vec<(FreeVar<'static>, LambdaType)> {
    vec![
        (
            FreeVar::Named("f"),
            LambdaType::from_string("<a,t>").unwrap(),
        ),
        (
            FreeVar::Named("g"),
            LambdaType::from_string("<<a,t>,t>").unwrap(),
        ),
        (FreeVar::Named("h"), LambdaType::from_string("a").unwrap()),
        (
            FreeVar::Anonymous(0),
            LambdaType::from_string("<e,t>").unwrap(),
        ),
    ]
}

#[test]
fn random_expressions_round_trip() {
    let mut rng = ChaCha8Rng::seed_from_u64(42);
    for i in 0..300 {
        let pool = RootedLambdaPool::<Expr>::random_up_to(
            None,
            8,
            &base_expressions(),
            &free_vars(),
            &mut rng,
        )
        .unwrap_or_else(|e| panic!("generation failed on iteration {i}: {e}"));
        let printed = pool.to_string();
        let reparsed = RootedLambdaPool::<Expr>::parse(&printed).unwrap_or_else(|e| {
            panic!("display output failed to parse (iteration {i}):\n{printed}\n{e}")
        });
        assert_eq!(
            pool, reparsed,
            "re-parsed pool differs from original (iteration {i}):\n{printed}"
        );
        assert_eq!(
            reparsed.to_string(),
            printed,
            "display is not idempotent (iteration {i}):\n{printed}"
        );
    }
}

#[test]
fn event_literal_overflow_is_an_error_not_a_panic() {
    assert!(Literal::parse("e_255").is_ok());
    assert!(RootedLambdaPool::<Expr>::parse("pe_run(e_255)").is_ok());
    let err = Literal::parse("e_256").expect_err("e_256 should not parse");
    assert!(err.to_string().contains("too big"));
    assert!(RootedLambdaPool::<Expr>::parse("pe_run(e_256)").is_err());
    assert!(RootedLambdaPool::<Expr>::parse("{e_256}(x)").is_err());
}

#[test]
fn empty_scenario_parses_and_round_trips() -> anyhow::Result<()> {
    let scenario = Scenario::parse("<>")?;
    assert!(scenario.actors().is_empty());
    assert!(scenario.thematic_relations().is_empty());
    assert!(scenario.questions().is_empty());
    assert_eq!(scenario.to_string(), "<>");
    assert_eq!(Scenario::parse(&scenario.to_string())?, scenario);
    Ok(())
}

fn events_with_properties(n: usize) -> String {
    let events = (0..n)
        .map(|i| if i == 0 { "{}" } else { "{A: a (run)}" })
        .collect::<Vec<_>>()
        .join(", ");
    format!("<a; {events}>")
}

#[test]
fn too_many_events_is_a_parse_error_not_a_panic() {
    let max = events_with_properties(256);
    assert!(Scenario::parse(&max).is_ok());
    let err =
        Scenario::parse(&events_with_properties(257)).expect_err("257 events should not parse");
    assert!(err.to_string().contains("at most 256 events"));
}

#[test]
#[should_panic(expected = "A scenario can have at most 256 events")]
fn too_many_events_panics_in_new() {
    let mut relations = vec![ThetaRoles::default(); 257];
    relations[0] = ThetaRoles {
        agent: Some("a"),
        patient: None,
    };
    let _ = Scenario::new(vec!["a"], relations, BTreeMap::default());
}

#[test]
fn empty_lemmas_are_pruned() -> anyhow::Result<()> {
    let dataset = ScenarioDataset::parse("\"John  ran\" <John; {A: John (run)}>\n")?;
    assert_eq!(dataset.lemmas(), ["John", "ran"]);
    let (_, sentence) = dataset.iter().next().unwrap();
    assert_eq!(sentence, &vec!["John", "ran"]);
    Ok(())
}

#[test]
fn scenario_files_round_trip() -> anyhow::Result<()> {
    for file in [
        "tests/resources/men.scenario",
        "tests/resources/testfile.scenario",
    ] {
        let s = std::fs::read_to_string(file)?;
        let dataset = ScenarioDataset::parse(&s)?;
        for (scenario, _) in dataset.iter() {
            let printed = scenario.to_string();
            let reparsed = Scenario::parse(&printed)?;
            assert_eq!(
                scenario.questions(),
                reparsed.questions(),
                "scenario questions differ after round trip:\n{printed}"
            );
            assert_eq!(
                scenario.thematic_relations(),
                reparsed.thematic_relations(),
                "scenario events differ after round trip:\n{printed}"
            );
            assert_eq!(
                scenario.properties(),
                reparsed.properties(),
                "scenario properties differ after round trip:\n{printed}"
            );
            assert_eq!(&scenario.actors(), &reparsed.actors().to_vec());
        }
    }
    Ok(())
}
