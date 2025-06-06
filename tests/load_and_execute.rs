use std::{
    collections::HashMap,
    path::{Path, PathBuf},
};

use simple_semantics::{Entity, LabelledScenarios, LanguageResult, Scenario, ThetaRoles};

fn get_resource_path() -> anyhow::Result<PathBuf> {
    let cargo_path = std::env::var("CARGO_MANIFEST_DIR")?;
    Ok(Path::new(&cargo_path).join("tests").join("resources"))
}

#[test]
fn load_dataset() -> anyhow::Result<()> {
    let path = get_resource_path()?.join("testfile.scenario");
    let file = std::fs::read_to_string(path)?;
    let parsed_data = LabelledScenarios::parse(&file)?;

    let scenarios = vec![
        Scenario::new(
            vec!["John"],
            vec![ThetaRoles {
                agent: Some("John"),
                patient: None,
            }],
            HashMap::from_iter([("run", vec![Entity::Event(0)])]),
        ),
        Scenario::new(
            vec!["Mary"],
            vec![ThetaRoles {
                agent: Some("Mary"),
                patient: None,
            }],
            HashMap::from_iter([("run", vec![Entity::Event(0)])]),
        ),
        Scenario::new(
            vec!["Mary", "John"],
            vec![ThetaRoles {
                agent: Some("John"),
                patient: Some("Mary"),
            }],
            HashMap::from_iter([("see", vec![Entity::Event(0)])]),
        ),
    ];

    let data = LabelledScenarios::new(
        scenarios,
        ["John ran", "Mary ran", "John saw Mary"]
            .map(|x| x.split(" ").collect::<Vec<_>>())
            .into_iter()
            .collect::<Vec<_>>(),
        ["John", "Mary", "ran", "saw"].into_iter().collect(),
    );

    assert_eq!(data, parsed_data);

    let executable = simple_semantics::parse_executable("AgentOf(a_John, e0)")?;
    assert_eq!(
        parsed_data
            .iter_scenarios()
            .map(|x| executable.run(x).unwrap())
            .collect::<Vec<_>>(),
        [true, false, true].map(LanguageResult::Bool).to_vec()
    );

    Ok(())
}

#[test]
fn lambda_stuff() -> anyhow::Result<()> {
    let path = get_resource_path()?.join("men.scenario");
    let file = std::fs::read_to_string(path)?;
    let parsed_data = LabelledScenarios::parse(&file)?;

    let executable = simple_semantics::parse_executable(
        "every(x,pa_man, some_e(y, all_e, AgentOf(x, y) & pe_sleep(y)))",
    )?;
    assert_eq!(
        parsed_data
            .iter_scenarios()
            .map(|x| executable.run(x).unwrap())
            .collect::<Vec<_>>(),
        [true, false, true, false]
            .map(LanguageResult::Bool)
            .to_vec()
    );

    let man = "lambda a x (pa_man(x))";
    let woman = "lambda a x (pa_woman(x))";
    let sleeps = "lambda a x (some_e(y, all_e, AgentOf(x, y) & pe_sleep(y)))";
    let every = "lambda <a,t> p(lambda <a,t> q(every(x, p(x), q(x))))";
    let and = "lambda t psi (lambda t phi (psi & phi))";
    let not = "lambda t phi (~phi)";

    let every_man_sleeps = format!("(({every})({man}))({sleeps})");
    println!("{every_man_sleeps}");
    let executable = simple_semantics::parse_executable(every_man_sleeps.as_str())?;
    assert_eq!(
        parsed_data
            .iter_scenarios()
            .map(|x| executable.run(x).unwrap())
            .collect::<Vec<_>>(),
        [true, false, true, false]
            .map(LanguageResult::Bool)
            .to_vec()
    );

    let not_every_woman_sleeps = format!("({not})((({every})({woman}))({sleeps}))");
    let statement = format!("(({and})({every_man_sleeps}))({not_every_woman_sleeps})");
    println!("{statement}");
    let executable = simple_semantics::parse_executable(statement.as_str())?;
    println!("{executable}");
    assert_eq!(
        parsed_data
            .iter_scenarios()
            .map(|x| executable.run(x).unwrap())
            .collect::<Vec<_>>(),
        [true, false, false, false]
            .map(LanguageResult::Bool)
            .to_vec()
    );

    Ok(())
}
