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
    let mut parsed_data = LabelledScenarios::from_file(path)?;

    let scenarios = vec![
        Scenario::new(
            vec![0],
            vec![ThetaRoles {
                agent: Some(0),
                patient: None,
            }],
            HashMap::from_iter([(0, vec![Entity::Event(0)])]),
        ),
        Scenario::new(
            vec![1],
            vec![ThetaRoles {
                agent: Some(1),
                patient: None,
            }],
            HashMap::from_iter([(0, vec![Entity::Event(0)])]),
        ),
        Scenario::new(
            vec![1, 0],
            vec![ThetaRoles {
                agent: Some(0),
                patient: Some(1),
            }],
            HashMap::from_iter([(1, vec![Entity::Event(0)])]),
        ),
    ];

    let data = LabelledScenarios::new(
        scenarios,
        ["John ran", "Mary ran", "John saw Mary"]
            .map(|x| x.split(" ").map(ToString::to_string).collect::<Vec<_>>())
            .into_iter()
            .collect::<Vec<_>>(),
        ["John", "Mary", "ran", "saw"]
            .map(ToString::to_string)
            .into_iter()
            .collect(),
        HashMap::from_iter([("run", 0), ("see", 1)].map(|(x, y)| (x.to_string(), y))),
        HashMap::from_iter([("John", 0), ("Mary", 1)].map(|(x, y)| (x.to_string(), y))),
        HashMap::default(),
    );

    assert_eq!(data, parsed_data);

    let executable = simple_semantics::parse_executable("AgentOf(a_John, e0)", &mut parsed_data)?;
    assert_eq!(
        parsed_data
            .iter_scenarios()
            .map(|x| executable.run(x))
            .collect::<Vec<_>>(),
        [true, false, true].map(LanguageResult::Bool).to_vec()
    );

    Ok(())
}

#[test]
fn lambda_stuff() -> anyhow::Result<()> {
    let path = get_resource_path()?.join("men.scenario");
    let mut parsed_data = LabelledScenarios::from_file(path)?;

    let executable = simple_semantics::parse_executable(
        "every(x,p_man, some(y, all_e, AgentOf(x, y) & p_sleep(y)))",
        &mut parsed_data,
    )?;
    assert_eq!(
        parsed_data
            .iter_scenarios()
            .map(|x| executable.run(x))
            .collect::<Vec<_>>(),
        [true, false, true, false]
            .map(LanguageResult::Bool)
            .to_vec()
    );

    let man = "lambda e x (p_man(x))";
    let woman = "lambda e x (p_woman(x))";
    let sleeps = "lambda e x (some(y, all_e, AgentOf(x, y) & p_sleep(y)))";
    let every = "lambda <e,t> p(lambda <e,t> q(every(x, p(x), q(x))))";
    let and = "lambda t psi (lambda t phi (psi & phi))";
    let not = "lambda t phi (~phi)";

    let every_man_sleeps = format!("(({every})({man}))({sleeps})");
    println!("{every_man_sleeps}");
    let executable =
        simple_semantics::parse_executable(every_man_sleeps.as_str(), &mut parsed_data)?;
    assert_eq!(
        parsed_data
            .iter_scenarios()
            .map(|x| executable.run(x))
            .collect::<Vec<_>>(),
        [true, false, true, false]
            .map(LanguageResult::Bool)
            .to_vec()
    );

    let not_every_woman_sleeps = format!("({not})((({every})({woman}))({sleeps}))");
    let statement = format!("(({and})({every_man_sleeps}))({not_every_woman_sleeps})");
    println!("{statement}");
    let executable = simple_semantics::parse_executable(statement.as_str(), &mut parsed_data)?;
    println!("{executable}");
    assert_eq!(
        parsed_data
            .iter_scenarios()
            .map(|x| executable.run(x))
            .collect::<Vec<_>>(),
        [true, false, false, false]
            .map(LanguageResult::Bool)
            .to_vec()
    );

    Ok(())
}
