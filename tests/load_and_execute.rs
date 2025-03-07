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
