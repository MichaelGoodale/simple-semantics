use divan::AllocProfiler;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use simple_semantics::{
    LanguageExpression, ScenarioDataset,
    lambda::{
        RootedLambdaPool,
        types::{LambdaType, TypeParsingError},
    },
    language::PossibleExpressions,
};

#[global_allocator]
static ALLOC: AllocProfiler = AllocProfiler::system();

fn main() {
    // Run registered benchmarks.
    divan::main();
}

// Register a `fibonacci` function and benchmark it over multiple cases.
#[divan::bench(args = ["a", "<a,t>", "<<a,<t,t>>"])]
fn parsing(s: &str) -> Result<LambdaType, TypeParsingError> {
    LambdaType::from_string(s)
}

#[divan::bench]
fn constant_types() -> [&'static LambdaType; 6] {
    [
        LambdaType::a(),
        LambdaType::t(),
        LambdaType::e(),
        LambdaType::et(),
        LambdaType::eet(),
        LambdaType::at(),
    ]
}

#[divan::bench(args = [("a", "<a,t>"), ("<a,<a,<e,t>>>", "<<a,<a,<e,t>>>,<a,<e,t>>>")])]
fn complicated_application(bencher: divan::Bencher, args: (&str, &str)) {
    let (alpha, beta) = divan::black_box((
        LambdaType::from_string(args.0).unwrap(),
        LambdaType::from_string(args.1).unwrap(),
    ));

    bencher.bench(|| beta.apply(&alpha).unwrap().clone())
}
#[divan::bench]
fn random_types() {
    let mut rng = ChaCha8Rng::seed_from_u64(32);
    for _ in 0..100 {
        LambdaType::random(&mut rng);
    }
}

#[divan::bench]
fn random(bencher: divan::Bencher) {
    let actors = &["1", "2", "3", "4", "5"];
    let actor_properties = &["1", "2", "3", "4", "5"];
    let event_properties = &["1", "2", "3", "4", "5"];

    bencher.bench(|| {
        let mut rng = ChaCha8Rng::from_os_rng();
        let t = LambdaType::random_no_e(&mut rng);
        let poss = PossibleExpressions::new(actors, actor_properties, event_properties);
        RootedLambdaPool::random_expr(&t, &poss, &mut rng)
    });
}

#[divan::bench(args = ["every_e(x,pe_dance,AgentOf(a_Phil,x))",
"every_e(x,pe_dance,AgentOf(a_Mary,x))",
"(every_e(x,pe_dance,AgentOf(a_Phil,x)))&~(every_e(x,pe_dance,AgentOf(a_Mary,x)))"])]
fn to_string(bencher: divan::Bencher, s: &str) {
    let a = LanguageExpression::parse(s).unwrap();
    bencher.bench(|| a.to_string());
}

#[divan::bench(args = ["lambda a z (every_e(x,pe_dance,AgentOf(z,x)))",
"lambda <a,<e,t>> P (every_e(x,pe_dance, (P(a_Mary))(x)))",
"lambda a r ((every_e(x,pe_dance,AgentOf(r,x)))&~(every_e(x,pe_dance,AgentOf(a_Mary,x))))"])]
fn lambda_string(bencher: divan::Bencher, s: &str) {
    let a = RootedLambdaPool::parse(s).unwrap();
    bencher.bench(|| a.to_string());
}

#[divan::bench]
fn scenarios(bencher: divan::Bencher) {
    let scenario = "\"Phil danced\" <John (man), Mary (woman), Susan (woman), Phil (man); {A: Phil (dance)}, {A: Mary (run)}>";

    let labels = ScenarioDataset::parse(scenario).unwrap();

    let a = LanguageExpression::parse("every_e(x,pe_dance,AgentOf(a_Phil,x))").unwrap();
    let b = LanguageExpression::parse("every_e(x,pe_dance,AgentOf(a_Mary,x))").unwrap();
    let c = LanguageExpression::parse(
        "(every_e(x,pe_dance,AgentOf(a_Phil,x)))&~(every_e(x,pe_dance,AgentOf(a_Mary,x)))",
    )
    .unwrap();
    let scenario = labels.iter_scenarios().next().unwrap();
    bencher.bench(|| {
        a.run(scenario, None).unwrap();
        b.run(scenario, None).unwrap();
        c.run(scenario, None).unwrap();
    });
}

#[divan::bench]
fn reduction(bencher: divan::Bencher) {
    let t_to_t = [
        "lambda t phi ~(phi | pa_woman(a_Phil) | (some_e(x, pe_laughs, pe_likes(x)) & ~some(x, pa_woman, phi))) | pa_woman(a_Mary) | every_e(x, pe_likes, pe_runs(x)) | pa_man(a_Mary) | pa_woman(a_Sue) | every(x, lambda a y phi, pa_man(a_Phil) & ~pa_woman(x) & some(y, all_a, phi | (some_e(z, pe_runs, PatientOf(a_John, z)) & (~pa_man(a_Sue) | ~pa_man(y)))))",
        "lambda t phi every_e(x, pe_sleeps, pe_sleeps(x) & (pa_woman(a_John) | pe_likes(x)))",
        "lambda t phi ~some(x, all_a, ~some_e(y, pe_loves, PatientOf(x, y)) & (~every_e(y, pe_helps, phi) | some(y, pa_man, ~~pa_woman(x)))) | some_e(x, all_e, pe_runs(x))",
    ]
    .map(|s| RootedLambdaPool::parse(s).unwrap());
    let t = RootedLambdaPool::parse("every_e(x, pe_runs, pe_laughs(x) & pa_woman(a_Sue))").unwrap();

    bencher.bench(|| {
        let mut t = t.clone();
        for x in t_to_t.iter().cycle().take(7500).cloned() {
            t = t.merge(x).unwrap();
        }
        t.reduce().unwrap();
    });
}
