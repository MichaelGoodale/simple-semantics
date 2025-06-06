use divan::AllocProfiler;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use simple_semantics::{
    LabelledScenarios, LanguageExpression,
    lambda::{
        RootedLambdaPool,
        types::{LambdaType, TypeParsingError},
    },
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
fn random_exprs() {
    let mut rng = ChaCha8Rng::seed_from_u64(32);
    let actors = &[1, 2, 3, 4, 5];
    let actor_properties = &[1, 2, 3, 4, 5];
    let event_properties = &[1, 2, 3, 4, 5];

    for _ in 0..100 {
        RootedLambdaPool::random_expr(
            LambdaType::at(),
            actors.as_slice(),
            actor_properties.as_slice(),
            event_properties.as_slice(),
            None,
            &mut rng,
        )
        .unwrap();
    }
}

#[divan::bench(args = ["every_e(x,pe_dance,AgentOf(a_Phil,x))",
"every_e(x,pe_dance,AgentOf(a_Mary,x))",
"(every_e(x,pe_dance,AgentOf(a_Phil,x)))&~(every_e(x,pe_dance,AgentOf(a_Mary,x)))"])]
fn to_string(bencher: divan::Bencher, s: &str) {
    let scenario = "\"Phil danced\" <John (man), Mary (woman), Susan (woman), Phil (man); {A: Phil (dance)}, {A: Mary (run)}>";

    let mut labels = LabelledScenarios::parse(scenario).unwrap();
    let a = LanguageExpression::parse(s, &mut labels).unwrap();
    bencher.bench(|| a.to_string());
}

#[divan::bench(args = ["lambda a z (every_e(x,pe_dance,AgentOf(z,x)))",
"lambda <a,<a,t>> P (every_e(x,pe_dance, (P(a_Mary))(x)))",
"lambda a r ((every_e(x,pe_dance,AgentOf(r,x)))&~(every_e(x,pe_dance,AgentOf(a_Mary,x))))"])]
fn lambda_string(bencher: divan::Bencher, s: &str) {
    let scenario = "\"Phil danced\" <John (man), Mary (woman), Susan (woman), Phil (man); {A: Phil (dance)}, {A: Mary (run)}>";

    let mut labels = LabelledScenarios::parse(scenario).unwrap();
    let a = RootedLambdaPool::parse(s, &mut labels).unwrap();
    bencher.bench(|| a.to_string());
}

#[divan::bench]
fn scenarios(bencher: divan::Bencher) {
    let scenario = "\"Phil danced\" <John (man), Mary (woman), Susan (woman), Phil (man); {A: Phil (dance)}, {A: Mary (run)}>";

    let mut labels = LabelledScenarios::parse(scenario).unwrap();

    let a =
        LanguageExpression::parse("every_e(x,pe_dance,AgentOf(a_Phil,x))", &mut labels).unwrap();
    let b =
        LanguageExpression::parse("every_e(x,pe_dance,AgentOf(a_Mary,x))", &mut labels).unwrap();
    let c = LanguageExpression::parse(
        "(every_e(x,pe_dance,AgentOf(a_Phil,x)))&~(every_e(x,pe_dance,AgentOf(a_Mary,x)))",
        &mut labels,
    )
    .unwrap();
    let scenario = labels.iter_scenarios().next().unwrap();
    bencher.bench(|| {
        a.run(scenario).unwrap();
        b.run(scenario).unwrap();
        c.run(scenario).unwrap();
    });
}
