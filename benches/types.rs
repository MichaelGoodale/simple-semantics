use divan::AllocProfiler;
use rand::{RngExt, SeedableRng};
use rand_chacha::ChaCha8Rng;
use simple_semantics::{
    ScenarioDataset,
    lambda::{
        RootedLambdaPool,
        enumerator::Generator,
        types::{LambdaType, TypeParsingError},
    },
    language::Expr,
};

#[global_allocator]
static ALLOC: AllocProfiler = AllocProfiler::system();

fn main() {
    // Run registered benchmarks.
    divan::main();
}

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

fn expressions_bencher(bencher: divan::Bencher, t: LambdaType, max_size: usize) {
    let scenario = simple_semantics::Scenario::parse(
        "<John, Mary, Susan, Phil, Sue (man);{A: John,P: Mary (likes)},{A: Mary,P: Susan (likes)},{A: Susan,P: Phil (likes)},{A: Phil,P: Sue (likes)}>",
    )
    .unwrap();
    let mut expressions = scenario.scenario_ops();
    expressions.extend(Expr::basic_ops().iter().cloned());

    bencher.bench(|| {
        let mut generator: Generator<Expr> = Generator::new(expressions.clone(), vec![]);
        generator.enumerate_or_generate(t.clone(), max_size);
        generator.enumerate(&t, max_size).unwrap().len()
    });
}

#[divan::bench]
fn enumerate(bencher: divan::Bencher) {
    expressions_bencher(bencher, LambdaType::T, 5);
}

#[divan::bench]
fn alt_enumerate(bencher: divan::Bencher) {
    expressions_bencher(bencher, LambdaType::from_string("<a,<a,t>>").unwrap(), 5);
}

#[divan::bench(args = ["every_e(x,pe_dance(x),AgentOf(a_Phil,x))",
"every_e(x,pe_dance(x),AgentOf(a_Mary,x))",
"(every_e(x,pe_dance(x),AgentOf(a_Phil,x)))&~(every_e(x,pe_dance(x),AgentOf(a_Mary,x)))"])]
fn to_string(bencher: divan::Bencher, s: &str) {
    let a: RootedLambdaPool<Expr> = RootedLambdaPool::parse(s).unwrap();
    bencher.bench(|| a.to_string());
}

#[divan::bench(args = ["lambda a z (every_e(x,pe_dance(x),AgentOf(z,x)))",
"lambda <a,t> P (P(a_Mary) & ~P(a_Phil))",
"lambda a r ((every_e(x,pe_dance(x),AgentOf(r,x)))&~(every_e(x,pe_dance(x),AgentOf(a_Mary,x))))"])]
fn lambda_string(bencher: divan::Bencher, s: &str) {
    let a: RootedLambdaPool<Expr> = RootedLambdaPool::parse(s).unwrap();
    bencher.bench(|| a.to_string());
}

#[divan::bench]
fn scenarios(bencher: divan::Bencher) {
    let scenario = "\"Phil danced\" <John (man), Mary (woman), Susan (woman), Phil (man); {A: Phil (dance)}, {A: Mary (run)}>";

    let labels = ScenarioDataset::parse(scenario).unwrap();

    let a: RootedLambdaPool<Expr> =
        RootedLambdaPool::parse("every_e(x,pe_dance(x),AgentOf(a_Phil,x))").unwrap();
    let b: RootedLambdaPool<Expr> =
        RootedLambdaPool::parse("every_e(x,pe_dance(x),AgentOf(a_Mary,x))").unwrap();
    let c: RootedLambdaPool<Expr> = RootedLambdaPool::parse(
        "(every_e(x,pe_dance(x),AgentOf(a_Phil,x)))&~(every_e(x,pe_dance(x),AgentOf(a_Mary,x)))",
    )
    .unwrap();
    let scenario = labels.iter_scenarios().next().unwrap();
    bencher.bench(|| {
        a.interp(scenario).unwrap();
        b.interp(scenario).unwrap();
        c.interp(scenario).unwrap();
    });
}

#[divan::bench]
fn reduction(bencher: divan::Bencher) {
    let t_to_t = [
        "lambda t phi ~(phi | pa_woman(a_Phil) | (some_e(x, pe_laughs(x), pe_likes(x)) & ~some(x, pa_woman(x), phi))) | pa_woman(a_Mary) | every_e(x, pe_likes(x), pe_runs(x)) | pa_man(a_Mary) | pa_woman(a_Sue) | every(x, all_a(x), pa_man(a_Phil) & ~pa_woman(x) & some(y, all_a(y), phi | (some_e(z, pe_runs(z), PatientOf(a_John, z)) & (~pa_man(a_Sue) | ~pa_man(y)))))",
        "lambda t phi every_e(x, pe_sleeps(x), pe_sleeps(x) & (pa_woman(a_John) | pe_likes(x)))",
        "lambda t phi ~some(x, all_a(x), ~some_e(y, pe_loves(y), PatientOf(x, y)) & (~every_e(y, pe_helps(y), phi) | some(y, pa_man(y), ~~pa_woman(x)))) | some_e(x, all_e(x), pe_runs(x))",
    ]
    .map(|s| RootedLambdaPool::<Expr>::parse(s).unwrap());
    let t: RootedLambdaPool<Expr> =
        RootedLambdaPool::parse("every_e(x, pe_runs(x), pe_laughs(x) & pa_woman(a_Sue))").unwrap();

    bencher.bench(|| {
        let mut t = t.clone();
        for x in t_to_t.iter().cycle().take(7500).cloned() {
            t = t.merge(x).unwrap();
        }
        t.reduce().unwrap();
    });
}

#[divan::bench]
fn ordering(bencher: divan::Bencher) {
    let scenario = simple_semantics::Scenario::parse(
        "<John, Mary (man);{A: John,P: Mary (likes)},{A: Mary,P: John (likes)}>",
    )
    .unwrap();
    let mut expressions = scenario.scenario_ops();
    expressions.extend(Expr::basic_ops().iter().cloned());
    let mut generator: Generator<Expr> = Generator::new(expressions, vec![]);
    let pools = generator
        .enumerate_or_generate(LambdaType::T, 5)
        .into_iter()
        .map(|x| generator.to_rooted_lambda_pool(x).unwrap())
        .collect::<Vec<_>>();
    let mut rng = ChaCha8Rng::seed_from_u64(32);
    let comparisons = (0..1000)
        .map(|_| {
            (
                rng.random_range(0..pools.len()),
                rng.random_range(0..pools.len()),
            )
        })
        .collect::<Vec<_>>();
    bencher.bench(|| {
        for (a, b) in comparisons.iter().copied() {
            let _ord = pools[a].cmp(&pools[b]);
        }
    });
}
