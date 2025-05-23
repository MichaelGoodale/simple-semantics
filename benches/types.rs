use divan::AllocProfiler;
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use simple_semantics::{
    lambda::{RootedLambdaPool, types::LambdaType},
    language::Expr,
};

#[global_allocator]
static ALLOC: AllocProfiler = AllocProfiler::system();

fn main() {
    // Run registered benchmarks.
    divan::main();
}

// Register a `fibonacci` function and benchmark it over multiple cases.
#[divan::bench(args = ["a", "<a,t>", "<<a,<t,t>>"])]
fn parsing(s: &str) -> anyhow::Result<LambdaType> {
    LambdaType::from_string(s)
}

#[divan::bench]
fn constant_types() -> [LambdaType; 6] {
    [
        LambdaType::A,
        LambdaType::T,
        LambdaType::E,
        LambdaType::et(),
        LambdaType::eet(),
        LambdaType::at(),
    ]
}

#[divan::bench(args = [("a", "<a,t>"), ("<a,<a,<e,t>>>", "<<a,<a,<e,t>>>,<a,<e,t>>>")])]
fn complicated_application(args: (&str, &str)) -> LambdaType {
    let (alpha, beta) = divan::black_box((
        LambdaType::from_string(args.0).unwrap(),
        LambdaType::from_string(args.1).unwrap(),
    ));

    beta.apply(&alpha).unwrap()
}
#[divan::bench]
fn random_types() {
    let mut rng = divan::black_box(ChaCha8Rng::seed_from_u64(32));
    for _ in 0..100 {
        LambdaType::random(&mut rng);
    }
}

#[divan::bench]
fn random_exprs() {
    let mut rng = divan::black_box(ChaCha8Rng::seed_from_u64(32));
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
