use std::{
    cmp::Reverse,
    collections::{BinaryHeap, VecDeque},
    fmt::Debug,
};

use ahash::HashMap;
use chumsky::container::Container;
use rand::{
    Rng,
    distr::{Distribution, weighted::WeightedIndex},
    seq::{IndexedRandom, IteratorRandom},
};
use thiserror::Error;

use super::*;
use crate::lambda::{
    LambdaError, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool,
    types::{LambdaType, TypeError},
};

mod context;
mod samplers;
use context::Context;
use samplers::PossibleExpr;
pub use samplers::PossibleExpressions;

#[derive(Debug, Error, Clone)]
pub struct ExprOrTypeError();

impl Display for ExprOrTypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "This ExprOrType is not an Expr!")
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum ExprOrType<'src, T: LambdaLanguageOfThought> {
    Type {
        lambda_type: LambdaType,
        parent: Option<usize>,
        is_app_subformula: bool,
        reset: Option<usize>,
    },
    Expr {
        lambda_expr: LambdaExpr<'src, T>,
        parent: Option<usize>,
    },
}

impl<'src, T: LambdaLanguageOfThought> TryFrom<ExprOrType<'src, T>> for LambdaExpr<'src, T> {
    type Error = ExprOrTypeError;

    fn try_from(value: ExprOrType<'src, T>) -> Result<Self, Self::Error> {
        match value {
            ExprOrType::Type { .. } => Err(ExprOrTypeError()),
            ExprOrType::Expr { lambda_expr, .. } => Ok(lambda_expr),
        }
    }
}

impl<'src, T: LambdaLanguageOfThought> ExprOrType<'src, T> {
    fn parent(&self) -> Option<usize> {
        match self {
            ExprOrType::Type { parent, .. } | ExprOrType::Expr { parent, .. } => *parent,
        }
    }

    fn is_type(&self) -> bool {
        matches!(self, ExprOrType::Type { .. })
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct UnfinishedLambdaPool<'src, T: LambdaLanguageOfThought> {
    pool: Vec<ExprOrType<'src, T>>,
}

impl<'src, T: LambdaLanguageOfThought> Default for UnfinishedLambdaPool<'src, T> {
    fn default() -> Self {
        Self { pool: vec![] }
    }
}

impl<'src, T: LambdaLanguageOfThought + Clone> UnfinishedLambdaPool<'src, T> {
    fn add_expr<'a>(&mut self, expr: PossibleExpr<'a, 'src, T>, c: &mut Context, t: &LambdaType) {
        let (mut lambda_expr, app_details) = expr.into_expr();
        c.depth += 1;
        c.open_nodes += lambda_expr.n_children();
        c.open_nodes -= 1;
        let parent = self.pool[c.position].parent();
        match &mut lambda_expr {
            LambdaExpr::Lambda(body, arg) => {
                c.add_lambda(arg);
                *body = LambdaExprRef(self.pool.len() as u32);
                self.pool.push(ExprOrType::Type {
                    lambda_type: t.rhs().unwrap().clone(),
                    parent: Some(c.position),
                    is_app_subformula: false,
                    reset: None,
                })
            }
            LambdaExpr::BoundVariable(b, _) => {
                c.use_bvar(*b);
            }
            LambdaExpr::FreeVariable(..) => (),
            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                *subformula = LambdaExprRef(self.pool.len() as u32);
                *argument = LambdaExprRef((self.pool.len() + 1) as u32);
                let (subformula, argument) = app_details.unwrap();
                self.pool.push(ExprOrType::Type {
                    lambda_type: subformula,
                    parent: Some(c.position),
                    is_app_subformula: true,
                    reset: None,
                });
                self.pool.push(ExprOrType::Type {
                    lambda_type: argument,
                    parent: Some(c.position),
                    is_app_subformula: false,
                    reset: None,
                });
            }
            LambdaExpr::LanguageOfThoughtExpr(e) => {
                let children_start = self.pool.len();
                if let Some(t) = e.var_type() {
                    c.add_lambda(t);
                }
                let reset = e.var_type().map(|_| c.n_vars() - 1);
                self.pool
                    .extend(e.get_arguments().map(|x| ExprOrType::Type {
                        lambda_type: x,
                        parent: Some(c.position),
                        is_app_subformula: false,
                        reset,
                    }));
                e.change_children(
                    (children_start..self.pool.len()).map(|x| LambdaExprRef(x as u32)),
                );
            }
        }
        self.pool[c.position] = ExprOrType::Expr {
            lambda_expr,
            parent,
        };
    }
}

#[derive(Debug)]
pub struct NormalEnumeration(BinaryHeap<Reverse<Context>>, VecDeque<ExprDetails>);

impl EnumerationType for NormalEnumeration {
    fn pop(&mut self) -> Option<Context> {
        self.0.pop().map(|x| x.0)
    }

    fn push(&mut self, context: Context, _: bool) {
        self.0.push(Reverse(context))
    }

    fn get_yield(&mut self) -> Option<ExprDetails> {
        self.1.pop_front()
    }

    fn push_yield(&mut self, e: ExprDetails) {
        self.1.push(e);
    }

    fn include(&mut self, n: usize) -> impl Iterator<Item = bool> + 'static {
        std::iter::repeat_n(true, n)
    }
}

impl ExprDetails {
    fn score(&self) -> f64 {
        (1.0 / (self.size as f64))
            + match self.constant_function {
                true => 0.0,
                false => 10.0,
            }
    }

    pub fn has_constant_function(&self) -> bool {
        self.constant_function
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
struct KeyedExprDetails {
    expr_details: ExprDetails,
    k: f64,
}

impl Eq for KeyedExprDetails {}

impl PartialOrd for KeyedExprDetails {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KeyedExprDetails {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        //reversed since we need a min-heap not a max-heap
        other.k.partial_cmp(&self.k).unwrap()
    }
}
impl KeyedExprDetails {
    fn new(expr_details: ExprDetails, rng: &mut impl Rng) -> Self {
        let u: f64 = rng.random();
        KeyedExprDetails {
            expr_details,
            k: u.powf(1.0 / expr_details.score()),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct RandomPQ(Context, f64);

impl Eq for RandomPQ {}

impl RandomPQ {
    fn new(c: Context, rng: &mut impl Rng) -> Self {
        RandomPQ(c, rng.random())
    }
}

#[derive(Debug)]
struct ProbabilisticEnumeration<'a, R: Rng, F>
where
    F: Fn(&ExprDetails) -> bool,
{
    rng: &'a mut R,
    reservoir_size: usize,
    reservoir: BinaryHeap<KeyedExprDetails>,
    backups: Vec<Context>,
    pq: BinaryHeap<RandomPQ>,
    filter: F,
    n_seen: usize,
    done: bool,
}
impl<R: Rng, F> ProbabilisticEnumeration<'_, R, F>
where
    F: Fn(&ExprDetails) -> bool,
{
    fn threshold(&self) -> Option<f64> {
        self.reservoir.peek().map(|x| x.k)
    }

    fn new<'a, 'src, T: LambdaLanguageOfThought, E: Fn(&Context) -> bool>(
        reservoir_size: usize,
        t: &LambdaType,
        possible_expressions: &'a PossibleExpressions<'src, T>,
        eager_filter: E,
        filter: F,
        rng: &'a mut R,
    ) -> LambdaEnumerator<'a, 'src, T, E, ProbabilisticEnumeration<'a, R, F>> {
        let context = Context::new(0, vec![]);
        let mut pq = BinaryHeap::default();
        pq.push(RandomPQ::new(context, rng));
        let pools = vec![UnfinishedLambdaPool {
            pool: vec![ExprOrType::Type {
                lambda_type: t.clone(),
                parent: None,
                is_app_subformula: false,
                reset: None,
            }],
        }];

        LambdaEnumerator {
            pools,
            possible_expressions,
            eager_filter,
            pq: ProbabilisticEnumeration {
                rng,
                reservoir_size,
                reservoir: BinaryHeap::default(),
                backups: vec![],
                filter,
                pq,
                n_seen: 0,
                done: false,
            },
        }
    }
}

impl<R: Rng, F> EnumerationType for ProbabilisticEnumeration<'_, R, F>
where
    F: Fn(&ExprDetails) -> bool,
{
    fn pop(&mut self) -> Option<Context> {
        //Pop from min-heap, or grab a random back up if the min-heap is exhausted
        self.pq.pop().map(|x| x.0).or_else(|| {
            (0..self.backups.len()).choose(self.rng).and_then(|index| {
                let last_item = self.backups.len() - 1;
                self.backups.swap(index, last_item);
                self.backups.pop()
            })
        })
    }

    fn push(&mut self, context: Context, included: bool) {
        if included {
            self.pq.push(RandomPQ::new(context, &mut self.rng));
        } else {
            self.backups.push(context);
        }
    }

    fn get_yield(&mut self) -> Option<ExprDetails> {
        if (self.done || self.pq.is_empty())
            && let Some(x) = self.reservoir.pop()
        {
            Some(x.expr_details)
        } else {
            None
        }
    }

    fn push_yield(&mut self, e: ExprDetails) {
        let e = KeyedExprDetails::new(e, &mut self.rng);
        if (self.filter)(&e.expr_details) {
            self.n_seen += 1;
            if self.reservoir_size > self.reservoir.len() {
                self.reservoir.push(e)
            } else if let Some(t) = self.threshold()
                && e.k > t
            {
                self.reservoir.pop();
                self.reservoir.push(e)
            }
            if self.n_seen >= self.reservoir_size * 20 {
                self.pq.clear();
                self.done = true;
            }
        }
    }

    fn include(&mut self, n: usize) -> impl Iterator<Item = bool> + 'static {
        let x = (0..n).choose_multiple(self.rng, (n / 2).max(1));
        let mut v = vec![false; n];
        for i in x {
            v[i] = true;
        }
        v.into_iter()
    }
}

#[derive(Debug)]
///An iterator that enumerates over all possible expressions of a given type.
pub struct LambdaEnumerator<'a, 'src, T: LambdaLanguageOfThought, F, E = NormalEnumeration> {
    pools: Vec<UnfinishedLambdaPool<'src, T>>,
    possible_expressions: &'a PossibleExpressions<'src, T>,
    eager_filter: F,
    pq: E,
}

///Provides detail about a generated lambda expression
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct ExprDetails {
    id: usize,
    constant_function: bool,
    root: LambdaExprRef,
    size: usize,
}

impl ExprDetails {
    ///Get the size of the associated [`RootedLambdaPool`].
    pub fn size(&self) -> usize {
        self.size
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
///A re-usable sampler for sampling expressions of arbitrary types while caching frequent types
pub struct TypeAgnosticSampler<'src, T: LambdaLanguageOfThought> {
    type_to_sampler: HashMap<LambdaType, (usize, LambdaSampler<'src, T>)>,
    max_expr: usize,
    max_types: usize,
    possible_expressions: PossibleExpressions<'src, T>,
}

impl<'src, T: LambdaLanguageOfThought + Clone + Debug> TypeAgnosticSampler<'src, T> {
    ///Samples an expression of a given type
    pub fn sample(
        &mut self,
        lambda_type: LambdaType,
        rng: &mut impl Rng,
    ) -> RootedLambdaPool<'src, T> {
        let (counts, exprs) = self
            .type_to_sampler
            .entry(lambda_type)
            .or_insert_with_key(|t| {
                (
                    1,
                    RootedLambdaPool::sampler(t, &self.possible_expressions, self.max_expr),
                )
            });
        *counts += 1;
        let sample = exprs.sample(rng);

        if self.type_to_sampler.len() > self.max_types {
            let (_, k) = self
                .type_to_sampler
                .iter()
                .map(|(k, (n_visits, _))| (n_visits, k))
                .min_by_key(|x| x.0)
                .unwrap();

            let t = k.clone();
            self.type_to_sampler.remove(&t);
        }

        sample
    }

    ///Get a reference to the [`PossibleExpressions`] used by the model
    pub fn possibles(&self) -> &PossibleExpressions<'src, T> {
        &self.possible_expressions
    }
}

impl<'src, T: LambdaLanguageOfThought + Clone> RootedLambdaPool<'src, T> {
    ///Create a sampler which can sample arbitrary types.
    pub fn typeless_sampler(
        possible_expressions: PossibleExpressions<'src, T>,
        max_expr: usize,
        max_types: usize,
    ) -> TypeAgnosticSampler<'src, T> {
        assert!(max_types >= 1);
        assert!(max_expr >= 1);
        TypeAgnosticSampler {
            possible_expressions,
            max_expr,
            max_types,
            type_to_sampler: HashMap::default(),
        }
    }
}

///A struct which samples expressions from a distribution.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LambdaSampler<'src, T: LambdaLanguageOfThought> {
    lambdas: Vec<RootedLambdaPool<'src, T>>,
    expr_details: Vec<ExprDetails>,
}

impl<'src, T: LambdaLanguageOfThought + Clone> Distribution<RootedLambdaPool<'src, T>>
    for LambdaSampler<'src, T>
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> RootedLambdaPool<'src, T> {
        let w = WeightedIndex::new(self.expr_details.iter().map(|x| x.score())).unwrap();
        let i = w.sample(rng);
        self.lambdas
            .get(i)
            .expect("The Lambda Sampler has no lambdas to sample :(")
            .clone()
    }
}

///A trait that handles how enumeration is processed (either normal enumeration or by doing
///reservoir sampling).
pub trait EnumerationType {
    fn pop(&mut self) -> Option<Context>;
    fn push(&mut self, context: Context, included: bool);
    fn get_yield(&mut self) -> Option<ExprDetails>;
    fn push_yield(&mut self, e: ExprDetails);
    fn include(&mut self, n: usize) -> impl Iterator<Item = bool> + 'static;
}

fn try_yield<'a, 'src, T, F, E>(
    x: &mut LambdaEnumerator<'a, 'src, T, F, E>,
) -> Option<(RootedLambdaPool<'src, T>, ExprDetails)>
where
    T: LambdaLanguageOfThought,
    E: EnumerationType,
{
    if let Some(item) = x.pq.get_yield() {
        let p = std::mem::take(&mut x.pools[item.id]);
        return Some((
            RootedLambdaPool {
                pool: LambdaPool(
                    p.pool
                        .into_iter()
                        .map(|x| LambdaExpr::try_from(x).unwrap())
                        .collect(),
                ),
                root: item.root,
            },
            item,
        ));
    }
    None
}

impl<'a, 'src, T, F, E> LambdaEnumerator<'a, 'src, T, F, E>
where
    T: LambdaLanguageOfThought + Clone + Debug,
    F: Fn(&Context) -> bool,
    E: EnumerationType,
{
    fn push(&mut self, c: Context, included: bool) {
        if (self.eager_filter)(&c) {
            self.pq.push(c, included);
        }
    }
}

impl<'a, 'src, T, F, E> Iterator for LambdaEnumerator<'a, 'src, T, F, E>
where
    T: LambdaLanguageOfThought + Clone + Debug,
    F: Fn(&Context) -> bool,
    E: EnumerationType,
{
    type Item = (RootedLambdaPool<'src, T>, ExprDetails);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(x) = try_yield(self) {
            return Some(x);
        }

        while let Some(mut c) = self.pq.pop() {
            if let Some(x) = try_yield(self) {
                self.push(c, true);
                return Some(x);
            }
            let (possibles, lambda_type) = match &self.pools[c.pool_index].pool[c.position] {
                ExprOrType::Type {
                    lambda_type,
                    is_app_subformula,
                    reset,
                    ..
                } => {
                    if let Some(reset) = reset {
                        c.reset_lambda(*reset);
                    }
                    (
                        self.possible_expressions.possibilities(
                            lambda_type,
                            *is_app_subformula,
                            &c,
                        ),
                        lambda_type.clone(),
                    )
                }
                ExprOrType::Expr {
                    lambda_expr,
                    parent,
                } => {
                    //We add the next uninitialized child to the context or go to the parent if
                    //there are none.

                    if let Some(child) = lambda_expr
                        .get_children()
                        .map(|x| x.0 as usize)
                        .find(|child| self.pools[c.pool_index].pool[*child].is_type())
                    {
                        c.position = child;
                        self.pq.push(c, true);
                        continue;
                    }

                    if lambda_expr.inc_depth() {
                        c.pop_lambda();
                    }

                    if let Some(p) = parent {
                        c.position = *p;
                        self.pq.push(c, true);
                        continue;
                    } else {
                        //If the parent is None, we're done!
                        self.pq.push_yield(ExprDetails {
                            id: c.pool_index,
                            root: LambdaExprRef(c.position as u32),
                            size: c.depth,
                            constant_function: c.is_constant(),
                        });
                        continue;
                    }
                }
            };

            let n = possibles.len();
            let included = self.pq.include(n);
            if n == 0 {
                // dbg!(&self.pools[c.pool_index]);
                //   panic!("There is no possible expression of type {lambda_type}");
                //This is a dead-end.
                continue;
            }
            let n_pools = self.pools.len();

            for _ in 0..n.saturating_sub(1) {
                self.pools.push(self.pools[c.pool_index].clone());
            }

            let positions =
                std::iter::once(c.pool_index).chain(n_pools..n_pools + n.saturating_sub(1));

            for (((expr, pool_id), mut c), included) in possibles
                .into_iter()
                .zip(positions)
                .zip(std::iter::repeat_n(c, n))
                .zip(included)
            {
                c.pool_index = pool_id;
                let pool = self.pools.get_mut(pool_id).unwrap();
                pool.add_expr(expr, &mut c, &lambda_type);
                self.push(c, included);
            }

            if let Some(x) = try_yield(self) {
                return Some(x);
            }
        }

        //If we've somehow exhausted the pq, lets yield anything remaining that's done.
        if let Some(x) = try_yield(self) {
            return Some(x);
        }
        None
    }
}

impl<'src, T: LambdaLanguageOfThought + Clone + Debug> RootedLambdaPool<'src, T> {
    ///Create a [`LambdaSampler`] of a given type.
    pub fn resample_from_expr<'a>(
        &mut self,
        possible_expressions: &'a PossibleExpressions<'src, T>,
        helpers: Option<&HashMap<LambdaType, Vec<RootedLambdaPool<'src, T>>>>,
        rng: &mut impl Rng,
    ) -> Result<(), LambdaError> {
        let position = LambdaExprRef((0..self.len()).choose(rng).unwrap() as u32);
        let t = self.pool.get_type(position)?;

        let pool = if let Some(helpers) = helpers
            && rng.random_bool(0.2)
            && let Some(v) = helpers.get(&t)
            && !v.is_empty()
        {
            let pool = v.choose(rng).unwrap();
            pool.clone()
        } else {
            let (pool, _) = self
                .probabilistic_enumerate_from_expr(
                    position,
                    possible_expressions,
                    |_| true,
                    |_| true,
                    rng,
                )?
                .next()
                .unwrap();
            pool
        };

        let offset = self.len() as u32;
        let new_root = pool.root.0 + offset;
        self.pool.0.extend(pool.pool.0.into_iter().map(|mut x| {
            let children: Vec<_> = x
                .get_children()
                .map(|x| LambdaExprRef(x.0 + offset))
                .collect();
            x.change_children(children.into_iter());
            x
        }));
        self.pool.0.swap(position.0 as usize, new_root as usize);
        self.cleanup();
        Ok(())
    }

    fn probabilistic_enumerate_from_expr<'a, R, E, F>(
        &self,
        position: LambdaExprRef,
        possible_expressions: &'a PossibleExpressions<'src, T>,
        eager_filter: E,
        filter: F,
        rng: &'a mut R,
    ) -> Result<LambdaEnumerator<'a, 'src, T, E, ProbabilisticEnumeration<'a, R, F>>, TypeError>
    where
        R: Rng,
        F: Fn(&ExprDetails) -> bool,
        E: Fn(&Context) -> bool,
    {
        let (context, is_app_subformula) = Context::from_pos(self, position);
        let output = self.pool.get_type(position)?;
        let mut pq = BinaryHeap::default();
        pq.push(RandomPQ::new(context, rng));
        let pools = vec![UnfinishedLambdaPool {
            pool: vec![ExprOrType::Type {
                lambda_type: output,
                parent: None,
                is_app_subformula,
                reset: None,
            }],
        }];
        let enumerator = LambdaEnumerator {
            pools,
            possible_expressions,
            eager_filter,
            pq: ProbabilisticEnumeration {
                rng,
                reservoir_size: 1,
                reservoir: BinaryHeap::default(),
                done: false,
                n_seen: 0,
                filter,
                backups: vec![],
                pq,
            },
        };

        Ok(enumerator)
    }

    ///Create a [`LambdaSampler`] of a given type with a filter
    pub fn enumerator_filter<'a, F: Fn(&Context) -> bool>(
        t: &LambdaType,
        filter: F,
        possible_expressions: &'a PossibleExpressions<'src, T>,
    ) -> LambdaEnumerator<'a, 'src, T, F> {
        let context = Context::new(0, vec![]);
        let mut pq = BinaryHeap::default();
        pq.push(Reverse(context));
        let pools = vec![UnfinishedLambdaPool {
            pool: vec![ExprOrType::Type {
                lambda_type: t.clone(),
                parent: None,
                is_app_subformula: false,
                reset: None,
            }],
        }];

        LambdaEnumerator {
            pools,
            possible_expressions,
            eager_filter: filter,
            pq: NormalEnumeration(pq, VecDeque::default()),
        }
    }

    ///Create a [`LambdaSampler`] of a given type.
    pub fn enumerator<'a>(
        t: &LambdaType,
        possible_expressions: &'a PossibleExpressions<'src, T>,
    ) -> LambdaEnumerator<'a, 'src, T, impl Fn(&'_ Context) -> bool> {
        let context = Context::new(0, vec![]);
        let mut pq = BinaryHeap::default();
        pq.push(Reverse(context));
        let pools = vec![UnfinishedLambdaPool {
            pool: vec![ExprOrType::Type {
                lambda_type: t.clone(),
                parent: None,
                is_app_subformula: false,
                reset: None,
            }],
        }];

        LambdaEnumerator {
            pools,
            possible_expressions,
            eager_filter: |_: &Context| true,
            pq: NormalEnumeration(pq, VecDeque::default()),
        }
    }

    ///Creates a reusable random sampler by enumerating over the first `max_expr` expressions
    pub fn sampler(
        t: &LambdaType,
        possible_expressions: &PossibleExpressions<'src, T>,
        max_expr: usize,
    ) -> LambdaSampler<'src, T> {
        let enumerator = RootedLambdaPool::enumerator(t, possible_expressions);
        let mut lambdas = Vec::with_capacity(max_expr);
        let mut expr_details = Vec::with_capacity(max_expr);
        for (lambda, expr_detail) in enumerator.take(max_expr) {
            lambdas.push(lambda);
            expr_details.push(expr_detail);
        }

        LambdaSampler {
            lambdas,
            expr_details,
        }
    }

    ///Randomly generate a [`RootedLambdaPool`] of type `t`.
    pub fn random_expr(
        t: &LambdaType,
        possible_expressions: &PossibleExpressions<'src, T>,
        rng: &mut impl Rng,
    ) -> RootedLambdaPool<'src, T> {
        ProbabilisticEnumeration::new(
            1,
            t,
            possible_expressions,
            |_: &Context| true,
            |_| true,
            rng,
        )
        .next()
        .unwrap()
        .0
    }

    ///Randomly generate a [`RootedLambdaPool`] of type `t` without constant functions.
    pub fn random_expr_no_constant(
        t: &LambdaType,
        possible_expressions: &PossibleExpressions<'src, T>,
        rng: &mut impl Rng,
    ) -> Option<RootedLambdaPool<'src, T>> {
        ProbabilisticEnumeration::new(
            1,
            t,
            possible_expressions,
            |c: &Context| !c.is_constant(),
            |e| !e.constant_function,
            rng,
        )
        .next()
        .map(|x| x.0)
    }
}

impl<'src> RootedLambdaPool<'src, Expr<'src>> {
    ///Remove quantifiers which do not use their variable in their body.
    pub fn prune_quantifiers(&mut self) {
        let quantifiers = self
            .pool
            .bfs_from(self.root)
            .filter_map(|(i, _)| match self.get(i) {
                LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier { subformula, .. }) => {
                    if !self
                        .pool
                        .bfs_from(LambdaExprRef(subformula.0))
                        .any(|(x, d)| {
                            if let LambdaExpr::BoundVariable(v, _) = self.get(x) {
                                *v == d
                            } else {
                                false
                            }
                        })
                    {
                        Some((i, LambdaExprRef(subformula.0)))
                    } else {
                        None
                    }
                }
                _ => None,
            })
            .collect::<Vec<_>>();

        //By reversing, we ensure that we fix inner quantifiers before outer ones.
        for (quantifier, subformula) in quantifiers.into_iter().rev() {
            *self.pool.get_mut(quantifier) = self.pool.get(subformula).clone();
            self.pool.bfs_from_mut(quantifier).for_each(|(x, d, _)| {
                if let LambdaExpr::BoundVariable(b_d, _) = x
                    && *b_d > d
                {
                    *b_d -= 1;
                }
            });
        }
        self.root = self.pool.cleanup(self.root);
    }

    ///Replace a random expression with something else of the same type.
    pub fn swap_expr(
        &mut self,
        possible_expressions: &PossibleExpressions<'src, Expr<'src>>,
        rng: &mut impl Rng,
    ) -> Result<(), TypeError> {
        let position = LambdaExprRef((0..self.len()).choose(rng).unwrap() as u32);

        let (context, _) = Context::from_pos(self, position);

        let output = self.pool.get_type(position)?;
        let expr = self.pool.get(position);

        let arguments: Vec<_> = expr
            .get_children()
            .map(|x| self.pool.get_type(x).unwrap())
            .collect();

        let replacements = possible_expressions.possiblities_fixed_children(
            &output,
            &arguments,
            expr.var_type(),
            &context,
        );

        let choice = replacements.choose(rng).unwrap_or_else(|| {
            panic!(
                "There is no node with output {output} and arguments {}",
                arguments
                    .into_iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        });

        let mut new_expr = choice.clone().into_owned();
        new_expr.change_children(self.pool.get(position).get_children());
        self.pool.0[position.0 as usize] = new_expr;

        Ok(())
    }

    ///Replace a random expression with something else of the same type from within the same
    ///expression.
    pub fn swap_subtree(&mut self, rng: &mut impl Rng) -> Result<(), TypeError> {
        let position = LambdaExprRef((0..self.len()).choose(rng).unwrap() as u32);
        let (context, _) = Context::from_pos(self, position);
        let alt = context.find_compatible(self, position)?;
        if let Some(new_pos) = alt.choose(rng).copied() {
            let offset = self.pool.0.len();
            let mut lookup = HashMap::default();
            let mut new_pool: Vec<LambdaExpr<'src, Expr<'src>>> = self
                .pool
                .bfs_from(new_pos)
                .map(|(x, _)| {
                    let n = lookup.len();
                    lookup
                        .entry(x)
                        .or_insert(LambdaExprRef((n + offset) as u32));
                    self.get(x).clone()
                })
                .collect();

            new_pool.iter_mut().for_each(|x| {
                let child: Vec<_> = x.get_children().map(|x| *lookup.get(&x).unwrap()).collect();
                x.change_children(child.into_iter());
            });

            self.pool.0.extend(new_pool);
            self.pool.0.swap(position.0 as usize, offset);
            self.cleanup();
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {

    use std::collections::HashSet;

    use super::*;
    use crate::lambda::{LambdaPool, LambdaSummaryStats};
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    #[test]
    fn prune_quantifier_test() -> anyhow::Result<()> {
        let mut pool =
            RootedLambdaPool::parse("some_e(x,all_e,AgentOf(a_2,e_1) & PatientOf(a_0,e_0))")?;

        pool.prune_quantifiers();
        assert_eq!(pool.to_string(), "AgentOf(a_2, e_1) & PatientOf(a_0, e_0)");

        let mut pool = RootedLambdaPool::parse(
            "some_e(x0, all_e, some(z, all_a, AgentOf(z, e_1) & PatientOf(a_0, e_0)))",
        )?;

        pool.prune_quantifiers();
        assert_eq!(
            pool.to_string(),
            "some(x, all_a, AgentOf(x, e_1) & PatientOf(a_0, e_0))"
        );

        let mut pool = RootedLambdaPool::parse("~every_e(z, pe_1, pa_2(a_0))")?;

        pool.prune_quantifiers();

        assert_eq!(pool.to_string(), "~pa_2(a_0)");
        let mut pool = RootedLambdaPool::new(
            LambdaPool(vec![
                LambdaExpr::Lambda(LambdaExprRef(1), LambdaType::E),
                LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::T),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                    quantifier: Quantifier::Universal,
                    var_type: ActorOrEvent::Actor,
                    restrictor: ExprRef(3),
                    subformula: ExprRef(4),
                }),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Constant(Constant::Property(
                    "1",
                    ActorOrEvent::Actor,
                ))),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                    quantifier: Quantifier::Existential,
                    var_type: ActorOrEvent::Actor,
                    restrictor: ExprRef(5),
                    subformula: ExprRef(6),
                }),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Constant(Constant::Property(
                    "0",
                    ActorOrEvent::Actor,
                ))),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                    MonOp::Property("3", ActorOrEvent::Event),
                    ExprRef(7),
                )),
                LambdaExpr::BoundVariable(3, LambdaType::E),
            ]),
            LambdaExprRef(0),
        );

        assert_eq!(
            pool.to_string(),
            "lambda e x lambda t phi every(y, pa_1, some(z, pa_0, pe_3(x)))"
        );

        let mut parsed_pool = RootedLambdaPool::parse(
            "lambda e x lambda t phi every(y, pa_1, some(z, pa_0, pe_3(x)))",
        )?;
        parsed_pool.prune_quantifiers();
        pool.prune_quantifiers();
        assert_eq!(pool.to_string(), "lambda e x lambda t phi pe_3(x)");

        Ok(())
    }

    #[test]
    fn random_swap_tree() -> anyhow::Result<()> {
        let mut rng = ChaCha8Rng::seed_from_u64(2);
        let x = RootedLambdaPool::parse("lambda a x pa_cool(a_John) | pa_cool(x)")?;
        let mut h = HashSet::new();
        for _ in 0..100 {
            let mut z = x.clone();
            z.swap_subtree(&mut rng)?;
            h.insert(z.to_string());
        }
        for x in h.iter() {
            println!("{x}");
        }
        assert!(h.contains("lambda a x pa_cool(x)"));
        assert!(h.contains("lambda a x pa_cool(a_John)"));
        Ok(())
    }

    #[test]
    fn randomn_swap() -> anyhow::Result<()> {
        let mut rng = ChaCha8Rng::seed_from_u64(2);
        let actors = ["0", "1"];
        let available_event_properties = ["2", "3", "4"];
        let possible_expressions = PossibleExpressions::new(
            &actors,
            &available_event_properties,
            &available_event_properties,
        );
        for _ in 0..200 {
            let t = LambdaType::random_no_e(&mut rng);
            println!("{t}");
            let mut pool = RootedLambdaPool::random_expr(&t, &possible_expressions, &mut rng);
            println!("{t}: {pool}");
            assert_eq!(t, pool.get_type()?);
            println!("{pool:?}");
            pool.swap_expr(&possible_expressions, &mut rng)?;
            println!("{pool:?}");
            println!("{t}: {pool}");
            assert_eq!(t, pool.get_type()?);
        }
        let p =
            RootedLambdaPool::parse("lambda <a,t> P some(x, P(x), some_e(y, pe_2(y), pe_4(y)))")?;
        let t = p.get_type()?;
        for _ in 0..1000 {
            let mut pool = p.clone();
            assert_eq!(t, pool.get_type()?);

            pool.swap_expr(&possible_expressions, &mut rng)?;
            dbg!(&pool);
            println!("{t}: {pool}");
            assert_eq!(t, pool.get_type()?);
        }

        Ok(())
    }

    #[test]
    fn enumerate() -> anyhow::Result<()> {
        let actors = ["john"];
        let actor_properties = ["a"];
        let event_properties = ["e"];
        let possibles = PossibleExpressions::new(&actors, &actor_properties, &event_properties);

        let t = LambdaType::from_string("<<a,t>,t>")?;

        let p = RootedLambdaPool::enumerator(&t, &possibles);
        let pools: HashSet<_> = p
            .filter_map(|(p, x)| {
                if !x.has_constant_function() {
                    Some(p.to_string())
                } else {
                    None
                }
            })
            .take(20)
            .collect();
        assert!(pools.contains("lambda <a,t> P P(a_john)"));
        for p in pools {
            println!("{p}");
        }

        Ok(())
    }

    #[test]
    fn random_expr() -> anyhow::Result<()> {
        let actors = ["john"];
        let actor_properties = ["a"];
        let event_properties = ["e"];
        let possibles = PossibleExpressions::new(&actors, &actor_properties, &event_properties);
        let mut rng = ChaCha8Rng::seed_from_u64(0);

        let map = [(LambdaType::A, vec![RootedLambdaPool::parse("a_john")?])]
            .into_iter()
            .collect();

        for _ in 0..1000 {
            let t = LambdaType::random_no_e(&mut rng);
            println!("sampling: {t}");
            let mut pool = RootedLambdaPool::random_expr(&t, &possibles, &mut rng);
            assert_eq!(t, pool.get_type()?);
            let s = pool.to_string();
            let mut pool2 = RootedLambdaPool::parse(s.as_str())?;
            assert_eq!(s, pool2.to_string());
            println!("{pool}");
            pool2.resample_from_expr(&possibles, None, &mut rng)?;
            assert_eq!(pool2.get_type()?, t);
            pool2.resample_from_expr(&possibles, Some(&map), &mut rng)?;
            assert_eq!(pool2.get_type()?, t);

            pool.swap_subtree(&mut rng)?;
            assert_eq!(pool.get_type()?, t);
        }
        let t = LambdaType::from_string("<a,<a,t>>")?;
        for _ in 0..1000 {
            let pool = RootedLambdaPool::random_expr(&t, &possibles, &mut rng);
            println!("{pool}");
        }
        Ok(())
    }

    #[test]
    fn constant_exprs() -> anyhow::Result<()> {
        let actors = ["john", "mary", "phil", "sue"];
        let actor_properties = ["a"];
        let event_properties = ["e"];
        let possibles = PossibleExpressions::new(&actors, &actor_properties, &event_properties);
        let mut rng = ChaCha8Rng::seed_from_u64(0);

        let v: HashSet<_> = RootedLambdaPool::enumerator(LambdaType::a(), &possibles)
            .map(|(x, _)| x.to_string())
            .collect();

        assert_eq!(v, HashSet::from(actors.map(|x| format!("a_{x}"))));
        println!("{v:?}");

        let mut constants = 0;
        for _ in 0..1000 {
            let t = LambdaType::from_string("<a, <a,t>>")?;
            println!("sampling: {t}");
            let pool = RootedLambdaPool::random_expr(&t, &possibles, &mut rng);
            let x = pool.stats();
            match x {
                LambdaSummaryStats::WellFormed {
                    constant_function, ..
                } => {
                    if constant_function {
                        constants += 1;
                    }
                }
                LambdaSummaryStats::Malformed => todo!(),
            }
        }
        println!("{constants}");

        Ok(())
    }

    #[test]
    fn random_expr_counts() -> anyhow::Result<()> {
        let actors = ["john", "mary", "phil", "sue"];
        let actor_properties = ["a"];
        let event_properties = ["e"];
        let possibles = PossibleExpressions::new(&actors, &actor_properties, &event_properties);
        let mut rng = ChaCha8Rng::seed_from_u64(0);

        let mut counts: HashMap<_, usize> = HashMap::default();
        for _ in 0..1000 {
            let t = LambdaType::A;
            let pool = RootedLambdaPool::random_expr(&t, &possibles, &mut rng);
            assert_eq!(t, pool.get_type()?);
            let s = pool.to_string();
            *counts.entry(s).or_default() += 1;
        }
        assert_eq!(counts.len(), 4);
        for (_, v) in counts.iter() {
            assert!(200 <= *v && *v <= 300);
        }

        counts.clear();
        for _ in 0..1000 {
            let t = LambdaType::at().clone();
            let pool = RootedLambdaPool::random_expr(&t, &possibles, &mut rng);
            assert_eq!(t, pool.get_type()?);
            let s = pool.to_string();
            *counts.entry(s).or_default() += 1;
        }
        dbg!(counts);
        Ok(())
    }
}
