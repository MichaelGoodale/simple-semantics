use std::{
    borrow::Cow,
    collections::{VecDeque, hash_map::Entry},
    iter::repeat_n,
};

use ahash::HashMap;
use rand::seq::IndexedRandom;
use thiserror::Error;

use super::*;
use crate::{Actor, Event, PropertyLabel, lambda::ExpressionType};

#[derive(Debug, Error, Clone, Copy)]
pub enum MutationError {
    #[error("You cannot make an expression that returns 'e'")]
    InvalidType,
}

impl RootedLambdaPool<Expr> {
    fn get_context_for_expr<'a: 'pool, 'pool, 'props: 'pool>(
        &'pool self,
        position: LambdaExprRef,
        possible_expressions: &'a PossibleExpressions<'pool>,
    ) -> Option<Context<'props, 'pool>> {
        let mut pos_context = None;

        for (n, c) in self.context_bfs_iter(possible_expressions) {
            if n == position {
                pos_context = Some(c);
                break;
            }
        }
        pos_context
    }

    pub fn resample_from_expr(
        self,
        available_actors: &[Actor],
        available_actor_properties: &[PropertyLabel],
        available_event_properties: &[PropertyLabel],
        config: Option<&RandomExprConfig>,
        rng: &mut impl Rng,
    ) -> Self {
        let config = config.unwrap_or(&DEFAULT_CONFIG);
        let position = LambdaExprRef(rng.random_range(0..self.len()) as u32);

        let possible_expressions = PossibleExpressions::new(
            available_actors,
            available_actor_properties,
            available_event_properties,
        );

        let context = self
            .get_context_for_expr(position, &possible_expressions)
            .expect("Couldn't find the {position}th expression");

        //Here we extract the lambdas and reborrow them to avoid borrowing crap.
        let available_vars = context.available_vars;
        let lambdas = context.lambdas.into_iter().cloned().collect::<Vec<_>>();
        let context = Context {
            lambdas: lambdas.iter().collect(),
            available_vars,
            possible_expressions: &possible_expressions,
            depth: context.depth,
        };

        let (root, pool) = (self.root, self.pool);

        let lambda_type = pool.get_type(position).unwrap();
        let mut pool: Vec<Option<LambdaExpr<Expr>>> = pool.into();
        pool[position.0 as usize] = None;

        let mut pool = build_out_pool(pool, &lambda_type, position.0, context, config, rng);
        let root = pool.cleanup(root);

        RootedLambdaPool { pool, root }
    }

    pub fn random_expr(
        lambda_type: &LambdaType,
        available_actors: &[Actor],
        available_actor_properties: &[PropertyLabel],
        available_event_properties: &[PropertyLabel],
        config: Option<&RandomExprConfig>,
        rng: &mut impl Rng,
    ) -> Result<Self, MutationError> {
        if lambda_type == LambdaType::e() {
            return Err(MutationError::InvalidType);
        }
        let pool = vec![None];

        let possible_expression = PossibleExpressions::new(
            available_actors,
            available_actor_properties,
            available_event_properties,
        );
        let context = Context {
            lambdas: vec![],
            available_vars: vec![],
            possible_expressions: &possible_expression,
            depth: 0,
        };
        let config = config.unwrap_or(&DEFAULT_CONFIG);

        let pool = build_out_pool(pool, lambda_type, 0, context, config, rng);
        Ok(RootedLambdaPool::new(pool, LambdaExprRef(0)))
    }

    pub fn prune_quantifiers(&mut self) {
        let quantifiers = self
            .pool
            .0
            .iter()
            .enumerate()
            .filter_map(|(i, x)| match x {
                LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier { .. }) => {
                    Some(LambdaExprRef(i as u32))
                }
                _ => None,
            })
            .collect::<Vec<_>>();

        for quantifier in quantifiers {
            if let LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                var, subformula, ..
            }) = self.get(quantifier)
            {
                let has_variable = self
                    .pool
                    .bfs_from(LambdaExprRef(subformula.0))
                    .any(|(x, _)| {
                        if let LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(v)) = self.get(x) {
                            v == var
                        } else {
                            false
                        }
                    });
                if !has_variable {
                    self.pool.0[quantifier.0 as usize] = self.pool.0[subformula.0 as usize].clone();
                }
            }
        }
        self.root = self.pool.cleanup(self.root);
    }

    pub fn swap_expr(
        &mut self,
        available_actors: &[Actor],
        available_actor_properties: &[PropertyLabel],
        available_event_properties: &[PropertyLabel],
        rng: &mut impl Rng,
    ) {
        let position = LambdaExprRef((0..self.len()).choose(rng).unwrap() as u32);
        let possible_expressions = PossibleExpressions::new(
            available_actors,
            available_actor_properties,
            available_event_properties,
        );

        let context = self
            .get_context_for_expr(position, &possible_expressions)
            .unwrap_or_else(|| panic!("Couldn't find {}th expr!", position.0));
        let ExpressionType { output, arguments } = self.get_expression_type(position).unwrap();
        let replacement = possible_expressions
            .expr_from_args_and_output(&output, &arguments, &context)
            .choose(rng)
            .unwrap()
            .clone()
            .into_owned();

        let new_expr = {
            let mut children = self.get(position).get_children();
            match replacement {
                UnbuiltExpr::Quantifier(quantifier, actor_or_event) => {
                    let mut fresher = Fresher::new_rooted(self);
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                        quantifier,
                        var: fresher.fresh(actor_or_event),
                        restrictor: children.next().unwrap().into(),
                        subformula: children.next().unwrap().into(),
                    })
                }
                UnbuiltExpr::Variable(variable) => {
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(variable))
                }
                UnbuiltExpr::Actor(a) => LambdaExpr::LanguageOfThoughtExpr(Expr::Actor(a)),
                UnbuiltExpr::Event(e) => LambdaExpr::LanguageOfThoughtExpr(Expr::Event(e)),
                UnbuiltExpr::Binary(bin_op) => LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(
                    bin_op,
                    children.next().unwrap().into(),
                    children.next().unwrap().into(),
                )),
                UnbuiltExpr::Unary(mon_op) => LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                    mon_op,
                    children.next().unwrap().into(),
                )),
                UnbuiltExpr::Constant(constant) => {
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Constant(constant))
                }
                UnbuiltExpr::Lambda(lhs, _) => {
                    LambdaExpr::Lambda(children.next().unwrap(), lhs.clone())
                }
                UnbuiltExpr::BoundVariable(var, lambda_type) => {
                    LambdaExpr::BoundVariable(var, lambda_type.clone())
                }
            }
        };

        self.pool.0[position.0 as usize] = new_expr;
    }
}

fn build_out_pool<'typ>(
    mut pool: Vec<Option<LambdaExpr<Expr>>>,
    lambda_type: &'typ LambdaType,
    start_pos: u32,
    context: Context<'_, 'typ>,
    config: &RandomExprConfig,
    rng: &mut impl Rng,
) -> LambdaPool<Expr> {
    let mut fresher = Fresher::new(&pool);
    let e: UnbuiltExpr<'typ> = context.sample_expr(lambda_type, config, rng);

    let mut stack = add_expr(e, start_pos, context, &mut fresher, &mut pool);

    while let Some((pos, lambda_type, context)) = stack.pop() {
        let e = context.sample_expr(lambda_type, config, rng);

        stack.extend(add_expr(e, pos, context, &mut fresher, &mut pool));
    }
    pool.try_into().unwrap()
}

impl UnbuiltExpr<'_> {
    fn get_expression_type(&self) -> ExpressionType {
        match self {
            UnbuiltExpr::Quantifier(_, actor_or_event) => ExpressionType {
                output: LambdaType::t().clone(),
                arguments: vec![
                    match actor_or_event {
                        ActorOrEvent::Actor => LambdaType::at().clone(),
                        ActorOrEvent::Event => LambdaType::et().clone(),
                    },
                    LambdaType::t().clone(),
                ],
            },
            UnbuiltExpr::Variable(var) => ExpressionType::new_no_args(match var {
                Variable::Actor(_) => LambdaType::a().clone(),
                Variable::Event(_) => LambdaType::e().clone(),
            }),
            UnbuiltExpr::Actor(_) => ExpressionType::new_no_args(LambdaType::a().clone()),
            UnbuiltExpr::Event(_) => ExpressionType::new_no_args(LambdaType::e().clone()),
            UnbuiltExpr::Binary(b) => match b {
                BinOp::AgentOf | BinOp::PatientOf => ExpressionType {
                    output: LambdaType::t().clone(),
                    arguments: vec![LambdaType::a().clone(), LambdaType::e().clone()],
                },
                BinOp::And | BinOp::Or => ExpressionType {
                    output: LambdaType::t().clone(),
                    arguments: vec![LambdaType::t().clone(), LambdaType::t().clone()],
                },
            },
            UnbuiltExpr::Unary(m) => match m {
                MonOp::Not | MonOp::Tautology | MonOp::Contradiction => ExpressionType {
                    output: LambdaType::t().clone(),
                    arguments: vec![LambdaType::t().clone()],
                },
                MonOp::Property(_, actor_or_event) => ExpressionType {
                    output: LambdaType::t().clone(),
                    arguments: vec![match actor_or_event {
                        ActorOrEvent::Actor => LambdaType::a().clone(),
                        ActorOrEvent::Event => LambdaType::e().clone(),
                    }],
                },
            },
            UnbuiltExpr::Constant(c) => match c {
                Constant::Everyone => ExpressionType::new_no_args(LambdaType::at().clone()),
                Constant::EveryEvent => ExpressionType::new_no_args(LambdaType::et().clone()),
                Constant::Contradiction | Constant::Tautology => {
                    ExpressionType::new_no_args(LambdaType::t().clone())
                }
                Constant::Property(_, actor_or_event) => {
                    ExpressionType::new_no_args(match actor_or_event {
                        ActorOrEvent::Actor => LambdaType::at().clone(),
                        ActorOrEvent::Event => LambdaType::et().clone(),
                    })
                }
            },
            UnbuiltExpr::Lambda(lhs, rhs) => ExpressionType {
                output: (*rhs).clone(),
                arguments: vec![(*lhs).clone()],
            },
            UnbuiltExpr::BoundVariable(_, lambda_type) => {
                ExpressionType::new_no_args((*lambda_type).clone())
            }
        }
    }
}
#[derive(Debug, Clone)]
pub struct PossibleExpressions<'a> {
    expressions: HashMap<LambdaType, HashMap<Vec<LambdaType>, Vec<UnbuiltExpr<'a>>>>,
}

impl<'typ> PossibleExpressions<'typ> {
    fn new(
        actors: &[Actor],
        actor_properties: &[PropertyLabel],
        event_properties: &[PropertyLabel],
    ) -> Self {
        let mut all_expressions: Vec<UnbuiltExpr> = vec![
            UnbuiltExpr::Constant(Constant::Everyone),
            UnbuiltExpr::Constant(Constant::EveryEvent),
            UnbuiltExpr::Unary(MonOp::Not),
            UnbuiltExpr::Binary(BinOp::And),
            UnbuiltExpr::Binary(BinOp::Or),
            UnbuiltExpr::Quantifier(Quantifier::Existential, ActorOrEvent::Actor),
            UnbuiltExpr::Quantifier(Quantifier::Universal, ActorOrEvent::Actor),
            UnbuiltExpr::Quantifier(Quantifier::Existential, ActorOrEvent::Event),
            UnbuiltExpr::Quantifier(Quantifier::Universal, ActorOrEvent::Event),
            UnbuiltExpr::Binary(BinOp::AgentOf),
            UnbuiltExpr::Binary(BinOp::PatientOf),
        ];

        all_expressions.extend(actors.iter().map(|x| UnbuiltExpr::Actor(*x)));

        all_expressions.extend(actor_properties.iter().flat_map(|i| {
            [
                UnbuiltExpr::Unary(MonOp::Property(*i, ActorOrEvent::Actor)),
                UnbuiltExpr::Constant(Constant::Property(*i, ActorOrEvent::Actor)),
            ]
        }));
        all_expressions.extend(event_properties.iter().flat_map(|i| {
            [
                UnbuiltExpr::Unary(MonOp::Property(*i, ActorOrEvent::Event)),
                UnbuiltExpr::Constant(Constant::Property(*i, ActorOrEvent::Event)),
            ]
        }));

        let mut expressions: HashMap<LambdaType, HashMap<_, Vec<_>>> = HashMap::default();
        for expr in all_expressions {
            let ExpressionType { output, arguments } = expr.get_expression_type();

            //Annoying match to avoid cloning arguments
            match expressions.entry(output) {
                Entry::Occupied(mut occupied) => {
                    let inner_h: &mut HashMap<_, _> = occupied.get_mut();
                    match inner_h.entry(arguments) {
                        Entry::Occupied(mut occupied) => occupied.get_mut().push(expr),
                        Entry::Vacant(vacant) => {
                            vacant.insert(vec![expr]);
                        }
                    }
                }
                Entry::Vacant(vacant) => {
                    vacant.insert([(arguments, vec![expr])].into_iter().collect());
                }
            }
        }

        PossibleExpressions { expressions }
    }

    fn expr_from_args_and_output<'a>(
        &'a self,
        lambda_type: &'typ LambdaType,
        arguments: &'typ [LambdaType],
        context: &Context<'_, 'typ>,
    ) -> Vec<Cow<'a, UnbuiltExpr<'typ>>> {
        let mut possibilities: Vec<Cow<UnbuiltExpr<'typ>>> = self
            .expressions
            .get(lambda_type)
            .map(|x| {
                x.get(arguments)
                    .map(|x| x.iter().map(Cow::Borrowed).collect::<Vec<_>>())
                    .unwrap_or_default()
            })
            .unwrap_or_default();

        if arguments.len() == 1 {
            if let Ok((lhs, rhs)) = lambda_type.split() {
                if rhs == arguments.first().unwrap() {
                    possibilities.push(Cow::Owned(UnbuiltExpr::Lambda(lhs, rhs)));
                }
            }
        } else if arguments.is_empty() {
            possibilities.extend(context.lambda_variables(lambda_type).map(Cow::Owned));
            if lambda_type == LambdaType::a() {
                possibilities.extend(context.actor_variables().map(Cow::Owned));
            } else if lambda_type == LambdaType::e() {
                possibilities.extend(context.event_variables().map(Cow::Owned));
            }
        }

        possibilities
    }

    fn expr_from_output<'a>(
        &'a self,
        lambda_type: &'typ LambdaType,
        context: &Context<'_, 'typ>,
    ) -> (Vec<Cow<'a, UnbuiltExpr<'typ>>>, Vec<usize>) {
        let (mut possibilities, mut n_args): (Vec<Cow<UnbuiltExpr<'typ>>>, Vec<usize>) = self
            .expressions
            .get(lambda_type)
            .map(|x| {
                x.iter()
                    .filter(|(k, _)| !has_e_argument(k) || context.can_sample_event())
                    .flat_map(|(k, v)| v.iter().map(|x| (Cow::Borrowed(x), k.len())))
                    .collect()
            })
            .unwrap_or_default();

        if let Ok((lhs, rhs)) = lambda_type.split() {
            possibilities.push(Cow::Owned(UnbuiltExpr::Lambda(lhs, rhs)));
            n_args.push(1);
        }

        let n_possibilities = possibilities.len();

        possibilities.extend(context.lambda_variables(lambda_type).map(Cow::Owned));
        if lambda_type == LambdaType::a() {
            possibilities.extend(context.actor_variables().map(Cow::Owned));
        } else if lambda_type == LambdaType::e() {
            possibilities.extend(context.event_variables().map(Cow::Owned));
        }

        let n_new_possibilities = possibilities.len() - n_possibilities;
        n_args.extend(repeat_n(0, n_new_possibilities));

        #[cfg(test)]
        assert_eq!(possibilities.len(), n_args.len());

        (possibilities, n_args)
    }
}

fn has_e_argument(v: &[LambdaType]) -> bool {
    v.iter().any(|v| v == LambdaType::e())
}

#[derive(Debug, Clone)]
struct Context<'a, 't> {
    lambdas: Vec<&'t LambdaType>,
    available_vars: Vec<Variable>,
    possible_expressions: &'a PossibleExpressions<'t>,
    depth: usize,
}

impl<'a, 't> Context<'a, 't> {
    fn event_variables(&self) -> impl Iterator<Item = UnbuiltExpr<'t>> {
        self.available_vars.iter().filter_map(|x| {
            if matches!(x, Variable::Event(_)) {
                Some(UnbuiltExpr::Variable(*x))
            } else {
                None
            }
        })
    }

    fn actor_variables(&self) -> impl Iterator<Item = UnbuiltExpr<'t>> {
        self.available_vars.iter().filter_map(|x| {
            if matches!(x, Variable::Actor(_)) {
                Some(UnbuiltExpr::Variable(*x))
            } else {
                None
            }
        })
    }

    fn can_sample_event(&self) -> bool {
        self.available_vars
            .iter()
            .any(|x| matches!(x, Variable::Event(_)))
            | self.lambdas.iter().any(|lam| *lam == LambdaType::e())
    }

    fn lambda_variables(&self, lambda_type: &LambdaType) -> impl Iterator<Item = UnbuiltExpr<'t>> {
        let n = self.lambdas.len();
        self.lambdas.iter().enumerate().filter_map(move |(i, t)| {
            if *t == lambda_type {
                Some(UnbuiltExpr::BoundVariable(n - i - 1, t))
            } else {
                None
            }
        })
    }

    fn sample_expr(
        &self,
        lambda_type: &'t LambdaType,
        config: &RandomExprConfig,
        rng: &mut impl Rng,
    ) -> UnbuiltExpr<'t> {
        let (expressions, n_args) = self
            .possible_expressions
            .expr_from_output(lambda_type, self);
        let i = (0..expressions.len()).choose(rng).unwrap();
        expressions[i].clone().into_owned()
    }
}

fn add_expr<'props, 'pool>(
    e: UnbuiltExpr<'pool>,
    pos: u32,
    mut context: Context<'props, 'pool>,
    fresher: &mut Fresher,
    pool: &mut Vec<Option<LambdaExpr<Expr>>>,
) -> Vec<(u32, &'pool LambdaType, Context<'props, 'pool>)> {
    let cur_size = pool.len() as u32 - 1;
    let mut children = vec![];
    let expr = match e {
        UnbuiltExpr::Quantifier(quantifier, actor_or_event) => {
            children.extend_from_slice(&[
                (
                    cur_size + 1,
                    //TODO: Add ability to sample arbitrary restrictors (e.g. add type t)
                    match actor_or_event {
                        ActorOrEvent::Actor => LambdaType::at(),
                        ActorOrEvent::Event => LambdaType::et(),
                    },
                ),
                (cur_size + 2, LambdaType::t()),
            ]);
            let var = fresher.fresh(actor_or_event);
            context.available_vars.push(var);
            LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                quantifier,
                var,
                restrictor: ExprRef(cur_size + 1),
                subformula: ExprRef(cur_size + 2),
            })
        }
        UnbuiltExpr::Variable(var) => LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(var)),
        UnbuiltExpr::Event(event) => LambdaExpr::LanguageOfThoughtExpr(Expr::Event(event)),
        UnbuiltExpr::Actor(actor) => LambdaExpr::LanguageOfThoughtExpr(Expr::Actor(actor)),
        UnbuiltExpr::Binary(bin_op) => {
            children.extend_from_slice(&match bin_op {
                BinOp::AgentOf | BinOp::PatientOf => [
                    (cur_size + 1, LambdaType::a()),
                    (cur_size + 2, LambdaType::e()),
                ],
                BinOp::And | BinOp::Or => [
                    (cur_size + 1, LambdaType::t()),
                    (cur_size + 2, LambdaType::t()),
                ],
            });
            LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(
                bin_op,
                ExprRef(cur_size + 1),
                ExprRef(cur_size + 2),
            ))
        }
        UnbuiltExpr::Unary(mon_op) => {
            children.push(match mon_op {
                MonOp::Property(_, ActorOrEvent::Actor) => (cur_size + 1, LambdaType::a()),
                MonOp::Property(_, ActorOrEvent::Event) => (cur_size + 1, LambdaType::e()),
                MonOp::Not | MonOp::Tautology | MonOp::Contradiction => {
                    (cur_size + 1, LambdaType::t())
                }
            });
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(mon_op, ExprRef(cur_size + 1)))
        }
        UnbuiltExpr::Constant(constant) => {
            LambdaExpr::LanguageOfThoughtExpr(Expr::Constant(constant))
        }
        UnbuiltExpr::Lambda(lhs, rhs) => {
            children.push((cur_size + 1, rhs));
            context.lambdas.push(lhs);
            LambdaExpr::Lambda(LambdaExprRef(cur_size + 1), lhs.clone())
        }
        UnbuiltExpr::BoundVariable(bvar, lambda_type) => {
            LambdaExpr::BoundVariable(bvar, lambda_type.clone())
        }
    };

    pool[pos as usize] = Some(expr);
    pool.resize(pool.len() + children.len(), None);
    children
        .into_iter()
        .map(|(a, b)| (a, b, context.clone()))
        .collect()
}

//Need to add applications
#[derive(Debug, Clone)]
enum UnbuiltExpr<'t> {
    Quantifier(Quantifier, ActorOrEvent),
    Variable(Variable),
    Actor(Actor),
    Event(Event),
    Binary(BinOp),
    Unary(MonOp),
    Constant(Constant),
    Lambda(&'t LambdaType, &'t LambdaType),
    BoundVariable(Bvar, &'t LambdaType),
}

#[derive(Debug, Copy, Clone, Default)]
struct Fresher(u32);

impl Fresher {
    fn fresh(&mut self, actor_or_event: ActorOrEvent) -> Variable {
        self.0 += 1;
        actor_or_event.to_variable(self.0)
    }
    fn new_rooted(pool: &RootedLambdaPool<Expr>) -> Self {
        Fresher(
            pool.pool
                .0
                .iter()
                .filter_map(|x| match x {
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(v))
                    | LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier { var: v, .. }) => {
                        Some(v.id())
                    }
                    _ => None,
                })
                .max()
                .unwrap_or(0),
        )
    }

    fn new(pool: &[Option<LambdaExpr<Expr>>]) -> Self {
        Fresher(
            pool.iter()
                .filter_map(|x| match x {
                    Some(LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(v)))
                    | Some(LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                        var: v, ..
                    })) => Some(v.id()),
                    _ => None,
                })
                .max()
                .unwrap_or(0),
        )
    }
}

static DEFAULT_CONFIG: std::sync::LazyLock<RandomExprConfig> =
    std::sync::LazyLock::new(RandomExprConfig::default);

#[derive(Debug, Clone, Copy)]
pub struct RandomExprConfig {
    lambda_prob: f64,
    variable_prob: f64,
}

impl RandomExprConfig {
    fn new(lambda_prob: f64, variable_prob: f64) -> Self {
        Self {
            lambda_prob,
            variable_prob,
        }
    }
}

impl Default for RandomExprConfig {
    fn default() -> Self {
        Self {
            lambda_prob: 0.2,
            variable_prob: 0.5,
        }
    }
}
impl RandomExprConfig {
    fn is_lambda(&self, lambda_type: &LambdaType, rng: &mut impl Rng) -> bool {
        lambda_type.is_function() && rng.random_bool(self.lambda_prob)
    }

    fn is_variable(&self, rng: &mut impl Rng) -> bool {
        rng.random_bool(self.variable_prob)
    }
}

struct ContextBFSIterator<'a, 'b> {
    pool: &'a RootedLambdaPool<Expr>,
    queue: VecDeque<(LambdaExprRef, Context<'b, 'a>)>,
}

impl<'a, 'b> Iterator for ContextBFSIterator<'a, 'b> {
    type Item = (LambdaExprRef, Context<'b, 'a>);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((x, context)) = self.queue.pop_front() {
            match self.pool.get(x) {
                LambdaExpr::Lambda(x, c) => {
                    let mut context = context.clone();
                    context.lambdas.push(c);
                    context.depth += 1;
                    self.queue.push_back((*x, context))
                }
                LambdaExpr::Application {
                    subformula,
                    argument,
                } => {
                    let mut context = context.clone();
                    context.depth += 1;
                    self.queue.push_back((*subformula, context.clone()));
                    self.queue.push_back((*argument, context));
                }
                LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                    var,
                    restrictor,
                    subformula,
                    ..
                }) => {
                    let mut context = context.clone();
                    context.available_vars.push(*var);
                    context.depth += 1;
                    self.queue
                        .push_back((LambdaExprRef(restrictor.0), context.clone()));
                    self.queue.push_back((LambdaExprRef(subformula.0), context));
                }
                LambdaExpr::LanguageOfThoughtExpr(x) => x.get_children().for_each(|x| {
                    let mut context = context.clone();
                    context.depth += 1;
                    self.queue.push_back((x, context))
                }),
                LambdaExpr::BoundVariable(..) | LambdaExpr::FreeVariable(..) => (),
            }
            Some((x, context))
        } else {
            None
        }
    }
}

impl RootedLambdaPool<Expr> {
    fn context_bfs_iter<'a, 'b: 'a>(
        &'a self,
        possible_expressions: &'b PossibleExpressions,
    ) -> ContextBFSIterator<'a, 'b> {
        let mut queue = VecDeque::new();
        queue.push_back((
            self.root,
            Context {
                lambdas: vec![],
                available_vars: vec![],
                possible_expressions,
                depth: 0,
            },
        ));
        ContextBFSIterator { pool: self, queue }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use chumsky::{error::Rich, extra};
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use crate::{LabelledScenarios, language::lot_parser};

    #[test]
    fn prune_quantifier_test() -> anyhow::Result<()> {
        let mut labels = LabelledScenarios::default();
        let parser = lot_parser::<extra::Err<Rich<_>>>().then_ignore(end());
        let mut pool = parser
            .parse("some_e(x0,all_e,AgentOf(a2,a1) & PatientOf(a0,a0))")
            .unwrap()
            .to_pool(&mut labels)?;

        pool.prune_quantifiers();
        assert_eq!(pool.to_string(), "(AgentOf(a2,a1) & PatientOf(a0,a0))");

        let mut pool = parser
            .parse("some_e(x0,all_e,some(z, all_a, AgentOf(z,e1) & PatientOf(a0,e0)))")
            .unwrap()
            .to_pool(&mut labels)?;

        pool.prune_quantifiers();
        assert_eq!(
            pool.to_string(),
            "some(y,all_a,(AgentOf(y,e1) & PatientOf(a0,e0)))"
        );

        let mut pool = parser
            .parse("~(every_e(z,pe1,pa2(a0)))")
            .unwrap()
            .to_pool(&mut labels)?;

        pool.prune_quantifiers();

        assert_eq!(pool.to_string(), "~(pa2(a0))");

        Ok(())
    }

    #[test]
    fn randomn_swap() -> anyhow::Result<()> {
        let mut rng = ChaCha8Rng::seed_from_u64(2);
        let actors = [0, 1];
        let available_actor_properties = [0, 1, 2];
        let available_event_properties = [2, 3, 4];
        for _ in 0..200 {
            let t = LambdaType::random_no_e(&mut rng);
            println!("{t}");
            let mut pool = RootedLambdaPool::random_expr(
                &t,
                &actors,
                &available_actor_properties,
                &available_event_properties,
                None,
                &mut rng,
            )?;
            println!("{}: {}", t, pool);
            assert_eq!(t, pool.get_type()?);
            pool.swap_expr(
                &actors,
                &available_actor_properties,
                &available_event_properties,
                &mut rng,
            );
            println!("{}: {}", t, pool);
            assert_eq!(t, pool.get_type()?);
        }
        Ok(())
    }
}
