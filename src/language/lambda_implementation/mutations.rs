use std::collections::VecDeque;

use anyhow::bail;

use crate::{Actor, Event, PropertyLabel};

use super::*;

impl RootedLambdaPool<Expr> {
    pub fn resample_from_expr(
        self,
        available_actors: &[Actor],
        available_properties: &[PropertyLabel],
        config: Option<&RandomExprConfig>,
        rng: &mut impl Rng,
    ) -> Self {
        let config = config.unwrap_or(&DEFAULT_CONFIG);
        let position = LambdaExprRef(rng.random_range(0..self.len()) as u32);
        let mut pos_context = None;

        for (n, x) in self
            .context_bfs_iter(available_actors, available_properties)
            .enumerate()
        {
            if n == position.0 as usize {
                pos_context = Some(x);
                break;
            }
        }

        let (position, context) = pos_context.expect("Couldn't find the {position}th expression");
        let (root, pool) = (self.root, self.pool);

        let lambda_type = pool.get_type(position).unwrap();
        let mut pool: Vec<Option<LambdaExpr<Expr>>> = pool.into();
        pool[position.0 as usize] = None;

        let mut pool = build_out_pool(pool, lambda_type, position.0, context, config, rng);
        let root = pool.cleanup(root);

        RootedLambdaPool { pool, root }
    }

    pub fn random_expr(
        lambda_type: LambdaType,
        available_actors: &[Actor],
        available_properties: &[PropertyLabel],
        config: Option<&RandomExprConfig>,
        rng: &mut impl Rng,
    ) -> anyhow::Result<Self> {
        if lambda_type == LambdaType::E {
            bail!("There is no way to make a function with type E")
        }
        let pool = vec![None];

        let context = Context {
            lambdas: vec![],
            available_vars: vec![],
            available_actors,
            available_properties,
        };
        let config = config.unwrap_or(&DEFAULT_CONFIG);

        let pool = build_out_pool(pool, lambda_type, 0, context, config, rng);
        Ok(RootedLambdaPool::new(pool, LambdaExprRef(0)))
    }
}

fn build_out_pool(
    mut pool: Vec<Option<LambdaExpr<Expr>>>,
    lambda_type: LambdaType,
    start_pos: u32,
    context: Context,
    config: &RandomExprConfig,
    rng: &mut impl Rng,
) -> LambdaPool<Expr> {
    let mut fresher = Fresher::new(&pool);
    let e = Expr::get_new_from_type(lambda_type, &context, config, rng).unwrap();

    let mut stack = add_expr(e, start_pos, context, &mut fresher, &mut pool);

    while let Some((pos, lambda_type, context)) = stack.pop() {
        let e = Expr::get_new_from_type(lambda_type, &context, config, rng).unwrap();

        stack.extend(add_expr(e, pos, context, &mut fresher, &mut pool));
    }

    pool.try_into().unwrap()
}

#[derive(Debug, Clone)]
struct Context<'a> {
    lambdas: Vec<LambdaType>,
    available_vars: Vec<Variable>,
    available_actors: &'a [Actor],
    available_properties: &'a [PropertyLabel],
}

impl Context<'_> {
    fn can_sample_event(&self) -> bool {
        self.available_vars
            .iter()
            .any(|x| matches!(x, Variable::Event(_)))
            | self.lambdas.iter().any(|lam| *lam == LambdaType::E)
    }

    fn sample_actor(&self, rng: &mut impl Rng) -> Option<UnbuiltExpr> {
        self.available_actors
            .iter()
            .map(|x| UnbuiltExpr::Actor(*x))
            .chain(self.available_vars.iter().filter_map(|x| {
                if matches!(x, Variable::Actor(_)) {
                    Some(UnbuiltExpr::Variable(*x))
                } else {
                    None
                }
            }))
            .choose(rng)
    }

    fn sample_event(&self, rng: &mut impl Rng) -> Option<UnbuiltExpr> {
        self.available_vars
            .iter()
            .filter_map(|x| {
                if matches!(x, Variable::Event(_)) {
                    Some(UnbuiltExpr::Variable(*x))
                } else {
                    None
                }
            })
            .choose(rng)
    }

    fn sample_variable(&self, lambda_type: &LambdaType, rng: &mut impl Rng) -> Option<UnbuiltExpr> {
        let n = self.lambdas.len();
        self.lambdas
            .iter()
            .enumerate()
            .filter_map(|(i, t)| {
                if t == lambda_type {
                    Some(UnbuiltExpr::BoundVariable(n - i - 1, t.clone()))
                } else {
                    None
                }
            })
            .choose(rng)
    }
}

fn add_expr<'a>(
    e: UnbuiltExpr,
    pos: u32,
    mut context: Context<'a>,
    fresher: &mut Fresher,
    pool: &mut Vec<Option<LambdaExpr<Expr>>>,
) -> Vec<(u32, LambdaType, Context<'a>)> {
    let cur_size = pool.len() as u32 - 1;
    let mut children = vec![];
    let expr = match e {
        UnbuiltExpr::Quantifier(quantifier, actor_or_event) => {
            children.extend_from_slice(&[
                (
                    cur_size + 1,
                    match actor_or_event {
                        ActorOrEvent::Actor => LambdaType::at(),
                        ActorOrEvent::Event => LambdaType::et(),
                    },
                ),
                (cur_size + 2, LambdaType::T),
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
                BinOp::AgentOf | BinOp::PatientOf => {
                    [(cur_size + 1, LambdaType::E), (cur_size + 2, LambdaType::A)]
                }
                BinOp::And | BinOp::Or => {
                    [(cur_size + 1, LambdaType::T), (cur_size + 2, LambdaType::T)]
                }
            });
            LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(
                bin_op,
                ExprRef(cur_size + 1),
                ExprRef(cur_size + 2),
            ))
        }
        UnbuiltExpr::Unary(mon_op) => {
            children.push(match mon_op {
                MonOp::Property(_, ActorOrEvent::Actor) => (cur_size + 1, LambdaType::A),
                MonOp::Property(_, ActorOrEvent::Event) => (cur_size + 1, LambdaType::E),
                MonOp::Not | MonOp::Tautology | MonOp::Contradiction => {
                    (cur_size + 1, LambdaType::T)
                }
            });
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(mon_op, ExprRef(cur_size + 1)))
        }
        UnbuiltExpr::Constant(constant) => {
            LambdaExpr::LanguageOfThoughtExpr(Expr::Constant(constant))
        }
        UnbuiltExpr::Lambda(lambda_type) => {
            let (lhs, rhs) = lambda_type.split().unwrap();
            children.push((cur_size + 1, rhs));
            context.lambdas.push(lhs.clone());
            LambdaExpr::Lambda(LambdaExprRef(cur_size + 1), lhs)
        }
        UnbuiltExpr::BoundVariable(bvar, lambda_type) => {
            LambdaExpr::BoundVariable(bvar, lambda_type)
        }
    };

    pool[pos as usize] = Some(expr);
    pool.resize(pool.len() + children.len(), None);
    children
        .into_iter()
        .map(|(a, b)| (a, b, context.clone()))
        .collect()
}

//We never do applications since they would be redundant. Bound variables are not yet implemented.
#[derive(Debug, Clone)]
enum UnbuiltExpr {
    Quantifier(Quantifier, ActorOrEvent),
    Variable(Variable),
    Actor(Actor),
    Event(Event),
    Binary(BinOp),
    Unary(MonOp),
    Constant(Constant),
    Lambda(LambdaType),
    BoundVariable(Bvar, LambdaType),
}

#[derive(Debug, Copy, Clone, Default)]
struct Fresher(u32);

impl Fresher {
    fn fresh(&mut self, actor_or_event: ActorOrEvent) -> Variable {
        self.0 += 1;
        match actor_or_event {
            ActorOrEvent::Actor => Variable::Actor(self.0),
            ActorOrEvent::Event => Variable::Event(self.0),
        }
    }

    fn new(pool: &[Option<LambdaExpr<Expr>>]) -> Self {
        Fresher(
            pool.iter()
                .filter_map(|x| match x {
                    Some(LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(v))) => Some(v.id()),
                    Some(LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier { var, .. })) => {
                        Some(var.id())
                    }
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

impl Expr {
    fn get_new_from_type(
        lambda_type: LambdaType,
        context: &Context,
        config: &RandomExprConfig,
        rng: &mut impl Rng,
    ) -> anyhow::Result<UnbuiltExpr> {
        if config.is_lambda(&lambda_type, rng) {
            return Ok(UnbuiltExpr::Lambda(lambda_type));
        }
        if config.is_variable(rng) {
            let x = context.sample_variable(&lambda_type, rng);
            if let Some(x) = x {
                return Ok(x);
            }
        }

        let expr =
            if lambda_type == LambdaType::at() {
                let mut options = [Constant::Everyone].map(UnbuiltExpr::Constant).to_vec();

                options.extend(
                    context.available_properties.iter().map(|i| {
                        UnbuiltExpr::Constant(Constant::Property(*i, ActorOrEvent::Actor))
                    }),
                );
                let choice = (0..options.len()).choose(rng).unwrap();
                Some(options.remove(choice))
            } else if lambda_type == LambdaType::et() {
                let mut options = [Constant::EveryEvent].map(UnbuiltExpr::Constant).to_vec();

                options.extend(
                    context.available_properties.iter().map(|i| {
                        UnbuiltExpr::Constant(Constant::Property(*i, ActorOrEvent::Event))
                    }),
                );
                let choice = (0..options.len()).choose(rng).unwrap();
                Some(options.remove(choice))
            } else {
                match lambda_type {
                    LambdaType::T => {
                        let mut options: Vec<UnbuiltExpr> = vec![
                            UnbuiltExpr::Unary(MonOp::Not),
                            UnbuiltExpr::Binary(BinOp::And),
                            UnbuiltExpr::Binary(BinOp::Or),
                            UnbuiltExpr::Quantifier(Quantifier::Existential, ActorOrEvent::Actor),
                            UnbuiltExpr::Quantifier(Quantifier::Universal, ActorOrEvent::Actor),
                            UnbuiltExpr::Quantifier(Quantifier::Existential, ActorOrEvent::Event),
                            UnbuiltExpr::Quantifier(Quantifier::Universal, ActorOrEvent::Event),
                        ];
                        options.extend(
                            context.available_properties.iter().map(|i| {
                                UnbuiltExpr::Unary(MonOp::Property(*i, ActorOrEvent::Actor))
                            }),
                        );

                        if context.can_sample_event() {
                            options.push(UnbuiltExpr::Binary(BinOp::AgentOf));
                            options.push(UnbuiltExpr::Binary(BinOp::PatientOf));
                            options.extend(context.available_properties.iter().map(|i| {
                                UnbuiltExpr::Unary(MonOp::Property(*i, ActorOrEvent::Event))
                            }));
                        }

                        let choice = (0..options.len()).choose(rng).unwrap();
                        Some(options.remove(choice))
                    }
                    LambdaType::A => context.sample_actor(rng),
                    LambdaType::E => context.sample_event(rng),
                    _ => None,
                }
            };

        match expr {
            Some(expr) => Ok(expr),
            None => {
                if lambda_type.is_function() {
                    Ok(UnbuiltExpr::Lambda(lambda_type))
                } else if let Some(x) = context.sample_variable(&lambda_type, rng) {
                    Ok(x)
                } else {
                    bail!("Could not find expr of type {lambda_type}");
                }
            }
        }
    }
}

struct ContextBFSIterator<'a, 'b> {
    pool: &'a RootedLambdaPool<Expr>,
    queue: VecDeque<(LambdaExprRef, Context<'b>)>,
}

impl<'b> Iterator for ContextBFSIterator<'_, 'b> {
    type Item = (LambdaExprRef, Context<'b>);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((x, context)) = self.queue.pop_front() {
            match self.pool.get(x) {
                LambdaExpr::Lambda(x, c) => {
                    let mut context = context.clone();
                    context.lambdas.push(c.clone());
                    self.queue.push_back((*x, context))
                }
                LambdaExpr::Application {
                    subformula,
                    argument,
                } => {
                    self.queue.push_back((*subformula, context.clone()));
                    self.queue.push_back((*argument, context.clone()));
                }
                LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                    var,
                    restrictor,
                    subformula,
                    ..
                }) => {
                    let mut context = context.clone();
                    context.available_vars.push(*var);
                    self.queue
                        .push_back((LambdaExprRef(restrictor.0), context.clone()));
                    self.queue.push_back((LambdaExprRef(subformula.0), context));
                }
                LambdaExpr::LanguageOfThoughtExpr(x) => x
                    .get_children()
                    .for_each(|x| self.queue.push_back((x, context.clone()))),
                LambdaExpr::BoundVariable(..) | LambdaExpr::FreeVariable(..) => (),
            }
            Some((x, context))
        } else {
            None
        }
    }
}

impl RootedLambdaPool<Expr> {
    fn context_bfs_iter<'a, 'b>(
        &'a self,
        available_actors: &'b [Actor],
        available_properties: &'b [PropertyLabel],
    ) -> ContextBFSIterator<'a, 'b> {
        let mut queue = VecDeque::new();
        queue.push_back((
            self.root,
            Context {
                lambdas: vec![],
                available_vars: vec![],
                available_actors,
                available_properties,
            },
        ));
        ContextBFSIterator { pool: self, queue }
    }
}
