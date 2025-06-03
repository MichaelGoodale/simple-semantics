use std::{
    borrow::Cow,
    collections::{VecDeque, hash_map::Entry},
    iter::repeat_n,
};

use ahash::HashMap;
use rand::{
    Rng,
    seq::{IndexedRandom, IteratorRandom},
};
use thiserror::Error;

use super::*;
use crate::{
    Actor, Event, PropertyLabel,
    lambda::{
        Bvar, ExpressionType, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool,
        types::LambdaType,
    },
};

mod context;
mod samplers;
mod unbuilt;
use context::Context;
use unbuilt::{Fresher, UnbuiltExpr, add_expr};

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
        config: Option<RandomExprConfig>,
        rng: &mut impl Rng,
    ) -> Self {
        let config = &config.unwrap_or_default();
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
        let lambdas = context
            .lambdas()
            .iter()
            .map(|x| (*x).clone())
            .collect::<Vec<_>>();
        let context = context.to_owned_lambdas(&lambdas, &possible_expressions);

        let (root, pool) = (self.root, self.pool);

        let lambda_type = pool.get_type(position).unwrap();
        let mut pool: Vec<Option<LambdaExpr<_>>> = pool.into();
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
        config: Option<RandomExprConfig>,
        rng: &mut impl Rng,
    ) -> Result<Self, MutationError> {
        if lambda_type == LambdaType::e() {
            return Err(MutationError::InvalidType);
        }
        let pool = vec![None];

        let possible_expressions = PossibleExpressions::new(
            available_actors,
            available_actor_properties,
            available_event_properties,
        );
        let context = Context::new(&possible_expressions);
        let config = &config.unwrap_or_default();

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

/*
#[derive(Debug, Copy, Clone)]
enum SampleDetails {
    LambdaExpr,
    LambdaVar,
    QuantifierVar(Variable),
    Other(u8),
}

impl SampleDetails {
    fn new(e: &UnbuiltExpr, n_args: usize) -> {
        match e {
            UnbuiltExpr::Quantifier(quantifier, actor_or_event) => todo!(),
            UnbuiltExpr::Variable(variable) => todo!(),
            UnbuiltExpr::Actor(_) => todo!(),
            UnbuiltExpr::Event(_) => todo!(),
            UnbuiltExpr::Binary(bin_op) => todo!(),
            UnbuiltExpr::Unary(mon_op) => todo!(),
            UnbuiltExpr::Constant(constant) => todo!(),
            UnbuiltExpr::Lambda(lambda_type, lambda_type1) => todo!(),
            UnbuiltExpr::BoundVariable(_, lambda_type) => todo!(),
        }
    }
}
*/
fn has_e_argument(v: &[LambdaType]) -> bool {
    v.iter().any(|v| v == LambdaType::e())
}

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

#[cfg(test)]
mod test {
    use super::*;
    use chumsky::prelude::*;
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

    #[test]
    fn randomness() -> anyhow::Result<()> {
        let mut rng = ChaCha8Rng::seed_from_u64(2);
        let actors = [0, 1];
        let available_actor_properties = [0, 1, 2];
        let available_event_properties = [2, 3, 4];
        for _ in 0..200 {
            let t = LambdaType::random_no_e(&mut rng);
            println!("{t}");
            let pool = RootedLambdaPool::random_expr(
                &t,
                &actors,
                &available_actor_properties,
                &available_event_properties,
                None,
                &mut rng,
            )?;
            println!("{}: {}", t, pool);
            assert_eq!(t, pool.get_type()?);
            let pool = pool.resample_from_expr(
                &actors,
                &available_actor_properties,
                &available_event_properties,
                None,
                &mut rng,
            );
            println!("{}: {}", t, pool);
            assert_eq!(t, pool.get_type()?);
        }
        Ok(())
    }
}
