use std::collections::VecDeque;

use rand::{Rng, seq::IteratorRandom};
use thiserror::Error;

use super::*;
use crate::{
    Actor, Event, PropertyLabel,
    lambda::{
        Bvar, ExpressionType, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool,
        types::LambdaType,
    },
    language::mutations::samplers::SamplingError,
};

mod context;
mod samplers;
mod unbuilt;
use context::Context;
use samplers::PossibleExpressions;
pub use samplers::RandomExprConfig;
use unbuilt::{Fresher, UnbuiltExpr, add_expr};

#[derive(Debug, Error, Clone)]
pub enum MutationError {
    #[error("You cannot make an expression that returns 'e'")]
    InvalidType,

    #[error("Sampling Error: {0}")]
    SamplingError(#[from] SamplingError),
}

impl<'src> RootedLambdaPool<'src, Expr<'src>> {
    fn get_context_for_expr(&self, position: LambdaExprRef) -> Option<Context> {
        let mut pos_context = None;

        for (n, c) in self.context_bfs_iter() {
            if n == position {
                pos_context = Some(c);
                break;
            }
        }
        pos_context
    }

    ///Choose a random expression and resample its children.
    pub fn resample_from_expr(
        self,
        available_actors: &[Actor<'src>],
        available_actor_properties: &[PropertyLabel<'src>],
        available_event_properties: &[PropertyLabel<'src>],
        config: Option<RandomExprConfig>,
        rng: &mut impl Rng,
    ) -> Result<Self, MutationError> {
        let config = &config.unwrap_or_default();
        let position = LambdaExprRef(rng.random_range(0..self.len()) as u32);

        let possible_expressions = PossibleExpressions::new(
            available_actors,
            available_actor_properties,
            available_event_properties,
            config,
        );

        let context = self
            .get_context_for_expr(position)
            .expect("Couldn't find the {position}th expression");

        //Here we extract the lambdas and reborrow them to avoid borrowing crap.
        let lambdas = context
            .lambdas()
            .iter()
            .map(|x| (*x).clone())
            .collect::<Vec<_>>();
        let context = context.into_owned_lambdas(&lambdas);

        let (root, pool) = (self.root, self.pool);

        let lambda_type = pool.get_type(position).unwrap();
        let mut pool: Vec<Option<LambdaExpr<_>>> = pool.into();
        pool[position.0 as usize] = None;

        let mut pool = build_out_pool(
            pool,
            &lambda_type,
            position.0,
            context,
            possible_expressions,
            rng,
        )?;
        let root = pool.cleanup(root);

        Ok(RootedLambdaPool { pool, root })
    }

    ///Create a random expression of `lambda_type`.
    pub fn random_expr(
        lambda_type: &LambdaType,
        available_actors: &[Actor<'src>],
        available_actor_properties: &[PropertyLabel<'src>],
        available_event_properties: &[PropertyLabel<'src>],
        config: Option<RandomExprConfig>,
        rng: &mut impl Rng,
    ) -> Result<Self, MutationError> {
        if lambda_type == LambdaType::e() {
            return Err(MutationError::InvalidType);
        }
        let pool = vec![None];
        let config = &config.unwrap_or_default();

        let possible_expressions = PossibleExpressions::new(
            available_actors,
            available_actor_properties,
            available_event_properties,
            config,
        );
        let context = Context::default();
        let pool = build_out_pool(pool, lambda_type, 0, context, possible_expressions, rng)?;
        Ok(RootedLambdaPool::new(pool, LambdaExprRef(0)))
    }

    ///Remove quantifiers which do not use their variable in their body.
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
                var_type: var,
                subformula,
                ..
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

    ///Replace a random expression with something else of the same type.
    pub fn swap_expr(
        &mut self,
        available_actors: &[Actor<'src>],
        available_actor_properties: &[PropertyLabel<'src>],
        available_event_properties: &[PropertyLabel<'src>],
        rng: &mut impl Rng,
    ) -> Result<(), SamplingError> {
        let config = RandomExprConfig::default();
        let position = LambdaExprRef((0..self.len()).choose(rng).unwrap() as u32);
        let possible_expressions = PossibleExpressions::new(
            available_actors,
            available_actor_properties,
            available_event_properties,
            &config,
        );

        let context = self
            .get_context_for_expr(position)
            .unwrap_or_else(|| panic!("Couldn't find {}th expr!", position.0));
        let ExpressionType { output, arguments } = self.get_expression_type(position).unwrap();
        let replacement = possible_expressions
            .possiblities_fixed_children(&output, &arguments, &context)?
            .choose(rng)?;

        let new_expr = {
            let mut children = self.get(position).get_children();
            match replacement {
                UnbuiltExpr::Quantifier(quantifier, actor_or_event) => {
                    let mut fresher = Fresher::new_rooted(self);
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                        quantifier,
                        var_type: fresher.fresh(actor_or_event),
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

        Ok(())
    }
}

fn build_out_pool<'src, 'typ>(
    mut pool: Vec<Option<LambdaExpr<'src, Expr<'src>>>>,
    lambda_type: &'typ LambdaType,
    start_pos: u32,
    context: Context<'typ>,
    possible_expressions: PossibleExpressions<'src, 'typ, '_>,
    rng: &mut impl Rng,
) -> Result<LambdaPool<'src, Expr<'src>>, SamplingError> {
    let mut fresher = Fresher::new(&pool);
    let e = possible_expressions
        .possibilities(lambda_type, &context)?
        .choose(rng)?;

    let mut stack = add_expr(e, start_pos, context, &mut fresher, &mut pool);

    while let Some((pos, lambda_type, context)) = stack.pop() {
        let e = possible_expressions
            .possibilities(lambda_type, &context)?
            .choose(rng)?;

        stack.extend(add_expr(e, pos, context, &mut fresher, &mut pool));
    }
    Ok(pool.try_into().unwrap())
}

#[cfg(test)]
mod test {
    use super::*;
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

        Ok(())
    }

    #[test]
    fn randomn_swap() -> anyhow::Result<()> {
        let mut rng = ChaCha8Rng::seed_from_u64(2);
        let actors = ["0", "1"];
        let available_actor_properties = ["0", "1", "2"];
        let available_event_properties = ["2", "3", "4"];
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
            println!("{t}: {pool}");
            assert_eq!(t, pool.get_type()?);
            pool.swap_expr(
                &actors,
                &available_actor_properties,
                &available_event_properties,
                &mut rng,
            )?;
            println!("{t}: {pool}");
            assert_eq!(t, pool.get_type()?);
        }
        Ok(())
    }

    #[test]
    fn randomness() -> anyhow::Result<()> {
        let mut rng = ChaCha8Rng::seed_from_u64(2);
        let actors = ["0", "1"];
        let available_actor_properties = ["0", "1", "2"];
        let available_event_properties = ["2", "3", "4"];
        let mut lengths = vec![];
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
            lengths.push(pool.len());
            println!("{t}: {pool}");
            assert_eq!(t, pool.get_type()?);
            let pool = pool.resample_from_expr(
                &actors,
                &available_actor_properties,
                &available_event_properties,
                None,
                &mut rng,
            )?;
            println!("{t}: {pool}");
            assert_eq!(t, pool.get_type()?);
        }
        println!("{lengths:?}");
        Ok(())
    }

    #[test]
    fn reparse_random() -> anyhow::Result<()> {
        let mut rng = ChaCha8Rng::seed_from_u64(2);
        let actors = ["0", "1"];
        let available_actor_properties = ["0", "1", "2"];
        let available_event_properties = ["2", "3", "4"];
        for _ in 0..200 {
            let t = LambdaType::random_no_e(&mut rng);
            let pool = RootedLambdaPool::random_expr(
                &t,
                &actors,
                &available_actor_properties,
                &available_event_properties,
                None,
                &mut rng,
            )?;

            let s = pool.to_string();
            let pool2 = RootedLambdaPool::parse(s.as_str())?;
            assert_eq!(s, pool2.to_string());
        }
        Ok(())
    }
}
