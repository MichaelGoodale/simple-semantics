use std::{cmp::Reverse, collections::BinaryHeap};

use thiserror::Error;

use super::*;
use crate::lambda::{
    LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool, types::LambdaType,
};

mod context;
mod samplers;
use context::Context;
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
    Type(LambdaType, Option<usize>),
    Expr(LambdaExpr<'src, T>, Option<usize>),
}

impl<'src, T: LambdaLanguageOfThought> TryFrom<ExprOrType<'src, T>> for LambdaExpr<'src, T> {
    type Error = ExprOrTypeError;

    fn try_from(value: ExprOrType<'src, T>) -> Result<Self, Self::Error> {
        match value {
            ExprOrType::Type(..) => Err(ExprOrTypeError()),
            ExprOrType::Expr(lambda_expr, _) => Ok(lambda_expr),
        }
    }
}

impl<'src, T: LambdaLanguageOfThought> ExprOrType<'src, T> {
    fn parent(&self) -> Option<usize> {
        match self {
            ExprOrType::Type(_, p) | ExprOrType::Expr(_, p) => *p,
        }
    }

    fn is_type(&self) -> bool {
        matches!(self, ExprOrType::Type(..))
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

impl<'src, T: LambdaLanguageOfThought + Clone + std::fmt::Debug> UnfinishedLambdaPool<'src, T> {
    fn add_expr(&mut self, mut expr: LambdaExpr<'src, T>, c: &mut Context, t: &LambdaType) {
        c.depth += 1;
        c.open_nodes += expr.n_children();
        c.open_nodes -= 1;
        let parent = self.pool[c.position].parent();
        match &mut expr {
            LambdaExpr::Lambda(body, arg) => {
                c.add_lambda(arg);
                *body = LambdaExprRef(self.pool.len() as u32);
                self.pool
                    .push(ExprOrType::Type(t.rhs().unwrap().clone(), Some(c.position)))
            }
            LambdaExpr::BoundVariable(b, _) => {
                c.use_bvar(*b);
            }
            LambdaExpr::FreeVariable(..) => (),
            LambdaExpr::Application { .. } => {
                unimplemented!("No applications yet")
            }
            LambdaExpr::LanguageOfThoughtExpr(e) => {
                let children_start = self.pool.len();
                if let Some(t) = e.var_type() {
                    c.add_lambda(t);
                }
                self.pool.extend(
                    e.get_arguments()
                        .map(|x| ExprOrType::Type(x, Some(c.position))),
                );
                e.change_children(
                    (children_start..self.pool.len()).map(|x| LambdaExprRef(x as u32)),
                );
            }
        }
        self.pool[c.position] = ExprOrType::Expr(expr, parent);
    }
}

#[derive(Debug, Clone)]
pub struct LambdaSampler<'src, T: LambdaLanguageOfThought> {
    pools: Vec<UnfinishedLambdaPool<'src, T>>,
    pq: BinaryHeap<Reverse<Context>>,
    possible_expressions: PossibleExpressions<'src, T>,
}

impl<'src, T: std::fmt::Debug + LambdaLanguageOfThought + Clone> Iterator
    for LambdaSampler<'src, T>
{
    type Item = RootedLambdaPool<'src, T>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(Reverse(mut c)) = self.pq.pop() {
            let (possibles, lambda_type) = match &self.pools[c.pool_index].pool[c.position] {
                ExprOrType::Type(lambda_type, _) => (
                    self.possible_expressions.possibilities(lambda_type, &c),
                    lambda_type.clone(),
                ),
                ExprOrType::Expr(lambda_expr, p) => {
                    //We add the next uninitialized child to the context or go to the parent if
                    //there are none.

                    if let Some(child) = lambda_expr
                        .get_children()
                        .map(|x| x.0 as usize)
                        .find(|child| self.pools[c.pool_index].pool[*child].is_type())
                    {
                        c.position = child;
                        push_context(&mut self.pq, c);
                        continue;
                    }

                    if lambda_expr.inc_depth() {
                        c.pop_lambda();
                    }

                    if let Some(p) = p {
                        c.position = *p;
                        push_context(&mut self.pq, c);
                        continue;
                    } else {
                        //If the parent is None, we're done!
                        let root = LambdaExprRef(c.position as u32);
                        let p = std::mem::take(&mut self.pools[c.pool_index]);
                        return Some(RootedLambdaPool {
                            pool: LambdaPool(
                                p.pool
                                    .into_iter()
                                    .map(|x| LambdaExpr::try_from(x).unwrap())
                                    .collect(),
                            ),
                            root,
                        });
                    }
                }
            };
            let n = possibles.len();
            if n == 0 {
                panic!("There is no possible expression of type {lambda_type}");
            }
            let n_pools = self.pools.len();

            for _ in 0..n.saturating_sub(1) {
                self.pools.push(self.pools[c.pool_index].clone());
            }
            let positions =
                std::iter::once(c.pool_index).chain(n_pools..n_pools + n.saturating_sub(1));

            for ((expr, pool_id), mut c) in possibles
                .into_iter()
                .zip(positions)
                .zip(std::iter::repeat_n(c, n))
            {
                c.pool_index = pool_id;
                let pool = self.pools.get_mut(pool_id).unwrap();
                pool.add_expr(expr.into_owned(), &mut c, &lambda_type);
                push_context(&mut self.pq, c);
            }
        }
        None
    }
}

fn push_context(b: &mut BinaryHeap<Reverse<Context>>, context: Context) {
    b.push(Reverse(context))
}

impl<'src, T: Clone + LambdaLanguageOfThought> From<RootedLambdaPool<'src, T>>
    for UnfinishedLambdaPool<'src, T>
{
    fn from(mut value: RootedLambdaPool<'src, T>) -> Self {
        value.cleanup();
        let RootedLambdaPool { root, pool } = value;

        let mut pool: Vec<_> = pool
            .0
            .into_iter()
            .map(|expr| ExprOrType::Expr(expr, None))
            .collect();

        //Set parents
        let root = root.0 as usize;
        let mut stack = vec![(root, None)];
        while let Some((i, parent)) = stack.pop() {
            let ExprOrType::Expr(expr, e_parent) =
                pool.get_mut(i).expect("The pool was malformed!")
            else {
                panic!()
            };
            *e_parent = parent;
            stack.extend(expr.get_children().map(|x| (x.0 as usize, Some(i))));
        }

        Self { pool }
    }
}

impl<'src, T: LambdaLanguageOfThought + Clone> RootedLambdaPool<'src, T> {
    ///Create a [`LambdaSampler`] of a given type.
    pub fn sampler(
        t: &LambdaType,
        possible_expressions: PossibleExpressions<'src, T>,
    ) -> LambdaSampler<'src, T> {
        let context = Context::new(0, vec![]);
        let mut pq = BinaryHeap::default();
        pq.push(Reverse(context));
        let pools = vec![UnfinishedLambdaPool {
            pool: vec![ExprOrType::Type(t.clone(), None)],
        }];

        LambdaSampler {
            pools,
            possible_expressions,
            pq,
        }
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
}
/*

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
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                        quantifier,
                        var_type: actor_or_event,
                        restrictor: children.next().unwrap().into(),
                        subformula: children.next().unwrap().into(),
                    })
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
*/

#[cfg(test)]
mod test {
    use super::*;
    use crate::lambda::LambdaPool;
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
    fn randomn_swap() -> anyhow::Result<()> {
        let mut rng = ChaCha8Rng::seed_from_u64(2);
        let actors = ["0", "1"];
        let available_actor_properties = ["0", "1", "2"];
        let available_event_properties = ["2", "3", "4"];
        for _ in 0..2000 {
            let t = LambdaType::random_no_e(&mut rng);
            println!("{t}");
            let mut pool = todo!();
            /*
            println!("{t}: {pool}");
            assert_eq!(t, pool.get_type()?);
            pool.swap_expr(
                &actors,
                &available_actor_properties,
                &available_event_properties,
                &mut rng,
            )?;
            println!("{t}: {pool}");
            assert_eq!(t, pool.get_type()?);*/
        }
        Ok(())
    }

    #[test]
    fn randomness() -> anyhow::Result<()> {
        let mut rng = ChaCha8Rng::seed_from_u64(2);
        let actors = ["0", "1"];
        let available_actor_properties = ["0", "1", "2"];
        let available_event_properties = ["2", "3", "4"];
        let mut lengths = vec![0];
        for _ in 0..2000 {
            let t = LambdaType::random_no_e(&mut rng);
            todo!();
            /*
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
            let mut pool = pool.resample_from_expr(
                &actors,
                &available_actor_properties,
                &available_event_properties,
                None,
                &mut rng,
            )?;
            println!("{t}: {pool}");
            assert_eq!(t, pool.get_type()?);
            pool.prune_quantifiers();
            println!("{pool}");*/
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
        for _ in 0..2000 {
            let t = LambdaType::random_no_e(&mut rng);

            let pool: RootedLambdaPool<Expr> = todo!();

            let s = pool.to_string();
            let pool2 = RootedLambdaPool::parse(s.as_str())?;
            assert_eq!(s, pool2.to_string());
        }
        Ok(())
    }

    #[test]
    fn enumerate() -> anyhow::Result<()> {
        let actors = ["john"];
        let actor_properties = ["a"];
        let event_properties = ["e"];
        let possibles = PossibleExpressions::new(&actors, &actor_properties, &event_properties);
        let p = RootedLambdaPool::sampler(LambdaType::at(), possibles);
        let mut n = 0;
        for x in p.take(200) {
            println!("{x}");
            n += 1;
        }
        println!("{n}");
        panic!();

        Ok(())
    }

    #[test]
    fn convert_pool() -> anyhow::Result<()> {
        let phi = RootedLambdaPool::parse(
            "lambda e x lambda t phi every(y, pa_1, some(z, pa_0, pe_3(x)))",
        )?;

        let pool = UnfinishedLambdaPool::from(phi);

        Ok(())
    }
}
