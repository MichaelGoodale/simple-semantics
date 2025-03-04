use std::collections::{HashSet, VecDeque};

use anyhow::{bail, Context};

use super::{Expr, ExprPool, ExprRef, Variable};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Lambda {}

struct ExprPoolBFSIterator<'a> {
    pool: &'a ExprPool,
    queue: VecDeque<ExprRef>,
}

impl Iterator for ExprPoolBFSIterator<'_> {
    type Item = ExprRef;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(x) = self.queue.pop_front() {
            match self.pool.get(x) {
                Expr::Quantifier {
                    restrictor,
                    subformula,
                    ..
                } => {
                    self.queue.push_back(*restrictor);
                    self.queue.push_back(*subformula);
                }
                Expr::Lambda {
                    argument,
                    subformula,
                    ..
                } => {
                    self.queue.push_back(*subformula);
                    if let Some(argument) = argument {
                        self.queue.push_back(*argument);
                    }
                }
                Expr::Binary(_, x, y) => {
                    self.queue.push_back(*x);
                    self.queue.push_back(*y);
                }
                Expr::Unary(_, x) => self.queue.push_back(*x),
                Expr::DebruijnIndex(_)
                | Expr::BoundVariable(_)
                | Expr::Entity(_)
                | Expr::Constant(_) => (),
            }
            Some(x)
        } else {
            None
        }
    }
}

impl ExprPool {
    fn bfs_from(&self, x: ExprRef) -> ExprPoolBFSIterator {
        ExprPoolBFSIterator {
            pool: self,
            queue: VecDeque::from([x]),
        }
    }

    fn beta_reduce(&mut self, lambda: ExprRef) -> anyhow::Result<()> {
        //BFS over all children and then replace debruijn 0 w/ argument ref and reduce all other
        //debruijn indices by 1.
        //
        //swap position of lambda ref and subformula ref so the lambda now leads to this.
        //
        let expr = self.checked_get(lambda).context("ExprRef goes nowhere!")?;
        let (subformula, argument, subformula_debruijns) = if let Expr::Lambda {
            lambda: _,
            argument,
            subformula,
        } = expr
        {
            (
                *subformula,
                *self.get(argument.context("Can't beta-reduce if there is no argument!")?),
                self.bfs_from(*subformula)
                    .filter(|x| matches!(self.get(*x), Expr::DebruijnIndex(_)))
                    .collect::<Vec<_>>(),
            )
        } else {
            bail!("ExprRef doesn't refer to a lambda")
        };

        for x in subformula_debruijns.iter() {
            let val = self.get_mut(*x);
            if let Expr::DebruijnIndex(Variable(n)) = *val {
                *val = if n == 0 {
                    argument
                } else {
                    Expr::DebruijnIndex(Variable(n - 1))
                };
            } else {
                panic!("This should never happen because of the previous filter")
            }
        }

        self.0.swap(subformula.0 as usize, lambda.0 as usize);

        Ok(())
    }

    ///Iterates through a pool and de-allocates dangling refs and updates ExprRefs to new
    ///addresses. Basically garbage collection.
    fn cleanup(&mut self, root: ExprRef) {
        let findable: HashSet<_> = self.bfs_from(root).map(|x| x.0 as usize).collect();
        let mut remap = (0..self.0.len()).collect::<Vec<_>>();
        let mut adjustment = 0;
        for i in remap.iter_mut() {
            if !findable.contains(i) {
                adjustment += 1;
            }
            *i -= adjustment;
        }

        let mut i = 0;
        self.0.retain(|_| {
            i += 1;
            findable.contains(&(i - 1))
        });
        for x in self.0.iter_mut() {
            x.remap_refs(&remap);
        }
    }
}

impl Expr {
    fn remap_refs(&mut self, remap: &[usize]) {
        match self {
            Expr::Quantifier {
                restrictor,
                subformula,
                ..
            } => {
                *restrictor = ExprRef(remap[restrictor.0 as usize] as u32);
                *subformula = ExprRef(remap[subformula.0 as usize] as u32);
            }
            Expr::Lambda {
                argument,
                subformula,
                ..
            } => {
                *argument = argument.map(|x| ExprRef(remap[x.0 as usize] as u32));
                *subformula = ExprRef(remap[subformula.0 as usize] as u32);
            }
            Expr::Binary(_, x, y) => {
                *x = ExprRef(remap[x.0 as usize] as u32);
                *y = ExprRef(remap[y.0 as usize] as u32);
            }
            Expr::Unary(_, x) => *x = ExprRef(remap[x.0 as usize] as u32),
            Expr::DebruijnIndex(_)
            | Expr::BoundVariable(_)
            | Expr::Entity(_)
            | Expr::Constant(_) => (),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        language::{Expr, ExprPool, MonOp, Variable},
        Entity, LabelledScenarios,
    };

    #[test]
    fn check_beta_reduction() -> anyhow::Result<()> {
        let scenario = LabelledScenarios::parse("<m (p)>").unwrap();
        let mut pool = ExprPool(vec![
            Expr::Lambda {
                lambda: Lambda {},
                argument: Some(ExprRef(1)),
                subformula: ExprRef(2),
            },
            Expr::Entity(Entity::Actor(*scenario.actor_labels.get("m").unwrap())),
            Expr::Unary(
                MonOp::Property(*scenario.property_labels.get("p").unwrap()),
                ExprRef(3),
            ),
            Expr::DebruijnIndex(Variable(0)),
        ]);

        pool.beta_reduce(ExprRef(0))?;
        dbg!(&pool);

        let uncleaned = ExprPool(vec![
            Expr::Unary(MonOp::Property(0), ExprRef(3)),
            Expr::Entity(Entity::Actor(0)),
            Expr::Lambda {
                lambda: Lambda {},
                argument: Some(ExprRef(1)),
                subformula: ExprRef(2),
            },
            Expr::Entity(Entity::Actor(0)),
        ]);
        assert_eq!(pool, uncleaned);
        pool.cleanup(ExprRef(0));
        let cleaned = ExprPool(vec![
            Expr::Unary(MonOp::Property(0), ExprRef(1)),
            Expr::Entity(Entity::Actor(0)),
        ]);
        assert_eq!(pool, cleaned);
        Ok(())
    }
}
