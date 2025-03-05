use std::collections::{HashSet, VecDeque};

mod types;
use anyhow::{bail, Context};
use types::LambdaType;

use crate::lambda;

type Bvar = usize;
type Fvar = usize;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
struct LambdaExprRef(u32);

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum LambdaExpr<T> {
    Lambda(LambdaExprRef, LambdaType<T>),
    BoundVariable(Bvar, LambdaType<T>),
    FreeVariable(Fvar, LambdaType<T>),
    Application {
        subformula: LambdaExprRef,
        argument: LambdaExprRef,
    },
    LanguageOfThoughtExpr(T),
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct LambdaPool<T>(Vec<LambdaExpr<T>>);

impl<T> LambdaPool<T> {
    pub fn new() -> LambdaPool<T> {
        LambdaPool(vec![])
    }

    fn checked_get(&self, expr: LambdaExprRef) -> Option<&LambdaExpr<T>> {
        self.0.get(expr.0 as usize)
    }

    fn get(&self, expr: LambdaExprRef) -> &LambdaExpr<T> {
        &self.0[expr.0 as usize]
    }

    fn get_mut(&mut self, expr: LambdaExprRef) -> &mut LambdaExpr<T> {
        &mut self.0[expr.0 as usize]
    }

    pub fn add(&mut self, expr: LambdaExpr<T>) -> LambdaExprRef {
        let idx = self.0.len();
        self.0.push(expr);
        LambdaExprRef(idx.try_into().expect("Too many exprs in the pool"))
    }
}

struct LambdaPoolBFSIterator<'a, T> {
    pool: &'a LambdaPool<T>,
    queue: VecDeque<(LambdaExprRef, Bvar)>,
}

impl<T> Iterator for LambdaPoolBFSIterator<'_, T> {
    type Item = (LambdaExprRef, Bvar);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((x, lambda_depth)) = self.queue.pop_front() {
            match self.pool.get(x) {
                LambdaExpr::Lambda(x, _) => self.queue.push_back((*x, lambda_depth + 1)),
                LambdaExpr::Application {
                    subformula,
                    argument,
                } => {
                    self.queue.push_back((*subformula, lambda_depth));
                    self.queue.push_back((*argument, lambda_depth));
                }
                LambdaExpr::BoundVariable(..) | LambdaExpr::FreeVariable(..) => (),
                LambdaExpr::LanguageOfThoughtExpr(_) => todo!(),
            }
            Some((x, lambda_depth))
        } else {
            None
        }
    }
}

impl<T: Copy> LambdaPool<T> {
    fn bfs_from(&self, x: LambdaExprRef) -> LambdaPoolBFSIterator<T> {
        LambdaPoolBFSIterator {
            pool: self,
            queue: VecDeque::from([(x, 0)]),
        }
    }

    fn beta_reduce(&mut self, app: LambdaExprRef) -> anyhow::Result<()> {
        //BFS over all children and then replace debruijn k w/ argument ref where k is the number
        //of lambda abstractions we've gone under, e.g. (lambda 0 lambda 0 1)(u) -> lambda u lambda
        //1
        //
        //swap position of lambda ref and subformula ref so the lambda now leads to this.
        //
        let expr = self.checked_get(app).context("ExprRef goes nowhere!")?;

        let (inner_term, argument, subformula_vars) = if let LambdaExpr::Application {
            argument,
            subformula,
        } = expr
        {
            let inner_term = match self.get(*subformula) {
                LambdaExpr::Lambda(x, _lambda_type) => *x,
                _ => bail!("You can only beta reduce if the left hand side of the application is a lambda!")
            };

            (
                inner_term,
                *self.get(*argument),
                self.bfs_from(inner_term)
                    .filter(|(x, _)| matches!(self.get(*x), LambdaExpr::BoundVariable(..)))
                    .collect::<Vec<_>>(),
            )
        } else {
            bail!("ExprRef doesn't refer to a lambda")
        };
        for (x, lambda_depth) in subformula_vars.iter() {
            let val = self.get_mut(*x);
            println!("{:?} {:?}", x, lambda_depth);
            match val {
                LambdaExpr::BoundVariable(n, _lambda) if *n == *lambda_depth => *val = argument,
                LambdaExpr::BoundVariable(..) => (),
                _ => {
                    panic!("This should never happen because of the previous filter")
                }
            }
        }
        self.0.swap(inner_term.0 as usize, app.0 as usize);

        Ok(())
    }

    ///Iterates through a pool and de-allocates dangling refs and updates ExprRefs to new
    ///addresses. Basically garbage collection.
    fn cleanup(&mut self, root: LambdaExprRef) -> LambdaExprRef {
        let findable: HashSet<_> = self.bfs_from(root).map(|(x, _)| x.0 as usize).collect();
        let mut remap = (0..self.0.len()).collect::<Vec<_>>();
        let mut adjustment = 0;

        for i in remap.iter_mut() {
            if !findable.contains(i) {
                adjustment += 1;
            } else {
                *i -= adjustment;
            }
        }

        let mut i = 0;
        self.0.retain(|_| {
            i += 1;
            findable.contains(&(i - 1))
        });
        for x in self.0.iter_mut() {
            x.remap_refs(&remap);
        }
        LambdaExprRef(remap[root.0 as usize] as u32)
    }
}

impl<T> LambdaExpr<T> {
    fn remap_refs(&mut self, remap: &[usize]) {
        match self {
            LambdaExpr::Lambda(x, _) => {
                *x = LambdaExprRef(remap[x.0 as usize] as u32);
            }
            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                *subformula = LambdaExprRef(remap[subformula.0 as usize] as u32);
                *argument = LambdaExprRef(remap[argument.0 as usize] as u32);
            }
            LambdaExpr::BoundVariable(..) | LambdaExpr::FreeVariable(..) => (),
            LambdaExpr::LanguageOfThoughtExpr(_) => todo!(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn k<T: Default>(pos: u32) -> [LambdaExpr<T>; 3] {
        [
            LambdaExpr::Lambda(LambdaExprRef(pos + 1), LambdaType::default()),
            LambdaExpr::Lambda(LambdaExprRef(pos + 2), LambdaType::default()),
            LambdaExpr::BoundVariable(1, LambdaType::default()),
        ]
    }

    #[test]
    fn test_lambda_calculus() -> anyhow::Result<()> {
        let mut pool = LambdaPool::<()>(
            k(0).into_iter()
                .chain([
                    LambdaExpr::FreeVariable(32, LambdaType::default()),
                    LambdaExpr::Application {
                        subformula: LambdaExprRef(0),
                        argument: LambdaExprRef(3),
                    },
                ])
                .collect(),
        );
        let root = LambdaExprRef(4);
        pool.beta_reduce(root)?;
        let root = pool.cleanup(root);
        dbg!(&pool, root);

        assert_eq!(
            pool,
            LambdaPool(vec![
                LambdaExpr::FreeVariable(32, LambdaType::default()),
                LambdaExpr::Lambda(LambdaExprRef(0), LambdaType::default())
            ])
        );
        Ok(())
    }
}
