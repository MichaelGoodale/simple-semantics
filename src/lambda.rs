use std::collections::{HashSet, VecDeque};

mod types;
use anyhow::{bail, Context};
use types::LambdaType;

type Bvar = usize;
type Fvar = usize;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
struct LambdaExprRef(u32);

#[derive(Debug, Clone, Eq, PartialEq)]
enum LambdaExpr<T> {
    Lambda(LambdaExprRef, LambdaType),
    BoundVariable(Bvar, LambdaType),
    FreeVariable(Fvar, LambdaType),
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

    fn get_type(&self, x: LambdaExprRef) -> LambdaType {
        match self.get(x) {
            LambdaExpr::Lambda(_, x)
            | LambdaExpr::BoundVariable(_, x)
            | LambdaExpr::FreeVariable(_, x) => x.clone(),
            LambdaExpr::Application {
                subformula,
                argument: _,
            } => self.get_type(*subformula).apply(),
            LambdaExpr::LanguageOfThoughtExpr(_) => todo!(),
        }
    }

    fn types_clash(&self, lambda_type: &LambdaType, rhs: LambdaExprRef) -> bool {
        let rhs_type = self.get_type(rhs);
        !lambda_type.can_apply(&rhs_type)
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
                LambdaExpr::Lambda(x, lambda_type) => {

                    if self.types_clash(lambda_type, *argument) {
                        bail!("Type clash!");
                    }

                *x},
                _ => bail!("You can only beta reduce if the left hand side of the application is a lambda!")
            };

            (
                inner_term,
                self.get(*argument).clone(),
                self.bfs_from(inner_term)
                    .filter(|(x, _)| matches!(self.get(*x), LambdaExpr::BoundVariable(..)))
                    .collect::<Vec<_>>(),
            )
        } else {
            bail!("ExprRef doesn't refer to a lambda")
        };
        for (x, lambda_depth) in subformula_vars.iter() {
            let val = self.get_mut(*x);
            match val {
                LambdaExpr::BoundVariable(n, _lambda) if *n == *lambda_depth => {
                    *val = argument.clone()
                }
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

    fn get_next_app(&self, root: LambdaExprRef) -> Option<LambdaExprRef> {
        self.bfs_from(root)
            .map(|(x, _)| x)
            .find(|x| matches!(self.get(*x), LambdaExpr::Application { .. }))
    }

    fn reduce(&mut self, root: LambdaExprRef) -> anyhow::Result<()> {
        if let Some(x) = self.get_next_app(root) {
            self.beta_reduce(x)?;
            let new_i = self.cleanup(x);
            self.reduce(new_i)?;
        }
        Ok(())
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

    fn k<T: Default>(pos: u32) -> anyhow::Result<[LambdaExpr<T>; 3]> {
        Ok([
            LambdaExpr::Lambda(
                LambdaExprRef(pos + 1),
                LambdaType::from_string("<e, <e,e>>")?,
            ),
            LambdaExpr::Lambda(LambdaExprRef(pos + 2), LambdaType::from_string("<e,e>")?),
            LambdaExpr::BoundVariable(1, LambdaType::E),
        ])
    }

    #[test]
    fn complicated_lambda() -> anyhow::Result<()> {
        // [[[Mary sings] and]  [John dances]]
        let mut pool = LambdaPool::<()>(vec![
            LambdaExpr::Application {
                subformula: LambdaExprRef(5),
                argument: LambdaExprRef(1),
            },
            LambdaExpr::Application {
                //John dances
                subformula: LambdaExprRef(2),
                argument: LambdaExprRef(4),
            },
            LambdaExpr::Lambda(LambdaExprRef(3), LambdaType::et()),
            LambdaExpr::FreeVariable(0, LambdaType::T),
            LambdaExpr::FreeVariable(2, LambdaType::E),
            // 5
            //\lambda x. Mary sings and
            LambdaExpr::Lambda(LambdaExprRef(6), LambdaType::from_string("<t,t>")?),
            LambdaExpr::Application {
                subformula: LambdaExprRef(7),
                argument: LambdaExprRef(10),
            },
            LambdaExpr::Lambda(LambdaExprRef(8), LambdaType::from_string("<t, <t,t>>")?),
            LambdaExpr::Lambda(LambdaExprRef(9), LambdaType::from_string("<t,t>")?),
            LambdaExpr::BoundVariable(1, LambdaType::T),
            LambdaExpr::Application {
                //10
                subformula: LambdaExprRef(11),
                argument: LambdaExprRef(13),
            },
            LambdaExpr::Lambda(LambdaExprRef(12), LambdaType::et()),
            LambdaExpr::FreeVariable(1337, LambdaType::T),
            LambdaExpr::FreeVariable(5, LambdaType::E),
        ]);
        pool.reduce(LambdaExprRef(0))?;
        assert_eq!(
            pool,
            LambdaPool(vec![LambdaExpr::FreeVariable(1337, LambdaType::T)])
        );
        Ok(())
    }

    #[test]
    fn test_lambda_calculus() -> anyhow::Result<()> {
        let mut pool = LambdaPool::<()>(
            k(0)?
                .into_iter()
                .chain([
                    LambdaExpr::FreeVariable(32, LambdaType::E),
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
                LambdaExpr::FreeVariable(32, LambdaType::E),
                LambdaExpr::Lambda(LambdaExprRef(0), LambdaType::from_string("<e,e>")?)
            ])
        );
        Ok(())
    }
}
