use anyhow::{bail, Context};
use std::collections::{HashSet, VecDeque};

pub mod types;
use types::LambdaType;

type Bvar = usize;
type Fvar = usize;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LambdaExprRef(pub u32);

pub trait LambdaLanguageOfThought {
    type Pool;
    fn get_children(&self) -> impl Iterator<Item = LambdaExprRef>;
    fn remap_refs(&mut self, remap: &[usize]);
    fn get_type(&self) -> LambdaType;
    fn to_pool(pool: Vec<Self>, root: LambdaExprRef) -> Self::Pool
    where
        Self: Sized;
}

impl LambdaLanguageOfThought for () {
    type Pool = ();
    fn get_children(&self) -> impl Iterator<Item = LambdaExprRef> {
        std::iter::empty()
    }
    fn remap_refs(&mut self, _: &[usize]) {}

    fn get_type(&self) -> LambdaType {
        unimplemented!()
    }

    fn to_pool(_: Vec<Self>, _: LambdaExprRef) -> Self::Pool {}
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum LambdaExpr<T> {
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
pub struct LambdaPool<T: LambdaLanguageOfThought>(Vec<LambdaExpr<T>>);

impl<T: LambdaLanguageOfThought + Sized> LambdaPool<T> {
    pub fn into_pool(self, root: LambdaExprRef) -> anyhow::Result<T::Pool> {
        let processed_pool = self
            .0
            .into_iter()
            .map(|x| match x {
                LambdaExpr::LanguageOfThoughtExpr(x) => Ok(x),
                _ => bail!("Cannot turn into LOT expression, there are still lambda terms!"),
            })
            .collect::<anyhow::Result<Vec<_>>>()?;
        Ok(T::to_pool(processed_pool, root))
    }

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

struct LambdaPoolBFSIterator<'a, T: LambdaLanguageOfThought> {
    pool: &'a LambdaPool<T>,
    queue: VecDeque<(LambdaExprRef, Bvar)>,
}

impl<T: LambdaLanguageOfThought> Iterator for LambdaPoolBFSIterator<'_, T> {
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
                LambdaExpr::LanguageOfThoughtExpr(x) => x
                    .get_children()
                    .for_each(|x| self.queue.push_back((x, lambda_depth))),
            }
            Some((x, lambda_depth))
        } else {
            None
        }
    }
}

impl<T: LambdaLanguageOfThought + std::fmt::Debug> LambdaPool<T>
where
    T: Clone,
{
    fn bfs_from(&self, x: LambdaExprRef) -> LambdaPoolBFSIterator<T> {
        LambdaPoolBFSIterator {
            pool: self,
            queue: VecDeque::from([(x, 0)]),
        }
    }

    ///This function trusts that the subexpressions are all valid! For example if a lambda's body
    ///has the wrong type, it won't know.
    fn check_type_clash(&self, x: LambdaExprRef) -> Option<LambdaType> {
        match self.get(x) {
            LambdaExpr::BoundVariable(_, x)
            | LambdaExpr::FreeVariable(_, x)
            | LambdaExpr::Lambda(.., x) => Some(x.clone()),
            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                if let Some(lhs_type) = self.check_type_clash(*argument) {
                    if let Some(subformula) = self.check_type_clash(*subformula) {
                        if subformula.can_apply(&lhs_type) {
                            Some(subformula.apply())
                        } else {
                            //The subformula has a type clash
                            None
                        }
                    } else {
                        //The subformula has a type clash
                        None
                    }
                } else {
                    //The argument has a type clash
                    None
                }
            }
            LambdaExpr::LanguageOfThoughtExpr(x) => Some(x.get_type()),
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
                LambdaExpr::Lambda(x,..) => {

                    if self.check_type_clash(app).is_none() {
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
            .find(|x| match self.get(*x) {
                LambdaExpr::Application { subformula, .. } => {
                    matches!(self.get(*subformula), LambdaExpr::Lambda(..))
                }
                _ => false,
            })
    }

    pub fn reduce(&mut self, root: LambdaExprRef) -> anyhow::Result<LambdaExprRef> {
        if let Some(x) = self.get_next_app(root) {
            self.beta_reduce(x)?;
            let new_root = self.cleanup(root);
            Ok(self.reduce(new_root)?)
        } else {
            Ok(root)
        }
    }
}

impl<T: LambdaLanguageOfThought> LambdaExpr<T> {
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
            LambdaExpr::LanguageOfThoughtExpr(x) => x.remap_refs(remap),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        language::{BinOp, Expr, ExprPool, ExprRef, LanguageExpression, MonOp},
        Entity,
    };

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
    fn complicated_lambda_language_of_thought() -> anyhow::Result<()> {
        let mut pool = LambdaPool::<Expr>(vec![
            LambdaExpr::Application {
                //John dances
                subformula: LambdaExprRef(1),
                argument: LambdaExprRef(4),
            },
            LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::et()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Property(32), ExprRef(3))),
            LambdaExpr::BoundVariable(0, LambdaType::E),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Entity(Entity::Actor(3))),
        ]);
        pool.reduce(LambdaExprRef(0))?;

        assert_eq!(
            pool.clone(),
            LambdaPool(vec![
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Property(32), ExprRef(1))),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Entity(Entity::Actor(3)))
            ]),
        );

        let mut pool = LambdaPool(vec![
            LambdaExpr::Application {
                subformula: LambdaExprRef(1),
                argument: LambdaExprRef(6),
            },
            LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::from_string("<t, <t,t>>")?),
            LambdaExpr::Lambda(LambdaExprRef(3), LambdaType::from_string("<t,t>")?),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(4), ExprRef(5))), //10
            LambdaExpr::BoundVariable(1, LambdaType::T),
            LambdaExpr::BoundVariable(0, LambdaType::T),
            LambdaExpr::Application {
                //6
                subformula: LambdaExprRef(7),
                argument: LambdaExprRef(10),
            },
            LambdaExpr::Lambda(LambdaExprRef(8), LambdaType::et()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Property(36), ExprRef(9))),
            LambdaExpr::BoundVariable(0, LambdaType::E),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Entity(Entity::Actor(2))),
        ]);
        pool.reduce(LambdaExprRef(0))?;
        assert_eq!(
            pool,
            LambdaPool(vec![
                LambdaExpr::Lambda(
                    LambdaExprRef(1),
                    LambdaType::Composition(Box::new(LambdaType::T), Box::new(LambdaType::T))
                ),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(2), ExprRef(3))),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Property(36), ExprRef(4))),
                LambdaExpr::BoundVariable(0, LambdaType::T),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Entity(Entity::Actor(2))),
            ])
        );

        // [[[Mary sings] and]  [John dances]]
        let mut pool = LambdaPool::<Expr>(vec![
            LambdaExpr::Application {
                subformula: LambdaExprRef(6),
                argument: LambdaExprRef(1),
            },
            LambdaExpr::Application {
                //John dances
                subformula: LambdaExprRef(2),
                argument: LambdaExprRef(5),
            },
            LambdaExpr::Lambda(LambdaExprRef(3), LambdaType::et()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Property(32), ExprRef(4))),
            LambdaExpr::BoundVariable(0, LambdaType::E),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Entity(Entity::Actor(3))),
            // 6
            //\lambda x. Mary sings and
            LambdaExpr::Application {
                subformula: LambdaExprRef(7),
                argument: LambdaExprRef(12),
            },
            LambdaExpr::Lambda(LambdaExprRef(8), LambdaType::from_string("<t, <t,t>>")?),
            LambdaExpr::Lambda(LambdaExprRef(9), LambdaType::from_string("<t,t>")?),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(10), ExprRef(11))), //10
            LambdaExpr::BoundVariable(1, LambdaType::T),
            LambdaExpr::BoundVariable(0, LambdaType::T),
            LambdaExpr::Application {
                //13
                subformula: LambdaExprRef(13),
                argument: LambdaExprRef(16),
            },
            LambdaExpr::Lambda(LambdaExprRef(14), LambdaType::et()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Property(36), ExprRef(15))),
            LambdaExpr::BoundVariable(0, LambdaType::E),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Entity(Entity::Actor(2))),
        ]);
        let root = pool.reduce(LambdaExprRef(0))?;
        assert_eq!(
            pool,
            LambdaPool(vec![
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(2), ExprRef(3))),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Entity(Entity::Actor(3))),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Property(36), ExprRef(4))),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Property(32), ExprRef(1))),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Entity(Entity::Actor(2)))
            ])
        );

        assert_eq!(
            pool.into_pool(root)?,
            LanguageExpression::new(
                ExprPool::from(vec![
                    Expr::Binary(BinOp::And, ExprRef(2), ExprRef(3)),
                    Expr::Entity(Entity::Actor(3)),
                    Expr::Unary(MonOp::Property(36), ExprRef(4)),
                    Expr::Unary(MonOp::Property(32), ExprRef(1)),
                    Expr::Entity(Entity::Actor(2))
                ]),
                ExprRef(root.0)
            )
        );
        Ok(())
    }
    #[test]
    fn type_check() -> anyhow::Result<()> {
        // [[[Mary sings] and]  [John dances]]
        let mut pool = LambdaPool::<()>(vec![
            LambdaExpr::Application {
                subformula: LambdaExprRef(1),
                argument: LambdaExprRef(3),
            },
            LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::et()),
            LambdaExpr::BoundVariable(0, LambdaType::T),
            LambdaExpr::FreeVariable(0, LambdaType::T),
        ]);
        assert_eq!(
            pool.reduce(LambdaExprRef(0)).unwrap_err().to_string(),
            "Type clash!"
        );

        let mut pool = LambdaPool::<()>(vec![
            LambdaExpr::Application {
                subformula: LambdaExprRef(1),
                argument: LambdaExprRef(3),
            },
            LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::et()),
            LambdaExpr::BoundVariable(0, LambdaType::T),
            LambdaExpr::FreeVariable(0, LambdaType::E),
        ]);
        assert!(pool.reduce(LambdaExprRef(0)).is_ok());
        Ok(())
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
            LambdaExpr::Application {
                subformula: LambdaExprRef(6),
                argument: LambdaExprRef(9),
            },
            LambdaExpr::Lambda(LambdaExprRef(7), LambdaType::from_string("<t, <t,t>>")?),
            LambdaExpr::Lambda(LambdaExprRef(8), LambdaType::from_string("<t,t>")?),
            LambdaExpr::BoundVariable(1, LambdaType::T),
            LambdaExpr::Application {
                //10
                subformula: LambdaExprRef(10),
                argument: LambdaExprRef(12),
            },
            LambdaExpr::Lambda(LambdaExprRef(11), LambdaType::et()),
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
