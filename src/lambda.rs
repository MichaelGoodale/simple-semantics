use anyhow::{Context, bail};
use std::collections::{HashSet, VecDeque};

pub mod types;
use types::LambdaType;

pub type Bvar = usize;
pub type Fvar = usize;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LambdaExprRef(pub u32);

pub trait LambdaLanguageOfThought {
    type Pool;
    fn get_children(&self) -> impl Iterator<Item = LambdaExprRef>;
    fn remap_refs(&mut self, remap: &[usize]);
    fn alpha_reduce(a: &mut LambdaPool<Self>, b: &mut LambdaPool<Self>)
    where
        Self: Sized;
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

    fn alpha_reduce(_a: &mut LambdaPool<Self>, _b: &mut LambdaPool<Self>) {}

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
pub struct RootedLambdaPool<T: LambdaLanguageOfThought> {
    pool: LambdaPool<T>,
    root: LambdaExprRef,
}

impl<T: LambdaLanguageOfThought + Clone + std::fmt::Debug> RootedLambdaPool<T> {
    pub(crate) fn root(&self) -> LambdaExprRef {
        self.root
    }

    pub(crate) fn get(&self, x: LambdaExprRef) -> &LambdaExpr<T> {
        self.pool.get(x)
    }

    pub fn get_type(&self) -> anyhow::Result<LambdaType> {
        self.pool.get_type(self.root)
    }

    pub fn new(pool: LambdaPool<T>, root: LambdaExprRef) -> Self {
        RootedLambdaPool { pool, root }
    }

    pub fn into(self) -> (LambdaPool<T>, LambdaExprRef) {
        (self.pool, self.root)
    }

    pub fn merge(mut self, other: Self) -> Option<Self> {
        let self_type = self.pool.get_type(self.root).expect("malformed type");
        let other_type = other.pool.get_type(other.root).expect("malformed type");

        let self_subformula = if self_type.can_apply(&other_type) {
            true
        } else if other_type.can_apply(&self_type) {
            false
        } else {
            return None;
        };

        let (mut other_pool, other_root) = other.into();

        //To make sure that the rebound fresh variables are identical.
        if self_subformula {
            T::alpha_reduce(&mut self.pool, &mut other_pool);
        } else {
            T::alpha_reduce(&mut other_pool, &mut self.pool);
        }
        let other_root = self.pool.extend_pool(other_root, other_pool);

        self.root = self.pool.add(if self_subformula {
            LambdaExpr::Application {
                subformula: self.root,
                argument: other_root,
            }
        } else {
            LambdaExpr::Application {
                subformula: other_root,
                argument: self.root,
            }
        });

        Some(self)
    }

    pub fn reduce(&mut self) -> anyhow::Result<()> {
        let root = self.pool.reduce(self.root)?;
        self.root = root;
        Ok(())
    }

    pub fn into_pool(self) -> anyhow::Result<T::Pool> {
        self.pool.into_pool(self.root)
    }

    pub fn bind_free_variable(
        &mut self,
        fvar: Fvar,
        replacement: RootedLambdaPool<T>,
    ) -> anyhow::Result<()> {
        let (other_pool, other_root) = replacement.into();
        let other_root = self.pool.extend_pool(other_root, other_pool);
        self.pool.bind_free_variable(self.root, fvar, other_root)?;
        self.root = self.pool.cleanup(self.root);
        Ok(())
    }

    pub fn lambda_abstract_free_variable(&mut self, fvar: Fvar) -> anyhow::Result<()> {
        let vars = self
            .pool
            .bfs_from(self.root)
            .filter_map(|(x, d)| match self.pool.get(x) {
                LambdaExpr::FreeVariable(var, lambda_type) if *var == fvar => {
                    Some((x, d, lambda_type.clone()))
                }
                _ => None,
            })
            .collect::<Vec<_>>();

        let mut lambda_type = None;
        for (x, lambda_depth, inner_lambda_type) in vars.into_iter() {
            if lambda_type.is_none() {
                lambda_type = Some(inner_lambda_type.clone());
            }
            *self.pool.get_mut(x) = LambdaExpr::BoundVariable(lambda_depth, inner_lambda_type);
        }
        if let Some(lambda_type) = lambda_type {
            //This way we only abstract if there is such a free
            //variable
            self.root = self.pool.add(LambdaExpr::Lambda(self.root, lambda_type));
        }
        Ok(())
    }

    pub fn apply_new_free_variable(&mut self, fvar: Fvar) -> anyhow::Result<()> {
        let pool_type = self.pool.get_type(self.root)?;
        let var_type = pool_type.lhs()?;
        let argument = self.pool.add(LambdaExpr::FreeVariable(fvar, var_type));
        self.root = self.pool.add(LambdaExpr::Application {
            subformula: self.root,
            argument,
        });
        self.reduce()?;
        Ok(())
    }
}

#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub struct LambdaPool<T: LambdaLanguageOfThought>(Vec<LambdaExpr<T>>);

impl<T: LambdaLanguageOfThought + Sized> LambdaPool<T> {
    fn extend_pool(
        &mut self,
        mut other_root: LambdaExprRef,
        mut other_pool: LambdaPool<T>,
    ) -> LambdaExprRef {
        let shift_n = self.0.len();
        let remap: Vec<_> = (0..other_pool.0.len()).map(|x| x + shift_n).collect();
        other_pool.0.iter_mut().for_each(|x| x.remap_refs(&remap));
        other_root.0 += shift_n as u32;
        self.0.append(&mut other_pool.0);
        other_root
    }

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

    pub fn from(x: Vec<LambdaExpr<T>>) -> Self {
        LambdaPool(x)
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

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut LambdaExpr<T>> {
        self.0.iter_mut()
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
    fn check_type_clash(&self, x: LambdaExprRef) -> anyhow::Result<LambdaType> {
        if let LambdaExpr::Application {
            subformula,
            argument,
        } = self.get(x)
        {
            let argument_type = self.get_type(*argument)?;
            let subformula_type = self.get_type(*subformula)?;
            subformula_type.apply(&argument_type)
        } else {
            bail!("Can't apply when its not an application!")
        }
    }

    pub fn get_type(&self, x: LambdaExprRef) -> anyhow::Result<LambdaType> {
        match self.get(x) {
            LambdaExpr::BoundVariable(_, x) | LambdaExpr::FreeVariable(_, x) => Ok(x.clone()),
            LambdaExpr::Lambda(s, x) => {
                let result = self.get_type(*s);
                Ok(LambdaType::Composition(
                    Box::new(x.clone()),
                    Box::new(result?),
                ))
            }
            LambdaExpr::Application { subformula, .. } => {
                let subformula_type = self.get_type(*subformula)?;
                subformula_type.rhs()
            }
            LambdaExpr::LanguageOfThoughtExpr(x) => Ok(x.get_type()),
        }
    }

    fn bind_free_variable(
        &mut self,
        root: LambdaExprRef,
        fvar: Fvar,
        replacement_root: LambdaExprRef,
    ) -> anyhow::Result<()> {
        //TODO: Add type checking here maybe.
        let to_change = self
            .bfs_from(root)
            .filter_map(|(x, _)| match self.get(x) {
                LambdaExpr::FreeVariable(var, _t) if *var == fvar => Some(x),
                _ => None,
            })
            .collect::<Vec<_>>();
        let new_argument = self.get(replacement_root).clone();
        for x in to_change {
            self.0[x.0 as usize] = new_argument.clone();
        }
        Ok(())
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
                LambdaExpr::Lambda(x, ..) => {
                    self.check_type_clash(app)?;

                    *x
                }
                _ => bail!(
                    "You can only beta reduce if the left hand side of the application is a lambda!"
                ),
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
        Entity, LabelledScenarios,
        language::{BinOp, Expr, ExprPool, ExprRef, LanguageExpression, MonOp},
    };

    fn k<T: Default>(pos: u32) -> anyhow::Result<[LambdaExpr<T>; 3]> {
        Ok([
            LambdaExpr::Lambda(LambdaExprRef(pos + 1), LambdaType::E),
            LambdaExpr::Lambda(LambdaExprRef(pos + 2), LambdaType::E),
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
            LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::E),
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
                argument: LambdaExprRef(5),
            },
            LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::from_string("<e, t>")?),
            LambdaExpr::Application {
                subformula: LambdaExprRef(3),
                argument: LambdaExprRef(4),
            },
            LambdaExpr::BoundVariable(0, LambdaType::et()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Entity(Entity::Actor(2))),
            LambdaExpr::Lambda(LambdaExprRef(6), LambdaType::E),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Property(36), ExprRef(7))),
            LambdaExpr::BoundVariable(0, LambdaType::E),
        ]);
        pool.reduce(LambdaExprRef(0))?;
        assert_eq!(
            pool,
            LambdaPool(vec![
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Property(36), ExprRef(1))),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Entity(Entity::Actor(2))),
            ])
        );

        let mut pool = LambdaPool(vec![
            LambdaExpr::Application {
                subformula: LambdaExprRef(1),
                argument: LambdaExprRef(6),
            },
            LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::T),
            LambdaExpr::Lambda(LambdaExprRef(3), LambdaType::T),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(4), ExprRef(5))), //10
            LambdaExpr::BoundVariable(1, LambdaType::T),
            LambdaExpr::BoundVariable(0, LambdaType::T),
            LambdaExpr::Application {
                //6
                subformula: LambdaExprRef(7),
                argument: LambdaExprRef(10),
            },
            LambdaExpr::Lambda(LambdaExprRef(8), LambdaType::E),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Property(36), ExprRef(9))),
            LambdaExpr::BoundVariable(0, LambdaType::E),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Entity(Entity::Actor(2))),
        ]);
        pool.reduce(LambdaExprRef(0))?;

        assert_eq!(
            pool,
            LambdaPool(vec![
                LambdaExpr::Lambda(LambdaExprRef(1), LambdaType::T),
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
            LambdaExpr::Lambda(LambdaExprRef(3), LambdaType::E),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Property(32), ExprRef(4))),
            LambdaExpr::BoundVariable(0, LambdaType::E),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Entity(Entity::Actor(3))),
            // 6
            //\lambda x. Mary sings and
            LambdaExpr::Application {
                subformula: LambdaExprRef(7),
                argument: LambdaExprRef(12),
            },
            LambdaExpr::Lambda(LambdaExprRef(8), LambdaType::T),
            LambdaExpr::Lambda(LambdaExprRef(9), LambdaType::T),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(10), ExprRef(11))), //10
            LambdaExpr::BoundVariable(1, LambdaType::T),
            LambdaExpr::BoundVariable(0, LambdaType::T),
            LambdaExpr::Application {
                //13
                subformula: LambdaExprRef(13),
                argument: LambdaExprRef(16),
            },
            LambdaExpr::Lambda(LambdaExprRef(14), LambdaType::E),
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
            LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::E),
            LambdaExpr::BoundVariable(0, LambdaType::T),
            LambdaExpr::FreeVariable(0, LambdaType::T),
        ]);
        assert_eq!(
            pool.reduce(LambdaExprRef(0)).unwrap_err().to_string(),
            "Cannot apply t to <e,t>!"
        );

        let mut pool = LambdaPool::<()>(vec![
            LambdaExpr::Application {
                subformula: LambdaExprRef(1),
                argument: LambdaExprRef(3),
            },
            LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::E),
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
            LambdaExpr::Lambda(LambdaExprRef(3), LambdaType::E),
            LambdaExpr::FreeVariable(0, LambdaType::T),
            LambdaExpr::FreeVariable(2, LambdaType::E),
            // 5
            //\lambda x. Mary sings and
            LambdaExpr::Application {
                subformula: LambdaExprRef(6),
                argument: LambdaExprRef(9),
            },
            LambdaExpr::Lambda(LambdaExprRef(7), LambdaType::T),
            LambdaExpr::Lambda(LambdaExprRef(8), LambdaType::T),
            LambdaExpr::BoundVariable(1, LambdaType::T),
            LambdaExpr::Application {
                //10
                subformula: LambdaExprRef(10),
                argument: LambdaExprRef(12),
            },
            LambdaExpr::Lambda(LambdaExprRef(11), LambdaType::E),
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
        pool.cleanup(root);

        assert_eq!(
            pool,
            LambdaPool(vec![
                LambdaExpr::FreeVariable(32, LambdaType::E),
                LambdaExpr::Lambda(LambdaExprRef(0), LambdaType::E)
            ])
        );
        Ok(())
    }

    use crate::language::lot_parser;
    use chumsky::prelude::*;

    #[test]
    fn test_root_and_merger() -> anyhow::Result<()> {
        let labels = LabelledScenarios::default();
        let mut label_state = extra::SimpleState(labels.clone());
        let parser = lot_parser().then_ignore(end());
        let man = parser
            .parse_with_state("lambda e x (p_man(x))", &mut label_state)
            .unwrap();
        let sleeps = parser
            .parse_with_state(
                "lambda e x (some(y, all_e, AgentOf(x, y) & p_sleep(y)))",
                &mut label_state,
            )
            .unwrap();
        let every = parser
            .parse_with_state(
                "lambda <e,t> p(lambda <e,t> q(every(x, p(x), q(x))))",
                &mut label_state,
            )
            .unwrap();

        let phi = every.clone().merge(man.clone()).unwrap();
        let mut phi = phi.merge(sleeps.clone()).unwrap();
        phi.reduce()?;
        let pool = phi.into_pool()?;
        assert_eq!(
            "every(x,p0(x),some(y,all_e,(AgentOf(x,y) & p1(y))))",
            pool.to_string()
        );
        let phi = man.merge(every).unwrap();
        let mut phi = sleeps.merge(phi).unwrap();
        phi.reduce()?;
        let pool = phi.into_pool()?;
        assert_eq!(
            "every(x,p0(x),some(y,all_e,(AgentOf(x,y) & p1(y))))",
            pool.to_string()
        );
        Ok(())
    }

    #[test]
    fn bind_free_variable() -> anyhow::Result<()> {
        let labels = LabelledScenarios::default();
        let mut label_state = extra::SimpleState(labels.clone());
        let parser = lot_parser().then_ignore(end());
        let mut pool = parser
            .parse_with_state("phi_t & True", &mut label_state)
            .unwrap();

        pool.bind_free_variable(
            0,
            parser.parse_with_state("False", &mut label_state).unwrap(),
        )?;
        dbg!(&pool);
        assert_eq!("(False & True)", pool.into_pool()?.to_string());
        Ok(())
    }

    #[test]
    fn apply_new_free_variable() -> anyhow::Result<()> {
        let labels = LabelledScenarios::default();
        let mut label_state = extra::SimpleState(labels.clone());
        let parser = lot_parser().then_ignore(end());
        let mut pool = parser
            .parse_with_state(
                "lambda <e,t> P (lambda <e,t> Q (lambda e x (P(x) & Q(x))))",
                &mut label_state,
            )
            .unwrap();

        pool.apply_new_free_variable(0)?;

        let gold_pool = RootedLambdaPool {
            pool: LambdaPool(vec![
                LambdaExpr::FreeVariable(0, LambdaType::et()),
                LambdaExpr::BoundVariable(0, LambdaType::E),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(0),
                    argument: LambdaExprRef(1),
                },
                LambdaExpr::BoundVariable(1, LambdaType::et()),
                LambdaExpr::BoundVariable(0, LambdaType::E),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(3),
                    argument: LambdaExprRef(4),
                },
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(2), ExprRef(5))),
                LambdaExpr::Lambda(LambdaExprRef(6), LambdaType::E),
                LambdaExpr::Lambda(LambdaExprRef(7), LambdaType::et()),
            ]),
            root: LambdaExprRef(8),
        };
        assert_eq!(pool, gold_pool);
        Ok(())
    }

    #[test]
    fn lambda_abstraction() -> anyhow::Result<()> {
        let labels = LabelledScenarios::default();
        let mut label_state = extra::SimpleState(labels.clone());
        let parser = lot_parser().then_ignore(end());
        let mut pool = parser
            .parse_with_state(
                "lambda <e,t> P (lambda <e,t> Q (lambda e x (Z(x) & P(x) & Q(x))))",
                &mut label_state,
            )
            .unwrap();

        pool.lambda_abstract_free_variable(0)?;

        let gold_pool = RootedLambdaPool {
            pool: LambdaPool(vec![
                LambdaExpr::BoundVariable(3, LambdaType::et()),
                LambdaExpr::BoundVariable(0, LambdaType::E),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(0),
                    argument: LambdaExprRef(1),
                },
                LambdaExpr::BoundVariable(2, LambdaType::et()),
                LambdaExpr::BoundVariable(0, LambdaType::E),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(3),
                    argument: LambdaExprRef(4),
                },
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(2), ExprRef(5))),
                LambdaExpr::BoundVariable(1, LambdaType::et()),
                LambdaExpr::BoundVariable(0, LambdaType::E),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(7),
                    argument: LambdaExprRef(8),
                },
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(6), ExprRef(9))),
                LambdaExpr::Lambda(LambdaExprRef(10), LambdaType::E),
                LambdaExpr::Lambda(LambdaExprRef(11), LambdaType::et()),
                LambdaExpr::Lambda(LambdaExprRef(12), LambdaType::et()),
                LambdaExpr::Lambda(LambdaExprRef(13), LambdaType::et()),
            ]),
            root: LambdaExprRef(14),
        };

        assert_eq!(pool, gold_pool);
        Ok(())
    }
}
