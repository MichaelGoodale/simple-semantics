use std::{
    collections::{HashSet, VecDeque},
    fmt::Debug,
    iter::empty,
};
use thiserror::Error;

pub mod types;
use types::{LambdaType, TypeError};

pub type Bvar = usize;
pub type Fvar = usize;

#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum LambdaError {
    #[error("The free variable has type {free_var} while the argument is {arg}")]
    BadFreeVariableApp {
        free_var: LambdaType,
        arg: LambdaType,
    },
    #[error("The free variable has type {free_var} while its lambda takes {lambda}")]
    BadFreeVariable {
        free_var: LambdaType,
        lambda: LambdaType,
    },
    #[error(
        "A bound variable {var:?} cannot have a DeBruijn index higher than its lambda depth ({depth})"
    )]
    BadBoundVariable { var: LambdaExprRef, depth: usize },

    #[error("Expression has type error ({0})")]
    TypeError(#[from] TypeError),

    #[error("Failed reduction: {0}")]
    ReductionError(#[from] ReductionError),
}

#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum LambdaTryFromError {
    #[error("The vec contains None")]
    HasNone,
}

#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum ReductionError {
    #[error("{0:?} is not a valid ref!")]
    NotValidRef(LambdaExprRef),
    #[error("{0:?} is not an application!")]
    NotApplication(LambdaExprRef),
    #[error("The left hand side of the application ({app:?}), {lhs:?} is not a lambda expression!")]
    NotLambdaInApplication {
        app: LambdaExprRef,
        lhs: LambdaExprRef,
    },

    #[error("Incorrect types: {0}")]
    TypeError(#[from] TypeError),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LambdaExprRef(pub u32);

pub trait LambdaLanguageOfThought {
    type Pool;
    type ConversionError;

    fn get_children(&self) -> impl Iterator<Item = LambdaExprRef>;
    fn remap_refs(&mut self, remap: &[usize]);
    fn alpha_reduce(a: &mut LambdaPool<Self>, b: &mut LambdaPool<Self>)
    where
        Self: Sized;
    fn change_children(&mut self, new_children: &[LambdaExprRef]);
    fn get_type(&self) -> &LambdaType;
    fn get_arguments<'a>(&'a self) -> Box<dyn Iterator<Item = LambdaType> + 'a>;
    fn to_pool(
        pool: LambdaPool<Self>,
        root: LambdaExprRef,
    ) -> Result<Self::Pool, Self::ConversionError>
    where
        Self: Sized;
}

impl LambdaLanguageOfThought for () {
    type Pool = ();
    type ConversionError = ();
    fn get_children(&self) -> impl Iterator<Item = LambdaExprRef> {
        std::iter::empty()
    }
    fn remap_refs(&mut self, _: &[usize]) {}

    fn change_children(&mut self, _: &[LambdaExprRef]) {}

    fn get_type(&self) -> &LambdaType {
        unimplemented!()
    }

    fn get_arguments<'a>(&'a self) -> Box<dyn Iterator<Item = LambdaType> + 'a> {
        Box::new(empty())
    }

    fn alpha_reduce(_a: &mut LambdaPool<Self>, _b: &mut LambdaPool<Self>) {}

    fn to_pool(_: LambdaPool<Self>, _: LambdaExprRef) -> Result<Self::Pool, ()> {
        Ok(())
    }
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
    pub(crate) pool: LambdaPool<T>,
    pub(crate) root: LambdaExprRef,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct ExpressionType {
    pub output: LambdaType,
    pub arguments: Vec<LambdaType>,
}
impl ExpressionType {
    pub fn new_no_args(lambda_type: LambdaType) -> Self {
        ExpressionType {
            output: lambda_type,
            arguments: vec![],
        }
    }
}

impl<T: LambdaLanguageOfThought + Clone + std::fmt::Debug> RootedLambdaPool<T> {
    pub(crate) fn get_expression_type(
        &self,
        i: LambdaExprRef,
    ) -> Result<ExpressionType, TypeError> {
        match self.get(i) {
            LambdaExpr::Lambda(lambda_expr_ref, lambda_type) => {
                let arguments = vec![self.pool.get_type(*lambda_expr_ref)?];
                Ok(ExpressionType {
                    output: LambdaType::compose(
                        lambda_type.clone(),
                        arguments.first().unwrap().clone(),
                    ),
                    arguments,
                })
            }
            LambdaExpr::BoundVariable(_, lambda_type)
            | LambdaExpr::FreeVariable(_, lambda_type) => Ok(ExpressionType {
                output: lambda_type.clone(),
                arguments: vec![],
            }),
            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                let subformula_type = self.pool.get_type(*subformula)?;
                Ok(ExpressionType {
                    output: subformula_type.rhs()?.clone(),
                    arguments: vec![subformula_type, self.pool.get_type(*argument)?],
                })
            }
            LambdaExpr::LanguageOfThoughtExpr(x) => Ok(ExpressionType {
                output: x.get_type().clone(),
                arguments: x.get_arguments().collect(),
            }),
        }
    }

    pub(crate) fn root(&self) -> LambdaExprRef {
        self.root
    }

    pub fn get(&self, x: LambdaExprRef) -> &LambdaExpr<T> {
        self.pool.get(x)
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.pool.0.len()
    }

    pub fn get_mut(&mut self, x: LambdaExprRef) -> &mut LambdaExpr<T> {
        self.pool.get_mut(x)
    }

    pub fn get_type(&self) -> Result<LambdaType, TypeError> {
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

    pub fn reduce(&mut self) -> Result<(), ReductionError> {
        let root = self.pool.reduce(self.root)?;
        self.root = root;
        Ok(())
    }

    pub fn into_pool(self) -> Result<T::Pool, T::ConversionError> {
        self.pool.into_pool(self.root)
    }

    pub fn bind_free_variable(
        &mut self,
        fvar: Fvar,
        replacement: RootedLambdaPool<T>,
    ) -> Result<(), LambdaError> {
        let (other_pool, other_root) = replacement.into();
        let other_root = self.pool.extend_pool(other_root, other_pool);
        self.pool.bind_free_variable(self.root, fvar, other_root)?;
        self.root = self.pool.cleanup(self.root);
        Ok(())
    }

    pub fn lambda_abstract_free_variable(
        &mut self,
        fvar: Fvar,
        lambda_type: LambdaType,
        always_abstract: bool,
    ) -> Result<(), LambdaError> {
        self.reduce()?;
        let vars = self
            .pool
            .bfs_from(self.root)
            .filter_map(|(x, d)| match self.pool.get(x) {
                LambdaExpr::FreeVariable(var, var_type) if *var == fvar => {
                    if &lambda_type != var_type {
                        Some(Err(LambdaError::BadFreeVariable {
                            free_var: var_type.clone(),
                            lambda: lambda_type.clone(),
                        }))
                    } else {
                        Some(Ok((x, d)))
                    }
                }
                _ => None,
            })
            .collect::<Result<Vec<_>, LambdaError>>()?;

        if !vars.is_empty() || always_abstract {
            for (x, lambda_depth) in vars.into_iter() {
                *self.pool.get_mut(x) =
                    LambdaExpr::BoundVariable(lambda_depth, lambda_type.clone());
            }
            self.root = self.pool.add(LambdaExpr::Lambda(self.root, lambda_type));
        }
        Ok(())
    }

    pub fn apply_new_free_variable(&mut self, fvar: Fvar) -> Result<LambdaType, LambdaError> {
        let pool_type = self.pool.get_type(self.root)?;
        let var_type = pool_type.lhs()?;
        let argument = self
            .pool
            .add(LambdaExpr::FreeVariable(fvar, var_type.clone()));
        self.root = self.pool.add(LambdaExpr::Application {
            subformula: self.root,
            argument,
        });
        self.reduce()?;
        Ok(var_type.clone())
    }
}

#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub struct LambdaPool<T: LambdaLanguageOfThought>(pub(crate) Vec<LambdaExpr<T>>);

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

    pub fn into_pool(self, root: LambdaExprRef) -> Result<T::Pool, T::ConversionError> {
        return T::to_pool(self, root);
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

    pub(crate) fn get(&self, expr: LambdaExprRef) -> &LambdaExpr<T> {
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

pub struct LambdaPoolBFSIterator<'a, T: LambdaLanguageOfThought> {
    pool: &'a LambdaPool<T>,
    queue: VecDeque<(LambdaExprRef, Bvar)>,
}

impl<T: LambdaLanguageOfThought> LambdaExpr<T> {
    pub(crate) fn get_children<'a>(&'a self) -> Box<dyn Iterator<Item = LambdaExprRef> + 'a> {
        match self {
            LambdaExpr::Lambda(x, _) => Box::new([x].into_iter().copied()),
            LambdaExpr::Application {
                subformula,
                argument,
            } => Box::new([subformula, argument].into_iter().copied()),
            LambdaExpr::BoundVariable(..) | LambdaExpr::FreeVariable(..) => {
                Box::new(std::iter::empty())
            }
            LambdaExpr::LanguageOfThoughtExpr(x) => Box::new(x.get_children()),
        }
    }
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
    pub(crate) fn bfs_from(&self, x: LambdaExprRef) -> LambdaPoolBFSIterator<T> {
        LambdaPoolBFSIterator {
            pool: self,
            queue: VecDeque::from([(x, 0)]),
        }
    }

    fn check_type_clash(&self, x: LambdaExprRef) -> Result<LambdaType, ReductionError> {
        if let LambdaExpr::Application {
            subformula,
            argument,
        } = self.get(x)
        {
            let argument_type = self.get_type(*argument)?;
            let subformula_type = self.get_type(*subformula)?;
            Ok(subformula_type.apply(&argument_type)?.clone())
        } else {
            Err(ReductionError::NotApplication(x))
        }
    }

    pub fn get_type(&self, x: LambdaExprRef) -> Result<LambdaType, TypeError> {
        match self.get(x) {
            LambdaExpr::BoundVariable(_, x) | LambdaExpr::FreeVariable(_, x) => Ok(x.clone()),
            LambdaExpr::Lambda(s, x) => {
                let result = self.get_type(*s);
                Ok(LambdaType::compose(x.clone(), result?))
            }
            LambdaExpr::Application { subformula, .. } => {
                let subformula_type = self.get_type(*subformula)?;
                Ok(subformula_type.rhs()?.clone())
            }
            LambdaExpr::LanguageOfThoughtExpr(x) => Ok(x.get_type().clone()),
        }
    }

    fn bind_free_variable(
        &mut self,
        root: LambdaExprRef,
        fvar: Fvar,
        replacement_root: LambdaExprRef,
    ) -> Result<(), LambdaError> {
        let arg_t = self.get_type(replacement_root)?;

        let to_replace = self
            .bfs_from(root)
            .filter_map(|(x, _)| match self.get(x) {
                LambdaExpr::FreeVariable(var, t) if *var == fvar => {
                    if t == &arg_t {
                        Some(Ok(x))
                    } else {
                        Some(Err(LambdaError::BadFreeVariableApp {
                            free_var: t.clone(),
                            arg: arg_t.clone(),
                        }))
                    }
                }
                _ => None,
            })
            .collect::<Result<Vec<_>, LambdaError>>()?;

        self.replace_section(&to_replace, replacement_root);
        Ok(())
    }

    fn clone_section_return_expr(&mut self, source: LambdaExprRef) -> LambdaExpr<T> {
        let mut expr = self.get(source).clone();
        let new_children: Vec<_> = expr
            .get_children()
            .map(|child| self.clone_section(child))
            .collect();
        expr.change_children(&new_children);
        expr
    }

    fn clone_section(&mut self, source: LambdaExprRef) -> LambdaExprRef {
        let mut expr = self.get(source).clone();
        let new_children: Vec<_> = expr
            .get_children()
            .map(|child| self.clone_section(child))
            .collect();
        expr.change_children(&new_children);
        self.0.push(expr);
        LambdaExprRef(self.0.len() as u32 - 1)
    }

    fn replace_section(&mut self, to_replace: &[LambdaExprRef], to_copy: LambdaExprRef) {
        let n = to_replace.len();
        for (i, x) in to_replace.iter().enumerate() {
            if i != n - 1 {
                //We have more to add so we need to copy.
                let expr = self.clone_section_return_expr(to_copy);
                *self.get_mut(*x) = expr;
            } else {
                //Last iteration so we don't need to copy anymore.
                *self.get_mut(*x) = self.get(to_copy).clone();
            }
        }
    }

    fn beta_reduce(&mut self, app: LambdaExprRef) -> Result<(), ReductionError> {
        //BFS over all children and then replace debruijn k w/ argument ref where k is the number
        //of lambda abstractions we've gone under, e.g. (lambda 0 lambda 0 1)(u) -> lambda u lambda
        //1
        //
        //swap position of lambda ref and subformula ref so the lambda now leads to this.
        //
        let Some(expr) = self.checked_get(app) else {
            return Err(ReductionError::NotValidRef(app));
        };

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
                _ => {
                    return Err(ReductionError::NotLambdaInApplication {
                        app,
                        lhs: *subformula,
                    });
                }
            };

            (
                inner_term,
                *argument,
                self.bfs_from(inner_term)
                    .filter_map(|(x, n)| {
                        if let LambdaExpr::BoundVariable(i, _) = self.get(x) {
                            if *i == n { Some(x) } else { None }
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>(),
            )
        } else {
            return Err(ReductionError::NotApplication(app));
        };

        self.replace_section(&subformula_vars, argument);

        //We used to swap this, but that will cause an insanely arcane bug.
        //This is because the same term may be referred to by multiple instructions so if you swap
        //them, it gets invalidated.
        self.0[app.0 as usize] = self.0[inner_term.0 as usize].clone();
        //self.0.swap(inner_term.0 as usize, app.0 as usize); <- BAD

        Ok(())
    }

    ///Iterates through a pool and de-allocates dangling refs and updates ExprRefs to new
    ///addresses. Basically garbage collection.
    pub(crate) fn cleanup(&mut self, root: LambdaExprRef) -> LambdaExprRef {
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

    pub fn reduce(&mut self, root: LambdaExprRef) -> Result<LambdaExprRef, ReductionError> {
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
    fn change_children(&mut self, children: &[LambdaExprRef]) {
        match self {
            LambdaExpr::Lambda(lambda_expr_ref, _) => *lambda_expr_ref = children[0],
            LambdaExpr::BoundVariable(..) | LambdaExpr::FreeVariable(..) => (),
            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                *subformula = children[0];
                *argument = children[1];
            }
            LambdaExpr::LanguageOfThoughtExpr(x) => x.change_children(children),
        }
    }

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LambdaSummaryStats {
    WellFormed {
        lambda_type: LambdaType,
        constant_function: bool,
        n_nodes: usize,
    },
    Malformed,
}

impl<T: LambdaLanguageOfThought + Clone + std::fmt::Debug> RootedLambdaPool<T> {
    pub fn stats(&self) -> LambdaSummaryStats {
        let lambda_type = self.get_type();
        if lambda_type.is_err() {
            return LambdaSummaryStats::Malformed;
        }
        let lambda_type = lambda_type.unwrap();
        let n_nodes = self.pool.0.len();

        match self.lambda_has_variable(self.root, vec![]) {
            Ok((has_variable, _)) => LambdaSummaryStats::WellFormed {
                lambda_type,
                constant_function: !has_variable,
                n_nodes,
            },

            Err(_) => LambdaSummaryStats::Malformed,
        }
    }

    fn lambda_has_variable(
        &self,
        i: LambdaExprRef,
        mut previous_lambdas: Vec<bool>,
    ) -> Result<(bool, Vec<bool>), LambdaError> {
        let expr = self.get(i);

        match expr {
            LambdaExpr::Lambda(..) => {
                previous_lambdas.push(false);
            }
            LambdaExpr::BoundVariable(lambda, _) => {
                let n_lambdas = previous_lambdas.len();
                if *lambda >= previous_lambdas.len() {
                    return Err(LambdaError::BadBoundVariable {
                        var: i,
                        depth: previous_lambdas.len(),
                    });
                }
                *previous_lambdas.get_mut(n_lambdas - 1 - lambda).unwrap() = true;
            }
            _ => (),
        }

        let n_lambdas = previous_lambdas.len();

        // Use to check if any child has a constant lambda
        let mut has_variable = true;
        for child in expr.get_children() {
            let (is_lambda, v) = self.lambda_has_variable(child, previous_lambdas.clone())?;
            has_variable &= is_lambda;

            previous_lambdas
                .iter_mut()
                .zip(v[0..n_lambdas].iter())
                .for_each(|(a, b)| *a |= b);
        }

        if let LambdaExpr::Lambda(..) = expr {
            Ok((
                has_variable && previous_lambdas.pop().unwrap(),
                previous_lambdas,
            ))
        } else {
            Ok((has_variable, previous_lambdas))
        }
    }

    fn has_variable(&self, i: LambdaExprRef) -> bool {
        self.pool.bfs_from(i).any(|(x, lambda_depth)| matches!(*self.pool.get(x), LambdaExpr::BoundVariable(z,_) if z == lambda_depth-1))
    }
}

impl<T: LambdaLanguageOfThought> From<LambdaPool<T>> for Vec<Option<LambdaExpr<T>>> {
    fn from(value: LambdaPool<T>) -> Self {
        value.0.into_iter().map(Some).collect()
    }
}

impl<T: LambdaLanguageOfThought> TryFrom<Vec<Option<LambdaExpr<T>>>> for LambdaPool<T> {
    type Error = LambdaTryFromError;

    fn try_from(value: Vec<Option<LambdaExpr<T>>>) -> Result<Self, Self::Error> {
        match value.into_iter().collect::<Option<Vec<_>>>() {
            Some(x) => Ok(LambdaPool(x)),
            None => Err(LambdaTryFromError::HasNone),
        }
    }
}

#[cfg(test)]
mod test {

    use super::*;
    use crate::{
        LabelledScenarios,
        language::{ActorOrEvent, BinOp, Expr, ExprPool, ExprRef, LanguageExpression, MonOp},
    };

    #[test]
    fn stats() -> anyhow::Result<()> {
        let p = lot_parser::<extra::Err<Rich<_>>>();
        let mut labels = LabelledScenarios::default();
        for (expr, constant_lambda) in [
            ("a0", false),
            ("lambda a x (pa_man(x))", false),
            ("lambda a x (pa_man(a_m))", true),
            (
                "lambda a x (((lambda a y (pa_woman(y)))(a_m)) & pa_man(x))",
                false,
            ),
            (
                "lambda a x (((lambda a y (pa_woman(a_m)))(a_m)) & pa_man(x))",
                true,
            ),
            ("lambda a y (pa_woman(a_m))", true),
            ("lambda a y (lambda a x (y))", true),
        ] {
            let expr = p.parse(expr).unwrap().to_pool(&mut labels)?;
            match expr.stats() {
                LambdaSummaryStats::WellFormed {
                    constant_function, ..
                } => assert_eq!(constant_function, constant_lambda),
                LambdaSummaryStats::Malformed => panic!("{expr} should be well-formed!"),
            }
        }
        Ok(())
    }

    fn k<T: Default>(pos: u32) -> anyhow::Result<[LambdaExpr<T>; 3]> {
        Ok([
            LambdaExpr::Lambda(LambdaExprRef(pos + 1), LambdaType::e().clone()),
            LambdaExpr::Lambda(LambdaExprRef(pos + 2), LambdaType::e().clone()),
            LambdaExpr::BoundVariable(1, LambdaType::e().clone()),
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
            LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::a().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                MonOp::Property(32, ActorOrEvent::Actor),
                ExprRef(3),
            )),
            LambdaExpr::BoundVariable(0, LambdaType::a().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Actor(3)),
        ]);
        pool.reduce(LambdaExprRef(0))?;

        assert_eq!(
            pool.clone(),
            LambdaPool(vec![
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                    MonOp::Property(32, ActorOrEvent::Actor),
                    ExprRef(1)
                )),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Actor(3))
            ]),
        );

        let mut pool = LambdaPool(vec![
            LambdaExpr::Application {
                subformula: LambdaExprRef(1),
                argument: LambdaExprRef(5),
            },
            LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::from_string("<a, t>")?),
            LambdaExpr::Application {
                subformula: LambdaExprRef(3),
                argument: LambdaExprRef(4),
            },
            LambdaExpr::BoundVariable(0, LambdaType::et().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Actor(2)),
            LambdaExpr::Lambda(LambdaExprRef(6), LambdaType::a().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                MonOp::Property(36, ActorOrEvent::Actor),
                ExprRef(7),
            )),
            LambdaExpr::BoundVariable(0, LambdaType::a().clone()),
        ]);
        pool.reduce(LambdaExprRef(0))?;
        assert_eq!(
            pool,
            LambdaPool(vec![
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                    MonOp::Property(36, ActorOrEvent::Actor),
                    ExprRef(1)
                )),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Actor(2)),
            ])
        );

        let mut pool = LambdaPool(vec![
            LambdaExpr::Application {
                subformula: LambdaExprRef(1),
                argument: LambdaExprRef(6),
            },
            LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::t().clone()),
            LambdaExpr::Lambda(LambdaExprRef(3), LambdaType::t().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(4), ExprRef(5))), //10
            LambdaExpr::BoundVariable(1, LambdaType::t().clone()),
            LambdaExpr::BoundVariable(0, LambdaType::t().clone()),
            LambdaExpr::Application {
                //6
                subformula: LambdaExprRef(7),
                argument: LambdaExprRef(10),
            },
            LambdaExpr::Lambda(LambdaExprRef(8), LambdaType::a().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                MonOp::Property(36, ActorOrEvent::Actor),
                ExprRef(9),
            )),
            LambdaExpr::BoundVariable(0, LambdaType::a().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Actor(2)),
        ]);
        pool.reduce(LambdaExprRef(0))?;

        assert_eq!(
            pool,
            LambdaPool(vec![
                LambdaExpr::Lambda(LambdaExprRef(1), LambdaType::t().clone()),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(2), ExprRef(3))),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                    MonOp::Property(36, ActorOrEvent::Actor),
                    ExprRef(4)
                )),
                LambdaExpr::BoundVariable(0, LambdaType::t().clone()),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Actor(2)),
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
            LambdaExpr::Lambda(LambdaExprRef(3), LambdaType::a().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                MonOp::Property(32, ActorOrEvent::Actor),
                ExprRef(4),
            )),
            LambdaExpr::BoundVariable(0, LambdaType::a().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Actor(3)),
            // 6
            //\lambda x. Mary sings and
            LambdaExpr::Application {
                subformula: LambdaExprRef(7),
                argument: LambdaExprRef(12),
            },
            LambdaExpr::Lambda(LambdaExprRef(8), LambdaType::t().clone()),
            LambdaExpr::Lambda(LambdaExprRef(9), LambdaType::t().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(10), ExprRef(11))), //10
            LambdaExpr::BoundVariable(1, LambdaType::t().clone()),
            LambdaExpr::BoundVariable(0, LambdaType::t().clone()),
            LambdaExpr::Application {
                //13
                subformula: LambdaExprRef(13),
                argument: LambdaExprRef(16),
            },
            LambdaExpr::Lambda(LambdaExprRef(14), LambdaType::a().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                MonOp::Property(36, ActorOrEvent::Actor),
                ExprRef(15),
            )),
            LambdaExpr::BoundVariable(0, LambdaType::a().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Actor(2)),
        ]);
        let root = pool.reduce(LambdaExprRef(0))?;
        assert_eq!(
            pool,
            LambdaPool(vec![
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(2), ExprRef(3))),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Actor(3)),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                    MonOp::Property(36, ActorOrEvent::Actor),
                    ExprRef(4)
                )),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                    MonOp::Property(32, ActorOrEvent::Actor),
                    ExprRef(1)
                )),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Actor(2))
            ])
        );

        assert_eq!(
            pool.into_pool(root)?,
            LanguageExpression::new(
                ExprPool::from(vec![
                    Expr::Binary(BinOp::And, ExprRef(2), ExprRef(3)),
                    Expr::Actor(3),
                    Expr::Unary(MonOp::Property(36, ActorOrEvent::Actor), ExprRef(4)),
                    Expr::Unary(MonOp::Property(32, ActorOrEvent::Actor), ExprRef(1)),
                    Expr::Actor(2)
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
            LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::a().clone()),
            LambdaExpr::BoundVariable(0, LambdaType::t().clone()),
            LambdaExpr::FreeVariable(0, LambdaType::t().clone()),
        ]);
        assert_eq!(
            pool.reduce(LambdaExprRef(0)).unwrap_err(),
            ReductionError::TypeError(TypeError::CantApply(
                LambdaType::t().clone(),
                LambdaType::at().clone()
            ))
        );

        let mut pool = LambdaPool::<()>(vec![
            LambdaExpr::Application {
                subformula: LambdaExprRef(1),
                argument: LambdaExprRef(3),
            },
            LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::a().clone()),
            LambdaExpr::BoundVariable(0, LambdaType::t().clone()),
            LambdaExpr::FreeVariable(0, LambdaType::a().clone()),
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
            LambdaExpr::Lambda(LambdaExprRef(3), LambdaType::e().clone()),
            LambdaExpr::FreeVariable(0, LambdaType::t().clone()),
            LambdaExpr::FreeVariable(2, LambdaType::t().clone()),
            // 5
            //\lambda x. Mary sings and
            LambdaExpr::Application {
                subformula: LambdaExprRef(6),
                argument: LambdaExprRef(9),
            },
            LambdaExpr::Lambda(LambdaExprRef(7), LambdaType::t().clone()),
            LambdaExpr::Lambda(LambdaExprRef(8), LambdaType::t().clone()),
            LambdaExpr::BoundVariable(1, LambdaType::t().clone()),
            LambdaExpr::Application {
                //10
                subformula: LambdaExprRef(10),
                argument: LambdaExprRef(12),
            },
            LambdaExpr::Lambda(LambdaExprRef(11), LambdaType::e().clone()),
            LambdaExpr::FreeVariable(1337, LambdaType::t().clone()),
            LambdaExpr::FreeVariable(5, LambdaType::e().clone()),
        ]);
        pool.reduce(LambdaExprRef(0))?;
        assert_eq!(
            pool,
            LambdaPool(vec![LambdaExpr::FreeVariable(
                1337,
                LambdaType::t().clone()
            )])
        );
        Ok(())
    }

    #[test]
    fn test_lambda_calculus() -> anyhow::Result<()> {
        let mut pool = LambdaPool::<()>(
            k(0)?
                .into_iter()
                .chain([
                    LambdaExpr::FreeVariable(32, LambdaType::e().clone()),
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
                LambdaExpr::FreeVariable(32, LambdaType::e().clone()),
                LambdaExpr::Lambda(LambdaExprRef(0), LambdaType::e().clone())
            ])
        );
        Ok(())
    }

    use crate::language::lot_parser;
    use chumsky::prelude::*;

    #[test]
    fn test_root_and_merger() -> anyhow::Result<()> {
        let mut labels = LabelledScenarios::default();
        let parser = lot_parser::<extra::Err<Rich<_>>>().then_ignore(end());
        let man = parser
            .parse("lambda a x (pa_man(x))")
            .unwrap()
            .to_pool(&mut labels)?;

        let sleeps = parser
            .parse("lambda a x (some_e(y, all_e, AgentOf(x, y) & pe_sleep(y)))")
            .unwrap()
            .to_pool(&mut labels)?;
        let every = parser
            .parse("lambda <a,t> p(lambda <a,t> q(every(x, p(x), q(x))))")
            .unwrap()
            .to_pool(&mut labels)
            .unwrap();

        let phi = every.clone().merge(man.clone()).unwrap();
        let mut phi = phi.merge(sleeps.clone()).unwrap();
        phi.reduce()?;
        let pool = phi.into_pool()?;
        assert_eq!(
            "every(x,pa0(x),some_e(y,all_e,(AgentOf(x,y) & pe1(y))))",
            pool.to_string()
        );
        let phi = man.merge(every).unwrap();
        let mut phi = sleeps.merge(phi).unwrap();
        phi.reduce()?;
        let pool = phi.into_pool()?;
        assert_eq!(
            "every(x,pa0(x),some_e(y,all_e,(AgentOf(x,y) & pe1(y))))",
            pool.to_string()
        );
        Ok(())
    }

    #[test]
    fn bind_free_variable() -> anyhow::Result<()> {
        let mut labels = LabelledScenarios::default();
        let parser = lot_parser::<extra::Err<Rich<_>>>().then_ignore(end());
        let mut pool = parser
            .parse("phi_t#t & True")
            .unwrap()
            .to_pool(&mut labels)?;

        pool.bind_free_variable(0, parser.parse("False").unwrap().to_pool(&mut labels)?)?;
        assert_eq!("(False & True)", pool.into_pool()?.to_string());

        let input = parser
            .parse("lambda a x (every_e(y,pe4,AgentOf(x,y)))")
            .unwrap()
            .to_pool(&mut labels)?;
        let mut a = parser
            .parse("(P#<a,t>(a3) & ~P#<a,t>(a1))")
            .unwrap()
            .to_pool(&mut labels)?;

        a.bind_free_variable(1, input)?;
        a.reduce()?;
        assert_eq!(
            a.to_string(),
            "(every_e(x,pe4,AgentOf(a3,x)) & ~(every_e(x,pe4,AgentOf(a1,x))))"
        );
        Ok(())
    }

    #[test]
    fn apply_new_free_variable() -> anyhow::Result<()> {
        let mut labels = LabelledScenarios::default();
        let parser = lot_parser::<extra::Err<Rich<_>>>().then_ignore(end());
        let mut pool = parser
            .parse("lambda <e,t> P (lambda <e,t> Q (lambda e x (P(x) & Q(x))))")
            .unwrap()
            .to_pool(&mut labels)?;

        pool.apply_new_free_variable(0)?;

        let gold_pool = RootedLambdaPool {
            pool: LambdaPool(vec![
                LambdaExpr::FreeVariable(0, LambdaType::et().clone()),
                LambdaExpr::BoundVariable(0, LambdaType::e().clone()),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(0),
                    argument: LambdaExprRef(1),
                },
                LambdaExpr::BoundVariable(1, LambdaType::et().clone()),
                LambdaExpr::BoundVariable(0, LambdaType::e().clone()),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(3),
                    argument: LambdaExprRef(4),
                },
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(2), ExprRef(5))),
                LambdaExpr::Lambda(LambdaExprRef(6), LambdaType::e().clone()),
                LambdaExpr::Lambda(LambdaExprRef(7), LambdaType::et().clone()),
            ]),
            root: LambdaExprRef(8),
        };
        assert_eq!(pool, gold_pool);
        Ok(())
    }

    #[test]
    fn lambda_abstraction() -> anyhow::Result<()> {
        let mut labels = LabelledScenarios::default();
        let parser = lot_parser::<extra::Err<Rich<_>>>().then_ignore(end());
        let mut pool = parser
            .parse("lambda <e,t> P (lambda <e,t> Q (lambda e x (Z#<e,t>(x) & P(x) & Q(x))))")
            .unwrap()
            .to_pool(&mut labels)?;

        pool.lambda_abstract_free_variable(0, LambdaType::et().clone(), false)?;

        let gold_pool = RootedLambdaPool {
            pool: LambdaPool(vec![
                LambdaExpr::BoundVariable(3, LambdaType::et().clone()),
                LambdaExpr::BoundVariable(0, LambdaType::e().clone()),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(0),
                    argument: LambdaExprRef(1),
                },
                LambdaExpr::BoundVariable(2, LambdaType::et().clone()),
                LambdaExpr::BoundVariable(0, LambdaType::e().clone()),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(3),
                    argument: LambdaExprRef(4),
                },
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(2), ExprRef(5))),
                LambdaExpr::BoundVariable(1, LambdaType::et().clone()),
                LambdaExpr::BoundVariable(0, LambdaType::e().clone()),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(7),
                    argument: LambdaExprRef(8),
                },
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(6), ExprRef(9))),
                LambdaExpr::Lambda(LambdaExprRef(10), LambdaType::e().clone()),
                LambdaExpr::Lambda(LambdaExprRef(11), LambdaType::et().clone()),
                LambdaExpr::Lambda(LambdaExprRef(12), LambdaType::et().clone()),
                LambdaExpr::Lambda(LambdaExprRef(13), LambdaType::et().clone()),
            ]),
            root: LambdaExprRef(14),
        };

        assert_eq!(pool, gold_pool);
        Ok(())
    }

    #[test]
    fn could_time_out_if_swapping_instead_of_cloning() -> anyhow::Result<()> {
        let p = lot_parser::<extra::Err<Rich<_>>>();
        let mut labels = LabelledScenarios::default();
        let mut x = p
            .parse("(lambda a x_l (PatientOf(x_l,x_l)))((lambda a x_l (a1))(a0))")
            .unwrap()
            .to_pool(&mut labels)?;

        println!("{x}");
        x.reduce()?;
        println!("{x}");
        Ok(())
    }

    #[test]
    fn lambda_abstraction_reduction() -> anyhow::Result<()> {
        let p = lot_parser::<extra::Err<Rich<_>>>();
        let mut labels = LabelledScenarios::default();
        let mut a = p.parse("a1").unwrap().to_pool(&mut labels)?;
        let mut b = p
            .parse("(lambda t x_l (a1))(pa0(free_var#a))")
            .unwrap()
            .to_pool(&mut labels)?;

        a.lambda_abstract_free_variable(0, LambdaType::a().clone(), false)?;
        b.lambda_abstract_free_variable(0, LambdaType::a().clone(), false)?;
        println!("A:\t{a}");
        println!("B:\t{b}");

        assert_eq!(a, b);
        Ok(())
    }

    #[test]
    fn reduction_test() -> anyhow::Result<()> {
        let p = lot_parser::<extra::Err<Rich<_>>>();
        let mut labels = LabelledScenarios::default();
        let mut a = p
            .parse(
                "lambda a x (every_e(z, all_e, AgentOf((lambda e y ((lambda e w (w))(y)))(z), a0)))",
            )
            .unwrap().to_pool(&mut labels)?;
        a.reduce()?;

        let mut a = p
            .parse("(lambda <a,t> P (P(a3) & ~P(a1)))(lambda a x (every_e(y,pe4,AgentOf(x,y))))")
            .unwrap()
            .to_pool(&mut labels)?;

        a.pool.beta_reduce(a.root)?;
        a.root = a.pool.cleanup(a.root);
        println!("{a}");
        dbg!(&a);

        let mut a = p
            .parse("(lambda <a,t> P (P(a3) & ~P(a1)))(lambda a x (every_e(y,pe4,AgentOf(x,y))))")
            .unwrap()
            .to_pool(&mut labels)?;

        a.reduce()?;
        assert_eq!(
            a.to_string(),
            "(every_e(x,pe4,AgentOf(a3,x)) & ~(every_e(x,pe4,AgentOf(a1,x))))"
        );

        Ok(())
    }

    #[test]
    fn expr_type_checks() -> anyhow::Result<()> {
        let p = lot_parser::<extra::Err<Rich<_>>>();
        let mut labels = LabelledScenarios::default();
        let a = p
            .parse(
                "lambda a x (every_e(z, all_e, AgentOf((lambda e y ((lambda e w (w))(y)))(z), a0)))",
            )
            .unwrap().to_pool(&mut labels)?;
        assert_eq!(
            a.get_expression_type(a.root)?,
            ExpressionType {
                output: LambdaType::at().clone(),
                arguments: vec![LambdaType::t().clone()]
            }
        );

        assert_eq!(
            //all_e
            a.get_expression_type(LambdaExprRef(0))?,
            ExpressionType {
                output: LambdaType::et().clone(),
                arguments: vec![]
            }
        );

        assert_eq!(
            //agentof
            a.get_expression_type(LambdaExprRef(9))?,
            ExpressionType {
                output: LambdaType::t().clone(),
                arguments: vec![LambdaType::a().clone(), LambdaType::e().clone()]
            }
        );

        assert_eq!(
            //(lambda e w (w))(y)
            a.get_expression_type(LambdaExprRef(4))?,
            ExpressionType {
                output: LambdaType::e().clone(),
                arguments: vec![
                    LambdaType::compose(LambdaType::e().clone(), LambdaType::e().clone()),
                    LambdaType::e().clone()
                ]
            }
        );
        Ok(())
    }
}
