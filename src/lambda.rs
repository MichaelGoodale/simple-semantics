//! The module that defines the basic lambda calculus used to compose expressions in the langauge
//! of thought.

use core::sync;
use itertools::Either;
use serde::{Deserialize, Serialize};
use smallvec::{SmallVec, smallvec};
use std::{
    cmp::Ordering,
    collections::{HashSet, VecDeque},
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
    mem::discriminant,
};
use thiserror::Error;

mod interpretation;
pub mod types;
use types::{LambdaType, TypeError};

use crate::lambda::types::LambdaType::A;

mod parser;
mod printing;

pub(crate) type Bvar = usize;

///Errors resulting from interacting with a lambda calculus expression.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum LambdaError {
    ///A function application which violates the type system
    #[error("The free variable has type {free_var} while the argument is {arg}")]
    BadFreeVariableApp {
        ///The type of the free variable involved
        free_var: LambdaType,
        ///The argument applied to a free variable.
        arg: LambdaType,
    },
    ///A free variable that violates the type sytem
    #[error("The free variable has type {free_var} while its lambda takes {lambda}")]
    BadFreeVariable {
        ///The type of the free variable involved
        free_var: LambdaType,
        ///The argument applied to a free variable.
        lambda: LambdaType,
    },

    ///An internally caused error if `DeBruijn` indices are invalid.
    #[error(
        "A bound variable {var:?} cannot have a DeBruijn index higher than its lambda depth ({depth})"
    )]
    BadBoundVariable {
        ///The `DeBruijn` index
        var: LambdaExprRef,
        ///The depth of the expression
        depth: usize,
    },

    ///Any internal type error.
    #[error("Expression has type error ({0})")]
    TypeError(#[from] TypeError),

    ///An error caused by a failed reduction
    #[error("Failed reduction: {0}")]
    ReductionError(#[from] ReductionError),
}

///A conversion error used when converting to a [`RootedLambdaPool`] from a [`Vec<Option<LambdaExpr>>`]
#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum LambdaTryFromError {
    ///This error happens if the vector is not exclusively [`Some`].
    #[error("The vec contains None")]
    HasNone,
}

///An error from a faulty reduction
#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum ReductionError {
    ///A invalid reference to a [`LambdaExpr`] is passed.
    #[error("{0:?} is not a valid ref!")]
    NotValidRef(LambdaExprRef),
    ///A reference to a [`LambdaExpr`] which is not an application is passed
    #[error("{0:?} is not an application!")]
    NotApplication(LambdaExprRef),

    ///A reference to a [`LambdaExpr`] which is not a lambda(app(b, x))  is passed
    #[error("{0:?} is not an application!")]
    NoEtaReduction(LambdaExprRef),

    ///An application that doesn't apply a lambda expression
    #[error("The left hand side of the application ({app:?}), {lhs:?} is not a lambda expression!")]
    NotLambdaInApplication {
        ///The entire application
        app: LambdaExprRef,
        ///The left hand side of the application, which should be but isn't a lambda expression
        lhs: LambdaExprRef,
    },

    ///Any general malformed types.
    #[error("Incorrect types: {0}")]
    TypeError(#[from] TypeError),
}

///An index to a [`LambdaExpr`] in the lambda pool.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct LambdaExprRef(pub u32);

impl LambdaExprRef {
    pub(crate) fn new(x: usize) -> Self {
        LambdaExprRef(u32::try_from(x).expect("Reference is too high!"))
    }
}

///A trait which allows one to define a language of thought that interacts with the lambda
///calculus. An example implementation can be found for [`crate::language::Expr`].
pub trait LambdaLanguageOfThought {
    ///Returns the type of the bound variable at an instruction, if any
    fn var_type(&self) -> Option<&LambdaType>;

    ///Returns whether an expression has no body, one or two. (If one or two, [`Self::var_type`]
    ///must not return `None` for that expression).
    fn bind_vars(&self) -> PrimitiveVarType;

    ///Get the type of an expression.
    fn typ(&self) -> &LambdaType;

    ///Does the primitive function as an infix? (Must be a two-place function).
    ///For example, `phi & psi`, & is an infix.
    fn infix(&self) -> bool {
        false
    }

    ///Can the function be repeatedly applied to itself?
    ///Allows parsing !(!(!(phi))) as !!!phi
    fn unary_associative(&self) -> bool {
        false
    }

    ///Checks whether an expression is commutative
    fn commutative(&self) -> bool {
        false
    }
}

impl LambdaLanguageOfThought for () {
    fn typ(&self) -> &LambdaType {
        &LambdaType::T
    }

    fn var_type(&self) -> Option<&LambdaType> {
        None
    }

    fn bind_vars(&self) -> PrimitiveVarType {
        PrimitiveVarType::NoVar
    }
}

///A free variable which can either be named or refered to by a integer.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum FreeVar<'a> {
    ///A labeled free variable
    #[serde(borrow)]
    Named(&'a str),
    ///An anonymous free variable defined by an index.
    Anonymous(usize),
}

impl Display for FreeVar<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FreeVar::Named(s) => write!(f, "{s}"),
            FreeVar::Anonymous(t) => write!(f, "{t}"),
        }
    }
}

impl<'a> From<&'a str> for FreeVar<'a> {
    fn from(value: &'a str) -> Self {
        FreeVar::Named(value)
    }
}

impl From<usize> for FreeVar<'_> {
    fn from(value: usize) -> Self {
        FreeVar::Anonymous(value)
    }
}

///An indicator type that defines the [`ExprType`] used in an expression
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum PrimitiveVarType {
    ///Doesn't have a child
    NoVar,
    ///Binds a variable and has one child/body.
    BindVar,
    ///Binds a variable and has two children/bodies.
    BindVarTwoBodies,
}

///Whether a LOT primitive directly binds syntactic children.
///If it does, it assumes that it is also binding a variable.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ExprType {
    ///A normal primitive without binding children.
    NoVar,
    ///A primitive that binds one child, e.g. some(x, P(x))
    BindVar(LambdaExprRef),
    ///A primitive that binds two children (such as in generalized quantifiers),
    ///For example,  some(x, P(x), Q(x))
    BindVarTwoBodies(LambdaExprRef, LambdaExprRef),
}

impl From<ExprType> for PrimitiveVarType {
    fn from(value: ExprType) -> Self {
        match value {
            ExprType::NoVar => PrimitiveVarType::NoVar,
            ExprType::BindVar(_) => PrimitiveVarType::BindVar,
            ExprType::BindVarTwoBodies(..) => PrimitiveVarType::BindVarTwoBodies,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
///The core expression type of a lambda term
pub enum LambdaExpr<'a, T> {
    ///A lambda of a given type.
    Lambda(LambdaExprRef, LambdaType),
    ///A variable bound by a lambda, labeled by its [De Bruijn index](https://en.wikipedia.org/wiki/De_Bruijn_index).
    BoundVariable(Bvar, LambdaType),
    ///A free variable (may be named or anonymous, see [`FreeVar`]).
    FreeVariable(#[serde(borrow)] FreeVar<'a>, LambdaType),
    ///The application of an argument to a function
    Application {
        ///The body of the function
        subformula: LambdaExprRef,

        ///The argument of the function
        argument: LambdaExprRef,
    },
    ///Any expression which is not part of the lambda calculus directly (e.g. primitives). See
    ///[`crate::Expr`] for an example.
    LanguageOfThoughtExpr(T, ExprType),
}

impl<T: LambdaLanguageOfThought> LambdaExpr<'_, T> {
    pub(crate) fn var_type(&self) -> Option<&LambdaType> {
        match self {
            LambdaExpr::Lambda(_, lambda_type) => Some(lambda_type),
            LambdaExpr::LanguageOfThoughtExpr(e, _) => e.var_type(),
            LambdaExpr::BoundVariable(..)
            | LambdaExpr::FreeVariable(..)
            | LambdaExpr::Application { .. } => None,
        }
    }
    pub(crate) fn inc_depth(&self) -> bool {
        match self {
            LambdaExpr::Lambda(..)
            | LambdaExpr::LanguageOfThoughtExpr(
                _,
                ExprType::BindVar(_) | ExprType::BindVarTwoBodies(..),
            ) => true,
            LambdaExpr::LanguageOfThoughtExpr(_, ExprType::NoVar)
            | LambdaExpr::BoundVariable(..)
            | LambdaExpr::FreeVariable(..)
            | LambdaExpr::Application { .. } => false,
        }
    }

    pub(crate) fn commutative(&self) -> bool {
        match self {
            LambdaExpr::LanguageOfThoughtExpr(e, _) => e.commutative(),
            LambdaExpr::Lambda(..)
            | LambdaExpr::BoundVariable(..)
            | LambdaExpr::FreeVariable(..)
            | LambdaExpr::Application { .. } => false,
        }
    }
}

#[derive(Debug, Clone)]
///A lambda expression with its root defined.
pub struct RootedLambdaPool<'src, T: LambdaLanguageOfThought> {
    pub(crate) pool: LambdaPool<'src, T>,
    pub(crate) root: LambdaExprRef,
}

impl<T: PartialEq + LambdaLanguageOfThought> PartialEq for RootedLambdaPool<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        let mut bfs = self.pool.bfs_from(self.root).map(|(x, _)| self.pool.get(x));
        let mut o_bfs = other
            .pool
            .bfs_from(other.root)
            .map(|(x, _)| other.pool.get(x));
        loop {
            let x = bfs.next();
            let y = o_bfs.next();
            match (x, y) {
                (None, None) => return true,
                (None, Some(_)) | (Some(_), None) => return false,
                (Some(x), Some(y)) => match (x, y) {
                    (LambdaExpr::Lambda(_, a), LambdaExpr::Lambda(_, b)) if a != b => {
                        return false;
                    }
                    (
                        LambdaExpr::BoundVariable(id1, typ1),
                        LambdaExpr::BoundVariable(id2, typ2),
                    ) if id1 != id2 || typ1 != typ2 => {
                        return false;
                    }
                    (
                        LambdaExpr::FreeVariable(var1, typ1),
                        LambdaExpr::FreeVariable(var2, typ2),
                    ) if var1 != var2 || typ1 != typ2 => return false,
                    (
                        LambdaExpr::LanguageOfThoughtExpr(x, expr_type1),
                        LambdaExpr::LanguageOfThoughtExpr(y, expr_type2),
                    ) if (x != y
                        || !matches!(
                            (expr_type1, expr_type2),
                            (ExprType::NoVar, ExprType::NoVar)
                                | (ExprType::BindVar(_), ExprType::BindVar(_))
                                | (
                                    ExprType::BindVarTwoBodies(..),
                                    ExprType::BindVarTwoBodies(..)
                                )
                        )) =>
                    {
                        return false;
                    }
                    //If they have different kinds, their discriminant is different.
                    (x, y) if discriminant(x) != discriminant(y) => return false,
                    _ => (),
                },
            }
        }
    }
}
impl<T: PartialEq + LambdaLanguageOfThought> Eq for RootedLambdaPool<'_, T> {}

impl<T: LambdaLanguageOfThought + Ord> PartialOrd for RootedLambdaPool<'_, T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: LambdaLanguageOfThought + Ord> Ord for RootedLambdaPool<'_, T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.appless_len().cmp(&other.appless_len()).then_with(|| {
            let mut stack: SmallVec<[_; 2]> = smallvec![(self.root, other.root)];
            while let Some((alpha, beta)) = stack.pop() {
                let alpha = self.get(alpha);
                let beta = other.get(beta);
                match alpha.cmp_expr(beta) {
                    Ordering::Equal => alpha
                        .get_children()
                        .zip(beta.get_children())
                        .for_each(|x| stack.push(x)),
                    Ordering::Less => return Ordering::Less,
                    Ordering::Greater => return Ordering::Greater,
                }
            }
            Ordering::Equal
        })
    }
}

impl<T: LambdaLanguageOfThought + Ord> LambdaExpr<'_, T> {
    fn ordering(&self) -> usize {
        match self {
            LambdaExpr::Lambda(..) => 0,
            LambdaExpr::BoundVariable(..) => 1,
            LambdaExpr::FreeVariable(..) => 2,
            LambdaExpr::Application { .. } => 3,
            LambdaExpr::LanguageOfThoughtExpr(..) => 4,
        }
    }

    fn cmp_expr(&self, other: &Self) -> std::cmp::Ordering {
        self.ordering()
            .cmp(&other.ordering())
            .then_with(|| match (self, other) {
                (LambdaExpr::Lambda(_, lambda_type), LambdaExpr::Lambda(_, o_type)) => {
                    lambda_type.cmp(o_type)
                }
                (
                    LambdaExpr::BoundVariable(x, lambda_type),
                    LambdaExpr::BoundVariable(y, o_type),
                ) => x.cmp(y).then(lambda_type.cmp(o_type)),
                (LambdaExpr::FreeVariable(x, lambda_type), LambdaExpr::FreeVariable(y, o_type)) => {
                    x.cmp(y).then(lambda_type.cmp(o_type))
                }
                (LambdaExpr::Application { .. }, LambdaExpr::Application { .. }) => Ordering::Equal,
                (
                    LambdaExpr::LanguageOfThoughtExpr(x, x_bind_type),
                    LambdaExpr::LanguageOfThoughtExpr(y, y_bind_type),
                ) => {
                    let x_bind_type = PrimitiveVarType::from(*x_bind_type);
                    let y_bind_type = PrimitiveVarType::from(*y_bind_type);
                    x_bind_type.cmp(&y_bind_type).then(x.cmp(y))
                }

                _ => panic!("Previous check ensures they are the same variant"),
            })
    }
}

impl<T: LambdaLanguageOfThought + Hash> Hash for RootedLambdaPool<'_, T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        for x in self.pool.bfs_from(self.root).map(|(x, _)| self.pool.get(x)) {
            match x {
                LambdaExpr::Lambda(_, lambda_type) => {
                    0.hash(state);
                    lambda_type.hash(state);
                }
                LambdaExpr::BoundVariable(a, lambda_type) => {
                    1.hash(state);
                    a.hash(state);
                    lambda_type.hash(state);
                }
                LambdaExpr::FreeVariable(free_var, lambda_type) => {
                    2.hash(state);
                    free_var.hash(state);
                    lambda_type.hash(state);
                }
                LambdaExpr::Application { .. } => {
                    3.hash(state);
                }
                LambdaExpr::LanguageOfThoughtExpr(x, _) => {
                    4.hash(state);
                    x.hash(state);
                }
            }
        }
    }
}

impl<T: LambdaLanguageOfThought + PartialEq> LambdaExpr<'_, T> {
    fn same_expr(&self, other: &Self) -> bool {
        match self {
            LambdaExpr::Lambda(_, lambda_type) => {
                matches!(other, LambdaExpr::Lambda(_, other_type) if lambda_type == other_type)
            }
            LambdaExpr::BoundVariable(x, a) => {
                matches!(other, LambdaExpr::BoundVariable(y, b) if x==y && a==b)
            }
            LambdaExpr::FreeVariable(free_var, lambda_type) => {
                matches!(other, LambdaExpr::FreeVariable(o_var, o_type) if o_var == free_var && o_type == lambda_type)
            }
            LambdaExpr::Application { .. } => matches!(self, LambdaExpr::Application { .. }),
            LambdaExpr::LanguageOfThoughtExpr(x, ..) => {
                matches!(other, LambdaExpr::LanguageOfThoughtExpr(y,..) if x == y)
            }
        }
    }
}

impl<'src, T: LambdaLanguageOfThought> RootedLambdaPool<'src, T> {
    ///The length of the expression, excluding the number of [`LambdaExpr::Application`].
    ///Corresponds better to human intuitions about length.
    pub fn appless_len(&self) -> usize {
        self.pool
            .bfs_from(self.root)
            .filter(|(x, _)| !matches!(self.get(*x), LambdaExpr::Application { .. }))
            .count()
    }

    ///Check if the expression is fully reduced or not.
    pub fn is_reduced(&self) -> bool {
        self.pool.get_next_app(self.root).is_none()
    }

    ///Creates an anonymous free variable with [`index`] of type [`t`]
    #[must_use]
    pub fn new_free_variable(index: usize, t: LambdaType) -> RootedLambdaPool<'src, T> {
        RootedLambdaPool {
            pool: LambdaPool(vec![LambdaExpr::FreeVariable(FreeVar::Anonymous(index), t)]),
            root: LambdaExprRef(0),
        }
    }

    ///Gets all free variables that must be bound in order to evaluate this lambda expression
    pub fn free_variables(&self) -> impl Iterator<Item = (&FreeVar<'src>, &LambdaType)> {
        self.pool.0.iter().filter_map(|x| {
            if let LambdaExpr::FreeVariable(free_var, lambda_type) = x {
                Some((free_var, lambda_type))
            } else {
                None
            }
        })
    }

    pub(crate) fn root(&self) -> LambdaExprRef {
        self.root
    }

    ///Get the expression of a lambda term.
    pub(crate) fn get(&self, x: LambdaExprRef) -> &LambdaExpr<'src, T> {
        self.pool.get(x)
    }

    ///Get the length of a lambda tree
    #[allow(clippy::len_without_is_empty)]
    #[must_use]
    pub fn len(&self) -> usize {
        self.pool.0.len()
    }
}

impl<'src, T: LambdaLanguageOfThought + Clone> RootedLambdaPool<'src, T> {
    ///Clean up dangling references.
    pub fn cleanup(&mut self) {
        self.root = self.pool.cleanup(self.root);
    }

    ///Reduce a lambda expression
    ///
    ///# Errors
    ///Will throw a [`ReductionError`] if there is something makes the reduction improper.
    pub fn reduce(&mut self) -> Result<(), ReductionError> {
        self.pool.reduce(self.root)?;
        Ok(())
    }

    ///Replace a free variable with a value.
    ///
    ///# Errors
    ///Will return an error if a [`FreeVar`] with the same name but different type already exists
    pub fn bind_free_variable(
        &mut self,
        fvar: FreeVar<'src>,
        replacement: RootedLambdaPool<'src, T>,
    ) -> Result<(), LambdaError> {
        let (other_pool, other_root) = replacement.split();
        let other_root = self.pool.extend_pool(other_root, other_pool);
        self.pool.bind_free_variable(self.root, fvar, other_root)?;
        //self.root = self.pool.cleanup(self.root);
        Ok(())
    }

    ///Replace a free variable by lambda abstracting it. (e.g. $P(x_{free})$ to $\lambda x P(x)$).
    ///
    ///# Errors
    ///Will throw an error if the free variable has the wrong type.
    pub fn lambda_abstract_free_variable(
        &mut self,
        fvar: FreeVar<'src>,
        lambda_type: LambdaType,
        always_abstract: bool,
    ) -> Result<(), LambdaError> {
        self.reduce()?;
        let vars = self
            .pool
            .bfs_from(self.root)
            .filter_map(|(x, d)| match self.pool.get(x) {
                LambdaExpr::FreeVariable(var, var_type) if *var == fvar => {
                    if &lambda_type == var_type {
                        Some(Ok((x, d)))
                    } else {
                        Some(Err(LambdaError::BadFreeVariable {
                            free_var: var_type.clone(),
                            lambda: lambda_type.clone(),
                        }))
                    }
                }
                _ => None,
            })
            .collect::<Result<Vec<_>, LambdaError>>()?;

        if !vars.is_empty() || always_abstract {
            for (x, lambda_depth) in vars {
                *self.pool.get_mut(x) =
                    LambdaExpr::BoundVariable(lambda_depth, lambda_type.clone());
            }
            self.root = self.pool.add(LambdaExpr::Lambda(self.root, lambda_type));
        }
        Ok(())
    }

    ///Apply a free variable to a function.
    ///
    ///# Errors
    ///Will throw an error if there is an issue with the reduction
    pub fn apply_new_free_variable(
        &mut self,
        fvar: FreeVar<'src>,
    ) -> Result<LambdaType, LambdaError> {
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

impl<'src, T: LambdaLanguageOfThought> RootedLambdaPool<'src, T> {
    ///The type of the lambda expression
    ///
    ///# Errors
    ///Returns a [`TypeError`] if the underlying pool is malformed leading to no possible type
    ///being extractible.
    pub fn get_type(&self) -> Result<LambdaType, TypeError> {
        self.pool.get_type(self.root)
    }

    ///Create a new lambda expression.
    pub(crate) fn new(pool: LambdaPool<'src, T>, root: LambdaExprRef) -> Self {
        RootedLambdaPool { pool, root }
    }

    ///Split into the pool and root seperately.
    pub(crate) fn split(self) -> (LambdaPool<'src, T>, LambdaExprRef) {
        (self.pool, self.root)
    }

    ///Combine two lambda expressions by applying one to the other. Returns [`None`] if that is
    ///impossible.
    ///
    ///# Panics
    ///Will panic if either pool is malformed such that no type can be found.
    #[must_use]
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

        let (other_pool, other_root) = other.split();
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

    ///Applies other to self and returns None if the types do not correspond.
    ///
    ///# Panics
    ///Will panic if either pool is malformed such that no type can be found.
    #[must_use]
    pub fn apply(mut self, other: Self) -> Option<Self> {
        let self_type = self.pool.get_type(self.root).expect("malformed type");
        let other_type = other.pool.get_type(other.root).expect("malformed type");

        if !self_type.can_apply(&other_type) {
            return None;
        }
        let (other_pool, other_root) = other.split();
        let other_root = self.pool.extend_pool(other_root, other_pool);

        self.root = self.pool.add(LambdaExpr::Application {
            subformula: self.root,
            argument: other_root,
        });

        Some(self)
    }
}

#[derive(Default, Debug, Clone, Eq, PartialEq, Hash)]
pub(crate) struct LambdaPool<'a, T: LambdaLanguageOfThought>(pub(crate) Vec<LambdaExpr<'a, T>>);

impl<'src, T: LambdaLanguageOfThought + Sized> LambdaPool<'src, T> {
    pub(crate) fn extend_pool(
        &mut self,
        mut other_root: LambdaExprRef,
        mut other_pool: LambdaPool<'src, T>,
    ) -> LambdaExprRef {
        let shift_n = u32::try_from(self.0.len()).unwrap();
        let remap: Vec<_> = (0..u32::try_from(other_pool.0.len()).unwrap())
            .map(|x| x + shift_n)
            .collect();
        other_pool.0.iter_mut().for_each(|x| x.remap_refs(&remap));
        other_root.0 += shift_n;
        self.0.append(&mut other_pool.0);
        other_root
    }

    ///Convert from [`Vec<LambdaExpr<T>>`] to [`LambdaPool`]
    pub fn from(x: Vec<LambdaExpr<'src, T>>) -> Self {
        LambdaPool(x)
    }

    ///Create a new, empty [`LambdaPool`]
    pub fn new<'c>() -> LambdaPool<'c, T> {
        LambdaPool(vec![])
    }

    fn checked_get(&self, expr: LambdaExprRef) -> Option<&LambdaExpr<'src, T>> {
        self.0.get(expr.0 as usize)
    }

    ///Get the [`LambdaExpr`] at an index.
    pub fn get(&self, expr: LambdaExprRef) -> &LambdaExpr<'src, T> {
        &self.0[expr.0 as usize]
    }

    pub fn get_mut<'a>(&'a mut self, expr: LambdaExprRef) -> &'a mut LambdaExpr<'src, T> {
        &mut self.0[expr.0 as usize]
    }

    pub fn add(&mut self, expr: LambdaExpr<'src, T>) -> LambdaExprRef {
        let idx = self.0.len();
        self.0.push(expr);
        LambdaExprRef(idx.try_into().expect("Too many exprs in the pool"))
    }
}

///Iterate over a lambda pool in breadth-first search
pub(crate) struct LambdaPoolBFSIterator<'a, 'src, T: LambdaLanguageOfThought> {
    pool: &'a LambdaPool<'src, T>,
    queue: VecDeque<(LambdaExprRef, Bvar)>,
}

impl<T: LambdaLanguageOfThought> LambdaExpr<'_, T> {
    pub(crate) fn n_children(&self) -> usize {
        match self {
            LambdaExpr::BoundVariable(..) | LambdaExpr::FreeVariable(..) => 0,
            LambdaExpr::Lambda(..) => 1,
            LambdaExpr::Application { .. } => 2,
            LambdaExpr::LanguageOfThoughtExpr(_, ExprType::NoVar) => 0,
            LambdaExpr::LanguageOfThoughtExpr(_, ExprType::BindVar(_)) => 1,
            LambdaExpr::LanguageOfThoughtExpr(_, ExprType::BindVarTwoBodies(..)) => 2,
        }
    }

    pub(crate) fn get_children(&self) -> impl Iterator<Item = LambdaExprRef> {
        match self {
            LambdaExpr::Lambda(x, _) => Either::Left([x].into_iter().copied()),
            LambdaExpr::Application {
                subformula,
                argument,
            } => Either::Right(Either::Left([subformula, argument].into_iter().copied())),
            LambdaExpr::BoundVariable(..) | LambdaExpr::FreeVariable(..) => {
                Either::Right(Either::Right(std::iter::empty()))
            }
            LambdaExpr::LanguageOfThoughtExpr(_, ExprType::NoVar) => {
                Either::Right(Either::Right(std::iter::empty()))
            }
            LambdaExpr::LanguageOfThoughtExpr(_, ExprType::BindVar(x)) => {
                Either::Left([x].into_iter().copied())
            }
            LambdaExpr::LanguageOfThoughtExpr(_, ExprType::BindVarTwoBodies(a, b)) => {
                Either::Right(Either::Left([a, b].into_iter().copied()))
            }
        }
    }
}

impl<T: LambdaLanguageOfThought> Iterator for LambdaPoolBFSIterator<'_, '_, T> {
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
                LambdaExpr::LanguageOfThoughtExpr(_, expr_type) => match expr_type {
                    ExprType::NoVar => (),
                    ExprType::BindVar(x) => {
                        self.queue.push_back((*x, lambda_depth + 1));
                    }
                    ExprType::BindVarTwoBodies(x, y) => {
                        self.queue.push_back((*x, lambda_depth + 1));
                        self.queue.push_back((*y, lambda_depth + 1));
                    }
                },
            }
            Some((x, lambda_depth))
        } else {
            None
        }
    }
}

///Iterate over a lambda pool and return a mutable reference
pub(crate) struct MutableLambdaPoolBFSIterator<'a, 'src: 'a, T: LambdaLanguageOfThought + 'a> {
    pool: *mut LambdaPool<'src, T>,
    queue: VecDeque<(LambdaExprRef, Bvar)>,
    phantom: PhantomData<&'a ()>,
}

impl<'a, 'src: 'a, T: LambdaLanguageOfThought + 'a> MutableLambdaPoolBFSIterator<'a, 'src, T> {
    fn new(pool: &mut LambdaPool<'src, T>, x: LambdaExprRef) -> Self {
        Self {
            pool: std::ptr::from_mut::<LambdaPool<'src, T>>(pool),
            queue: VecDeque::from([(x, 0)]),
            phantom: PhantomData,
        }
    }
}

impl<'a, 'src, T: LambdaLanguageOfThought> Iterator for MutableLambdaPoolBFSIterator<'a, 'src, T> {
    type Item = (&'a mut LambdaExpr<'src, T>, usize, LambdaExprRef);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((x, lambda_depth)) = self.queue.pop_front() {
            let expr = unsafe { self.pool.as_ref().unwrap() };
            match expr.get(x) {
                LambdaExpr::Lambda(x, _) => self.queue.push_back((*x, lambda_depth + 1)),
                LambdaExpr::Application {
                    subformula,
                    argument,
                } => {
                    self.queue.push_back((*subformula, lambda_depth));
                    self.queue.push_back((*argument, lambda_depth));
                }
                LambdaExpr::BoundVariable(..) | LambdaExpr::FreeVariable(..) => (),
                LambdaExpr::LanguageOfThoughtExpr(_, expr_type) => match expr_type {
                    ExprType::NoVar => (),
                    ExprType::BindVar(x) => {
                        self.queue.push_back((*x, lambda_depth + 1));
                    }
                    ExprType::BindVarTwoBodies(x, y) => {
                        self.queue.push_back((*x, lambda_depth + 1));
                        self.queue.push_back((*y, lambda_depth + 1));
                    }
                },
            }
            Some((
                unsafe { self.pool.as_mut().unwrap().get_mut(x) },
                lambda_depth,
                x,
            ))
        } else {
            None
        }
    }
}

impl<'src, T: LambdaLanguageOfThought> LambdaPool<'src, T> {
    pub(crate) fn bfs_from(&self, x: LambdaExprRef) -> LambdaPoolBFSIterator<'_, 'src, T> {
        LambdaPoolBFSIterator {
            pool: self,
            queue: VecDeque::from([(x, 0)]),
        }
    }
}
impl<'src, T: LambdaLanguageOfThought> LambdaPool<'src, T> {
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
            LambdaExpr::LanguageOfThoughtExpr(x, ExprType::NoVar) => Ok(x.typ().clone()),
            LambdaExpr::LanguageOfThoughtExpr(x, ExprType::BindVar(_)) => {
                let (_, y) = x
                    .typ()
                    .split()
                    .expect("Implementation Error: If binding a variable body, the expression must be a function");
                Ok(y.clone())
            }
            LambdaExpr::LanguageOfThoughtExpr(x, ExprType::BindVarTwoBodies(..)) => {
                let (_, y) = x
                    .typ()
                    .split().and_then(|(_, x)| x.split())
                    .expect("Implementation Error: If binding a variable body, the expression must be a two-place function");
                Ok(y.clone())
            }
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

    pub(crate) fn bfs_from_mut<'a>(
        &'a mut self,
        x: LambdaExprRef,
    ) -> MutableLambdaPoolBFSIterator<'a, 'src, T> {
        MutableLambdaPoolBFSIterator::new(self, x)
    }

    fn get_next_app(&self, root: LambdaExprRef) -> Option<ApplicationOpportunity> {
        self.bfs_from(root)
            .map(|(x, _)| x)
            .find_map(|r| match self.get(r) {
                LambdaExpr::Lambda(..) if self.is_eta_opportunity(r) => {
                    Some(ApplicationOpportunity::Eta(r))
                }
                LambdaExpr::Application { subformula, .. }
                    if matches!(self.get(*subformula), LambdaExpr::Lambda(..)) =>
                {
                    Some(ApplicationOpportunity::Beta(r))
                }

                _ => None,
            })
    }

    fn is_eta_opportunity(&self, root: LambdaExprRef) -> bool {
        let LambdaExpr::Lambda(body, _) = self.get(root) else {
            return false;
        };
        let LambdaExpr::Application {
            subformula,
            argument,
        } = self.get(*body)
        else {
            return false;
        };
        if !matches!(self.get(*argument), LambdaExpr::BoundVariable(0, _)) {
            return false;
        };

        let uses_variable_in_body = self
            .bfs_from(*subformula)
            .any(|(x, d)| matches!(self.get(x), LambdaExpr::BoundVariable(v, _) if *v==d ));
        !uses_variable_in_body
    }
}

enum ApplicationOpportunity {
    Beta(LambdaExprRef),
    Eta(LambdaExprRef),
}

impl<'src, T: LambdaLanguageOfThought> LambdaPool<'src, T>
where
    T: Clone,
{
    fn bind_free_variable(
        &mut self,
        root: LambdaExprRef,
        fvar: FreeVar<'src>,
        replacement_root: LambdaExprRef,
    ) -> Result<(), LambdaError> {
        let arg_t = self.get_type(replacement_root)?;

        let to_replace = self
            .bfs_from(root)
            .filter_map(|(x, d)| match self.get(x) {
                LambdaExpr::FreeVariable(var, t) if *var == fvar => {
                    if t == &arg_t {
                        Some(Ok((x, d)))
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

    fn replace_section(&mut self, to_replace: &[(LambdaExprRef, usize)], to_copy: LambdaExprRef) {
        let n = to_replace.len();
        for (i, (x, depth)) in to_replace.iter().enumerate() {
            if i == n - 1 {
                for (x, d, _) in self.bfs_from_mut(to_copy) {
                    if let LambdaExpr::BoundVariable(bound_depth, _) = x
                        && *bound_depth >= d
                    {
                        *bound_depth += depth;
                    }
                }
                //Last iteration so we don't need to copy anymore.
                *self.get_mut(*x) = self.get(to_copy).clone();
            } else {
                let mut len = u32::try_from(self.0.len()).unwrap();
                let mut first = true;
                let mut head = None;
                self.0.extend(
                    self.bfs_from(to_copy)
                        .filter_map(|(x, d)| {
                            let mut expr = self.get(x).clone();
                            if let LambdaExpr::BoundVariable(bound_depth, _) = &mut expr
                                && *bound_depth >= d
                            {
                                *bound_depth += depth;
                            }

                            let old_len = len;
                            len += u32::try_from(expr.n_children()).unwrap();
                            expr.change_children((old_len..len).map(LambdaExprRef));
                            if first {
                                head = Some(expr);
                                first = false;
                                None
                            } else {
                                Some(expr)
                            }
                        })
                        .collect::<Vec<_>>(),
                );

                *self.get_mut(*x) = head.unwrap();
            }
        }
    }

    fn eta_reduce(&mut self, lambda: LambdaExprRef) -> Result<(), ReductionError> {
        //BFS over all children and then replace debruijn k w/ argument ref where k is the number
        //of lambda abstractions we've gone under, e.g. (lambda 0 lambda 0 1)(u) -> lambda u lambda
        //1
        //
        //swap position of lambda ref and subformula ref so the lambda now leads to this.
        //
        let Some(expr) = self.checked_get(lambda) else {
            return Err(ReductionError::NotValidRef(lambda));
        };
        let LambdaExpr::Lambda(body, _) = expr else {
            return Err(ReductionError::NoEtaReduction(lambda));
        };
        let LambdaExpr::Application {
            subformula,
            argument,
        } = *self.get(*body)
        else {
            return Err(ReductionError::NoEtaReduction(lambda));
        };

        if !matches!(self.get(argument), LambdaExpr::BoundVariable(0, _)) {
            return Err(ReductionError::NoEtaReduction(lambda));
        }

        for (x, d) in self.bfs_from_mut(subformula).filter_map(|(x, d, _)| {
            if let LambdaExpr::BoundVariable(bvar, _) = x {
                Some((bvar, d))
            } else {
                None
            }
        }) {
            if *x == d {
                return Err(ReductionError::NoEtaReduction(lambda));
            }
            *x -= 1;
        }

        *self.get_mut(lambda) = self.get(subformula).clone();

        Ok(())
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
                self.bfs_from_mut(inner_term)
                    .filter_map(|(expr, d, expr_ref)| {
                        if let LambdaExpr::BoundVariable(b_d, _) = expr {
                            match (*b_d).cmp(&d) {
                                std::cmp::Ordering::Greater => {
                                    //Decrement locally free variables
                                    *b_d -= 1;
                                    None
                                }
                                std::cmp::Ordering::Equal => Some((expr_ref, *b_d)),
                                std::cmp::Ordering::Less => None,
                            }
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>(),
            )
        } else {
            return Err(ReductionError::NotApplication(app));
        };

        //We used to swap this, but that will cause an insanely arcane bug.
        //This is because the same term may be referred to by multiple instructions so if you swap
        //them, it gets invalidated.
        self.replace_section(&subformula_vars, argument);
        self.0[app.0 as usize] = self.0[inner_term.0 as usize].clone();
        //self.0.swap(inner_term.0 as usize, app.0 as usize); <- BAD

        Ok(())
    }

    ///Iterates through a pool and de-allocates dangling refs and updates `LambdaExprRefs` to new
    ///addresses. Basically garbage collection.
    pub(crate) fn cleanup(&mut self, root: LambdaExprRef) -> LambdaExprRef {
        let findable: HashSet<_> = self.bfs_from(root).map(|(x, _)| x.0).collect();
        let mut remap = (0..u32::try_from(self.0.len()).unwrap()).collect::<Vec<_>>();
        let mut adjustment = 0;

        for i in &mut remap {
            if findable.contains(i) {
                *i -= adjustment;
            } else {
                adjustment += 1;
            }
        }

        let mut i = 0;
        self.0.retain(|_| {
            i += 1;
            findable.contains(&(i - 1))
        });
        for x in &mut self.0 {
            x.remap_refs(&remap);
        }
        LambdaExprRef(remap[root.0 as usize])
    }

    pub fn reduce(&mut self, root: LambdaExprRef) -> Result<(), ReductionError> {
        while let Some(x) = self.get_next_app(root) {
            match x {
                ApplicationOpportunity::Beta(x) => self.beta_reduce(x)?,
                ApplicationOpportunity::Eta(x) => self.eta_reduce(x)?,
            }
        }
        Ok(())
    }
}

impl<T: LambdaLanguageOfThought> LambdaExpr<'_, T> {
    pub(crate) fn change_children(&mut self, mut children: impl Iterator<Item = LambdaExprRef>) {
        match self {
            LambdaExpr::Lambda(lambda_expr_ref, _) => *lambda_expr_ref = children.next().unwrap(),
            LambdaExpr::BoundVariable(..)
            | LambdaExpr::FreeVariable(..)
            | LambdaExpr::LanguageOfThoughtExpr(_, ExprType::NoVar) => (),
            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                *subformula = children.next().unwrap();
                *argument = children.next().unwrap();
            }
            LambdaExpr::LanguageOfThoughtExpr(_, ExprType::BindVar(x)) => {
                *x = children.next().unwrap();
            }
            LambdaExpr::LanguageOfThoughtExpr(_, ExprType::BindVarTwoBodies(x, y)) => {
                *x = children.next().unwrap();
                *y = children.next().unwrap();
            }
        }
    }

    fn remap_refs(&mut self, remap: &[u32]) {
        match self {
            LambdaExpr::Lambda(x, _) => {
                *x = LambdaExprRef(remap[x.0 as usize]);
            }
            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                *subformula = LambdaExprRef(remap[subformula.0 as usize]);
                *argument = LambdaExprRef(remap[argument.0 as usize]);
            }
            LambdaExpr::BoundVariable(..)
            | LambdaExpr::FreeVariable(..)
            | LambdaExpr::LanguageOfThoughtExpr(_, ExprType::NoVar) => (),
            LambdaExpr::LanguageOfThoughtExpr(_, ExprType::BindVar(x)) => {
                *x = LambdaExprRef(remap[x.0 as usize]);
            }
            LambdaExpr::LanguageOfThoughtExpr(_, ExprType::BindVarTwoBodies(x, y)) => {
                *x = LambdaExprRef(remap[x.0 as usize]);
                *y = LambdaExprRef(remap[y.0 as usize]);
            }
        }
    }
}

///Details about a [`RootedLambdaPool`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LambdaSummaryStats {
    ///The expression is correctly formed.
    WellFormed {
        ///What type is it
        lambda_type: LambdaType,

        ///Is it a constant function?
        constant_function: bool,

        ///How long is the expression?
        n_nodes: usize,
    },

    ///Is there a problem with the expression
    Malformed,
}

impl<T: LambdaLanguageOfThought + Clone + std::fmt::Debug> RootedLambdaPool<'_, T> {
    ///Convert an expression `phi` of type `x` and convert it to `lambda <x,t> P P(phi)`
    ///
    ///# Errors
    ///Will return a type error if the type of the lambda expression is malformed
    pub fn lift(&mut self) -> Result<(), TypeError> {
        let t =
            LambdaType::Composition(Box::new(self.get_type()?.clone()), Box::new(LambdaType::T));

        let p = self.pool.add(LambdaExpr::BoundVariable(0, t.clone()));
        let apply = self.pool.add(LambdaExpr::Application {
            subformula: p,
            argument: self.root,
        });
        let lambda = self.pool.add(LambdaExpr::Lambda(apply, t));
        self.root = lambda;

        Ok(())
    }

    ///Get [`LambdaSummaryStats`] for an expression, e.g. how many context functions, size, etc.
    #[must_use]
    #[allow(clippy::missing_panics_doc)]
    pub fn stats(&self) -> LambdaSummaryStats {
        let lambda_type = self.get_type();
        if lambda_type.is_err() {
            return LambdaSummaryStats::Malformed;
        }
        let lambda_type = lambda_type.unwrap();
        let n_nodes = self.pool.0.len();

        match self.all_lambda_has_variable(self.root) {
            Ok(has_variable) => LambdaSummaryStats::WellFormed {
                lambda_type,
                constant_function: !has_variable,
                n_nodes,
            },

            Err(_) => LambdaSummaryStats::Malformed,
        }
    }

    fn all_lambda_has_variable(&self, i: LambdaExprRef) -> Result<bool, LambdaError> {
        let mut found = vec![];
        let mut stack = vec![(i, vec![])];
        while let Some((expr_ref, mut lambdas)) = stack.pop() {
            match self.get(expr_ref) {
                LambdaExpr::Lambda(x, _)
                | LambdaExpr::LanguageOfThoughtExpr(_, ExprType::BindVar(x)) => {
                    found.push(false);
                    lambdas.push(found.len() - 1);
                    stack.push((*x, lambdas));
                }
                LambdaExpr::LanguageOfThoughtExpr(_, ExprType::BindVarTwoBodies(x, y)) => {
                    found.push(false);
                    lambdas.push(found.len() - 1);
                    stack.push((*x, lambdas.clone()));
                    stack.push((*y, lambdas));
                }
                LambdaExpr::BoundVariable(d, _) => {
                    if let Some(index) = lambdas.len().checked_sub(d + 1) {
                        if let Some(found_index) = lambdas.get(index) {
                            if let Some(found) = found.get_mut(*found_index) {
                                *found = true;
                            } else {
                                return Err(LambdaError::BadBoundVariable {
                                    var: expr_ref,
                                    depth: lambdas.len(),
                                });
                            }
                        } else {
                            return Err(LambdaError::BadBoundVariable {
                                var: expr_ref,
                                depth: lambdas.len(),
                            });
                        }
                    } else {
                        return Err(LambdaError::BadBoundVariable {
                            var: expr_ref,
                            depth: lambdas.len(),
                        });
                    }
                }
                LambdaExpr::FreeVariable(..)
                | LambdaExpr::LanguageOfThoughtExpr(_, ExprType::NoVar) => (),
                LambdaExpr::Application {
                    subformula,
                    argument,
                } => {
                    stack.push((*subformula, lambdas.clone()));
                    stack.push((*argument, lambdas));
                }
            }
        }

        Ok(found.iter().all(|x| *x))
    }
}

impl<'a, T: LambdaLanguageOfThought> From<LambdaPool<'a, T>> for Vec<Option<LambdaExpr<'a, T>>> {
    fn from(value: LambdaPool<'a, T>) -> Self {
        value.0.into_iter().map(Some).collect()
    }
}

impl<'a, T: LambdaLanguageOfThought> TryFrom<Vec<Option<LambdaExpr<'a, T>>>> for LambdaPool<'a, T> {
    type Error = LambdaTryFromError;

    fn try_from(value: Vec<Option<LambdaExpr<'a, T>>>) -> Result<Self, Self::Error> {
        match value.into_iter().collect::<Option<Vec<_>>>() {
            Some(x) => Ok(LambdaPool(x)),
            None => Err(LambdaTryFromError::HasNone),
        }
    }
}

#[cfg(test)]
mod test {

    use std::{
        collections::BTreeSet,
        hash::{DefaultHasher, Hasher},
    };

    use super::*;
    use crate::language::Expr;

    #[test]
    fn ordering() -> anyhow::Result<()> {
        let x = [
            "a_0",
            "lambda a x (pa_man(x))",
            "lambda a x (pa_man(a_m))",
            "lambda a x (((lambda a y (pa_woman(y)))(a_m)) & pa_man(x))",
            "lambda a x (((lambda a y (pa_woman(a_m)))(a_m)) & pa_man(x))",
            "lambda a y (pa_woman(a_m))",
            "lambda a y (lambda a x (y))",
            "some(x, pa_man(x), True)",
            "some(x, pa_man(x), pa_man(x))",
            "some(x, True, pa_man(x))",
            "some(x, True, True)",
        ];

        let set: BTreeSet<_> = x
            .into_iter()
            .map(RootedLambdaPool::<Expr>::parse)
            .collect::<Result<_, _>>()?;

        assert_eq!(set.len(), 11);
        let order: Vec<_> = set.into_iter().map(|x| x.to_string()).collect();

        let sorted = vec![
            "a_0",
            "lambda a x lambda a y x",
            "lambda a x pa_man(x)",
            "lambda a x pa_man(a_m)",
            "lambda a x pa_woman(a_m)",
            "some(x, True, True)",
            "some(x, True, pa_man(x))",
            "some(x, pa_man(x), True)",
            "some(x, pa_man(x), pa_man(x))",
            "lambda a x (lambda a y pa_woman(y))(a_m) & pa_man(x)",
            "lambda a x (lambda a y pa_woman(a_m))(a_m) & pa_man(x)",
        ];

        for (x, y) in order.into_iter().zip(sorted) {
            assert_eq!(x, y);
        }

        Ok(())
    }

    #[test]
    fn stats() -> anyhow::Result<()> {
        for (expr, constant_lambda) in [
            ("a_0", false),
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
            ("some(x, pa_man(x), True)", false),
            ("some(x, pa_man(x), pa_man(x))", false),
            ("some(x, True, pa_man(x))", false),
            ("some(x, True, True)", true),
        ] {
            let expr = RootedLambdaPool::<Expr>::parse(expr)?;
            match expr.stats() {
                LambdaSummaryStats::WellFormed {
                    constant_function, ..
                } => assert_eq!(constant_function, constant_lambda),
                LambdaSummaryStats::Malformed => panic!("{expr} should be well-formed!"),
            }
        }
        Ok(())
    }

    fn k<'a, T: Default>(pos: u32) -> anyhow::Result<[LambdaExpr<'a, T>; 3]> {
        Ok([
            LambdaExpr::Lambda(LambdaExprRef(pos + 1), LambdaType::e().clone()),
            LambdaExpr::Lambda(LambdaExprRef(pos + 2), LambdaType::e().clone()),
            LambdaExpr::BoundVariable(1, LambdaType::e().clone()),
        ])
    }

    /*
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
                MonOp::Property("32", ActorOrEvent::Actor),
                LambdaExprRef(3),
            )),
            LambdaExpr::BoundVariable(0, LambdaType::a().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Actor("3")),
        ]);
        pool.reduce(LambdaExprRef(0))?;
        pool.cleanup(LambdaExprRef(0));

        assert_eq!(
            pool.clone(),
            LambdaPool(vec![
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                    MonOp::Property("32", ActorOrEvent::Actor),
                    LambdaExprRef(1)
                )),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Actor("3"))
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
            LambdaExpr::LanguageOfThoughtExpr(Expr::Actor("2")),
            LambdaExpr::Lambda(LambdaExprRef(6), LambdaType::a().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                MonOp::Property("36", ActorOrEvent::Actor),
                LambdaExprRef(7),
            )),
            LambdaExpr::BoundVariable(0, LambdaType::a().clone()),
        ]);
        pool.reduce(LambdaExprRef(0))?;
        pool.cleanup(LambdaExprRef(0));
        assert_eq!(
            pool,
            LambdaPool(vec![
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                    MonOp::Property("36", ActorOrEvent::Actor),
                    LambdaExprRef(1)
                )),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Actor("2")),
            ])
        );

        let mut pool = LambdaPool(vec![
            LambdaExpr::Application {
                subformula: LambdaExprRef(1),
                argument: LambdaExprRef(6),
            },
            LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::t().clone()),
            LambdaExpr::Lambda(LambdaExprRef(3), LambdaType::t().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(
                BinOp::And,
                LambdaExprRef(4),
                LambdaExprRef(5),
            )), //10
            LambdaExpr::BoundVariable(1, LambdaType::t().clone()),
            LambdaExpr::BoundVariable(0, LambdaType::t().clone()),
            LambdaExpr::Application {
                //6
                subformula: LambdaExprRef(7),
                argument: LambdaExprRef(10),
            },
            LambdaExpr::Lambda(LambdaExprRef(8), LambdaType::a().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                MonOp::Property("36", ActorOrEvent::Actor),
                LambdaExprRef(9),
            )),
            LambdaExpr::BoundVariable(0, LambdaType::a().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Actor("2")),
        ]);
        pool.reduce(LambdaExprRef(0))?;
        pool.cleanup(LambdaExprRef(0));

        assert_eq!(
            pool,
            LambdaPool(vec![
                LambdaExpr::Lambda(LambdaExprRef(1), LambdaType::t().clone()),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(
                    BinOp::And,
                    LambdaExprRef(2),
                    LambdaExprRef(3)
                )),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                    MonOp::Property("36", ActorOrEvent::Actor),
                    LambdaExprRef(4)
                )),
                LambdaExpr::BoundVariable(0, LambdaType::t().clone()),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Actor("2")),
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
                MonOp::Property("32", ActorOrEvent::Actor),
                LambdaExprRef(4),
            )),
            LambdaExpr::BoundVariable(0, LambdaType::a().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Actor("3")),
            // 6
            //\lambda x. Mary sings and
            LambdaExpr::Application {
                subformula: LambdaExprRef(7),
                argument: LambdaExprRef(12),
            },
            LambdaExpr::Lambda(LambdaExprRef(8), LambdaType::t().clone()),
            LambdaExpr::Lambda(LambdaExprRef(9), LambdaType::t().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(
                BinOp::And,
                LambdaExprRef(10),
                LambdaExprRef(11),
            )), //10
            LambdaExpr::BoundVariable(1, LambdaType::t().clone()),
            LambdaExpr::BoundVariable(0, LambdaType::t().clone()),
            LambdaExpr::Application {
                //13
                subformula: LambdaExprRef(13),
                argument: LambdaExprRef(16),
            },
            LambdaExpr::Lambda(LambdaExprRef(14), LambdaType::a().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                MonOp::Property("36", ActorOrEvent::Actor),
                LambdaExprRef(15),
            )),
            LambdaExpr::BoundVariable(0, LambdaType::a().clone()),
            LambdaExpr::LanguageOfThoughtExpr(Expr::Actor("2")),
        ]);
        pool.reduce(LambdaExprRef(0))?;
        let root = pool.cleanup(LambdaExprRef(0));
        assert_eq!(
            pool,
            LambdaPool(vec![
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(
                    BinOp::And,
                    LambdaExprRef(2),
                    LambdaExprRef(3)
                )),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Actor("3")),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                    MonOp::Property("36", ActorOrEvent::Actor),
                    LambdaExprRef(4)
                )),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                    MonOp::Property("32", ActorOrEvent::Actor),
                    LambdaExprRef(1)
                )),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Actor("2"))
            ])
        );

        assert_eq!(
            RootedLambdaPool::new(pool, root).into_pool()?,
            LanguageExpression::new(
                ExprPool::from(vec![
                    Expr::Binary(BinOp::And, LambdaExprRef(2), LambdaExprRef(3)),
                    Expr::Actor("3"),
                    Expr::Unary(MonOp::Property("36", ActorOrEvent::Actor), LambdaExprRef(4)),
                    Expr::Unary(MonOp::Property("32", ActorOrEvent::Actor), LambdaExprRef(1)),
                    Expr::Actor("2")
                ]),
                LambdaExprRef(root.0)
            )
        );
        Ok(())
    }*/

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
            LambdaExpr::FreeVariable("0".into(), LambdaType::t().clone()),
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
            LambdaExpr::FreeVariable("0".into(), LambdaType::a().clone()),
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
            LambdaExpr::FreeVariable("0".into(), LambdaType::t().clone()),
            LambdaExpr::FreeVariable("2".into(), LambdaType::t().clone()),
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
            LambdaExpr::FreeVariable("1337".into(), LambdaType::t().clone()),
            LambdaExpr::FreeVariable("5".into(), LambdaType::e().clone()),
        ]);
        pool.reduce(LambdaExprRef(0))?;
        pool.cleanup(LambdaExprRef(0));
        assert_eq!(
            pool,
            LambdaPool(vec![LambdaExpr::FreeVariable(
                "1337".into(),
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
                    LambdaExpr::FreeVariable("32".into(), LambdaType::e().clone()),
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
                LambdaExpr::FreeVariable("32".into(), LambdaType::e().clone()),
                LambdaExpr::Lambda(LambdaExprRef(0), LambdaType::e().clone())
            ])
        );
        Ok(())
    }

    #[test]
    fn test_root_and_merger() -> anyhow::Result<()> {
        let man = RootedLambdaPool::<Expr>::parse("lambda a x (pa_man(x))")?;

        let sleeps = RootedLambdaPool::<Expr>::parse(
            "lambda a x (some_e(y, all_e(y), AgentOf(x, y) & pe_sleep(y)))",
        )?;
        let every = RootedLambdaPool::<Expr>::parse(
            "lambda <a,t> p (lambda <a,t> q every(x, p(x), q(x)))",
        )?;

        let phi = every.clone().merge(man.clone()).unwrap();
        let mut phi = phi.merge(sleeps.clone()).unwrap();
        println!("{phi}");
        phi.reduce()?;
        println!("{phi}");
        assert_eq!(
            phi,
            RootedLambdaPool::<Expr>::parse(
                "every(x, pa_man(x), some_e(y, all_e(y), AgentOf(x, y) & pe_sleep(y)))",
            )?
        );
        assert!(check_hashes(
            &phi,
            &RootedLambdaPool::<Expr>::parse(
                "every(x, pa_man(x), some_e(y, all_e(y), AgentOf(x, y) & pe_sleep(y)))",
            )?,
        ));
        assert_eq!(
            "every(x, pa_man(x), some_e(y, all_e(y), AgentOf(x, y) & pe_sleep(y)))",
            phi.to_string()
        );
        let phi = man.merge(every).unwrap();
        let mut phi = sleeps.merge(phi).unwrap();
        phi.reduce()?;
        assert_eq!(
            phi,
            RootedLambdaPool::<Expr>::parse(
                "every(x, pa_man(x), some_e(y, all_e(y), AgentOf(x, y) & pe_sleep(y)))",
            )?
        );

        assert!(check_hashes(
            &phi,
            &RootedLambdaPool::<Expr>::parse(
                "every(x, pa_man(x), some_e(y, all_e(y), AgentOf(x, y) & pe_sleep(y)))",
            )?,
        ));

        assert_eq!(
            "every(x, pa_man(x), some_e(y, all_e(y), AgentOf(x, y) & pe_sleep(y)))",
            phi.to_string()
        );
        Ok(())
    }

    fn check_hashes<'src>(
        phi: &RootedLambdaPool<'src, Expr<'src>>,
        psi: &RootedLambdaPool<'src, Expr<'src>>,
    ) -> bool {
        let mut hasher1 = DefaultHasher::new();
        let mut hasher2 = DefaultHasher::new();

        phi.hash(&mut hasher1);
        psi.hash(&mut hasher2);

        hasher1.finish() == hasher2.finish()
    }

    #[test]
    fn bind_free_variable() -> anyhow::Result<()> {
        let mut pool = RootedLambdaPool::<Expr>::parse("phi#t & True")?;

        pool.bind_free_variable("phi".into(), RootedLambdaPool::<Expr>::parse("False")?)?;
        assert_eq!("False & True", pool.to_string());

        let input = RootedLambdaPool::<Expr>::parse("lambda a x every_e(y,pe_4(y),AgentOf(x,y))")?;
        let mut a = RootedLambdaPool::<Expr>::parse("(P#<a,t>(a_3) & ~P#<a,t>(a_1))")?;

        a.bind_free_variable("P".into(), input)?;
        a.reduce()?;
        assert_eq!(
            a.to_string(),
            "every_e(x, pe_4(x), AgentOf(a_3, x)) & ~every_e(x, pe_4(x), AgentOf(a_1, x))"
        );
        Ok(())
    }

    #[test]
    fn apply_new_free_variable() -> anyhow::Result<()> {
        let mut pool = RootedLambdaPool::<Expr>::parse(
            "lambda <e,t> P (lambda <e,t> Q (lambda e x (P(x) & Q(x))))",
        )?;

        pool.apply_new_free_variable("X".into())?;

        println!("{pool}");
        assert_eq!(
            pool,
            RootedLambdaPool::parse("lambda <e,t> Q (lambda e x (X#<e,t>(x) & Q(x)))",)?
        );
        Ok(())
    }

    #[test]
    fn lambda_abstraction() -> anyhow::Result<()> {
        let mut pool = RootedLambdaPool::<Expr>::parse(
            "lambda <e,t> P lambda <e,t> Q lambda e x Z#<e,t>(x) & P(x) & Q(x)",
        )?;

        pool.lambda_abstract_free_variable("Z".into(), LambdaType::et().clone(), false)?;
        assert_eq!(
            pool,
            RootedLambdaPool::parse(
                "lambda <e,t> P lambda <e,t> Q lambda <e,t> R lambda e x P(x) & Q(x) & R(x)",
            )?
        );
        Ok(())
    }

    #[test]
    fn could_time_out_if_swapping_instead_of_cloning() -> anyhow::Result<()> {
        let mut x = RootedLambdaPool::<Expr>::parse(
            "(lambda a x (PatientOf(x,e_0) & AgentOf(x, e_0)))((lambda a x (a_1))(a_0))",
        )?;

        println!("{x}");
        x.reduce()?;
        println!("{x}");
        Ok(())
    }

    #[test]
    fn lambda_abstraction_reduction() -> anyhow::Result<()> {
        let mut a = RootedLambdaPool::<Expr>::parse("a_1")?;
        let mut b = RootedLambdaPool::<Expr>::parse("(lambda t x (a_1))(pa_0(freeVar#a))")?;

        a.lambda_abstract_free_variable("freeVar".into(), LambdaType::a().clone(), false)?;
        b.lambda_abstract_free_variable("freeVar".into(), LambdaType::a().clone(), false)?;
        println!("A:\t{a}");
        println!("B:\t{b}");

        a.cleanup();
        b.cleanup();
        assert_eq!(a, b);
        Ok(())
    }

    #[test]
    fn reduction_test() -> anyhow::Result<()> {
        let mut a = RootedLambdaPool::<Expr>::parse(
            "lambda a x (every_e(z, all_e(z), AgentOf(a_0, (lambda e y ((lambda e w (w))(y)))(z))))",
        )?;
        a.reduce()?;

        let mut a = RootedLambdaPool::<Expr>::parse(
            "(lambda <a,t> P (P(a_3) & ~P(a_1)))(lambda a x (every_e(y,pe_4(y),AgentOf(x,y))))",
        )?;

        a.pool.beta_reduce(a.root)?;
        a.root = a.pool.cleanup(a.root);
        println!("{a}");
        dbg!(&a);

        let mut a = RootedLambdaPool::<Expr>::parse(
            "(lambda <a,t> P (P(a_3) & ~P(a_1)))(lambda a x (every_e(y,pe_4(y),AgentOf(x,y))))",
        )?;

        a.reduce()?;
        assert_eq!(
            a.to_string(),
            "every_e(x, pe_4(x), AgentOf(a_3, x)) & ~every_e(x, pe_4(x), AgentOf(a_1, x))"
        );

        Ok(())
    }

    #[test]
    fn lift() -> anyhow::Result<()> {
        let mut e = RootedLambdaPool::<Expr>::parse("a_john")?;
        e.lift()?;
        assert_eq!(e.to_string(), "lambda <a,t> P P(a_john)");

        Ok(())
    }

    #[test]
    fn lambda_abstractions() -> anyhow::Result<()> {
        let mut e = RootedLambdaPool::<Expr>::parse(
            "(lambda t phi phi)(some_e(x, all_e(x), AgentOf(a_m, x) & PatientOf(blarg#a, x) & pe_likes(x)))",
        )?;
        e.reduce()?;
        e.lambda_abstract_free_variable(FreeVar::Named("blarg"), LambdaType::A, false)
            .unwrap();
        assert_eq!(
            e.to_string(),
            "lambda a x some_e(y, all_e(y), AgentOf(a_m, y) & PatientOf(x, y) & pe_likes(y))"
        );
        Ok(())
    }

    #[test]
    fn is_constant_function() -> anyhow::Result<()> {
        let constants = [
            "lambda a x a_John",
            "lambda a x lambda a y pa_man(x)",
            "lambda a x some_e(y, all_e(y), pe_runs(y))",
        ];
        for s in constants {
            println!("{s}");
            let LambdaSummaryStats::WellFormed {
                lambda_type: _,
                constant_function,
                n_nodes: _,
            } = RootedLambdaPool::<Expr>::parse(s)?.stats()
            else {
                panic!("{s} is poorly formed")
            };
            assert!(constant_function);
        }

        let not_constants = [
            "lambda a x x",
            "lambda a x lambda a y pa_man(x) & pa_woman(y)",
        ];
        for s in not_constants {
            println!("{s}");
            let LambdaSummaryStats::WellFormed {
                lambda_type: _,
                constant_function,
                n_nodes: _,
            } = RootedLambdaPool::<Expr>::parse(s)?.stats()
            else {
                panic!("{s} is poorly formed")
            };
            assert!(!constant_function);
        }
        Ok(())
    }

    #[test]
    fn reduce_with_expressions() -> anyhow::Result<()> {
        let expressions = [
            ("lambda a x pa_kind(x)", "pa_kind"),
            ("lambda a x kind#<a,t>(x)", "kind#<a,t>"),
            (
                "(lambda <<a,t>,<<a,t>,t>> R lambda <a,t> P lambda <a,t> Q R(P, Q))(every)",
                "every",
            ),
        ];
        for (expresssion, reduced) in expressions {
            let mut phi = RootedLambdaPool::<Expr>::parse(expresssion)?;
            phi.reduce()?;
            let reduced = RootedLambdaPool::<Expr>::parse(reduced)?;
            assert_eq!(phi, reduced, "{phi} != {reduced}");
        }
        Ok(())
    }
}
