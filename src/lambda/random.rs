//! Randomly generates lambda expressions of a language of thought.
//!
//!Unlike [`crate::lambda::enumerator`], which enumerates *all* expressions up to a size, this
//!module randomly descends through the space of well-typed, beta-eta normal expressions and
//!generates a single one. Applications are "free" w.r.t. size (see
//![`RootedLambdaPool::appless_len`]), so the generator uses head applications to go deeper
//!without spending size.

use rand::{
    Rng,
    seq::{IndexedRandom, SliceRandom},
};
use thiserror::Error;

use crate::lambda::{
    ExprType, FreeVar, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool,
    RootedLambdaPool, types::LambdaType,
};

///Errors resulting from randomly generating a lambda expression.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum RandomError {
    ///No expression of the target type can be constructed from the given base expressions.
    #[error("No expression of type {typ} can be generated from the given base expressions")]
    NotConstructible {
        ///The type which could not be constructed.
        typ: LambdaType,
    },
    ///No expression of the target type of the given size can be constructed from the given base
    ///expressions.
    #[error(
        "No expression of type {typ} of size {size} can be generated from the given base expressions"
    )]
    SizeNotConstructible {
        ///The type which could not be constructed.
        typ: LambdaType,
        ///The size which could not be constructed.
        size: usize,
    },
    ///No base expressions or free variables were given to generate from.
    #[error("No base expressions or free variables to generate expressions from")]
    NoBaseExpressions,
}

///How many node attempts a single generation may make before giving up. This bounds the
///backtracking search so pathological base expressions cannot hang generation.
const BUDGET: usize = 10_000;

///A candidate way to spend the remaining size at a node.
enum Choice<'src, T> {
    Lambda {
        arg: LambdaType,
        res: LambdaType,
    },
    Application {
        head: LambdaExpr<'src, T>,
        args: Vec<LambdaType>,
    },
}

///The state of a single random descent.
struct RandomExprBuilder<'src, 'a, T> {
    pool: Vec<LambdaExpr<'src, T>>,
    ///The types of the bound variables in scope, indexed by De Bruijn index.
    context: Vec<LambdaType>,
    ///The usable base expressions and free variables, with their types.
    leaves: &'a [(LambdaExpr<'src, T>, LambdaType)],
    budget: usize,
}

impl<'src, T: LambdaLanguageOfThought + Clone + PartialEq> RandomExprBuilder<'src, '_, T> {
    ///Randomly generates an expression of exactly `size` (in the [`RootedLambdaPool::appless_len`]
    ///sense) of type `target`, backtracking when a descent dead-ends.
    fn generate(
        &mut self,
        rng: &mut impl Rng,
        target: &LambdaType,
        size: usize,
    ) -> Result<LambdaExprRef, ()> {
        if size == 0 || self.budget == 0 {
            return Err(());
        }
        self.budget -= 1;

        let bound_vars = self.bound_vars_of_type(target);

        if size == 1 {
            let mut candidates: Vec<LambdaExpr<'src, T>> = self
                .leaves
                .iter()
                .filter(|(_, typ)| typ == target)
                .map(|(x, _)| x.clone())
                .collect();
            candidates.extend(bound_vars);

            let Some(x) = candidates.choose(rng) else {
                return Err(());
            };
            let r = self.push(x.clone());
            return Ok(r);
        }

        let mut choices: Vec<Choice<'src, T>> = vec![];
        if let Ok((arg, res)) = target.split() {
            choices.push(Choice::Lambda {
                arg: arg.clone(),
                res: res.clone(),
            });
        }

        let mut heads: Vec<(LambdaExpr<'src, T>, LambdaType)> = self.leaves.to_vec();
        heads.extend(self.all_bound_vars());
        for (head, typ) in heads {
            for args in arg_chains(&typ, target) {
                if args.len() < size {
                    choices.push(Choice::Application {
                        head: head.clone(),
                        args,
                    });
                }
            }
        }

        choices.shuffle(rng);
        for choice in choices {
            let mark = self.pool.len();
            if let Some(r) = self.try_choice(rng, choice, size) {
                return Ok(r);
            }
            self.pool.truncate(mark);
        }

        Err(())
    }

    ///Attempts a single choice, returning [`None`] (leaving the builder in a rolled-back state)
    ///if it dead-ends.
    fn try_choice(
        &mut self,
        rng: &mut impl Rng,
        choice: Choice<'src, T>,
        size: usize,
    ) -> Option<LambdaExprRef> {
        match choice {
            Choice::Lambda { arg, res } => {
                self.context.insert(0, arg.clone());
                let body = self.generate(rng, &res, size - 1);
                self.context.remove(0);
                let body = body.ok()?;

                //The bound variable must be used and the body must not be an eta redex.
                if !self.uses_bvar(body, 0) || self.is_eta_redex(body) {
                    return None;
                }

                Some(self.push(LambdaExpr::Lambda(body, arg)))
            }
            Choice::Application { head, args } => {
                if args.len() > size - 1 {
                    return None;
                }

                let head_ref = self.push(head);
                let mut splits = compositions(size - 1, args.len());
                splits.shuffle(rng);

                for sizes in splits {
                    let mark = self.pool.len();
                    let mut cur = head_ref;
                    let mut ok = true;

                    for (typ, s) in args.iter().zip(sizes) {
                        let Some(argument) = self.generate(rng, typ, s).ok() else {
                            ok = false;
                            break;
                        };
                        if self.is_involutory(cur, argument) {
                            ok = false;
                            break;
                        }
                        cur = self.push(LambdaExpr::Application {
                            subformula: cur,
                            argument,
                        });
                    }

                    if ok {
                        return Some(cur);
                    }
                    self.pool.truncate(mark);
                }

                None
            }
        }
    }

    fn push(&mut self, expr: LambdaExpr<'src, T>) -> LambdaExprRef {
        self.pool.push(expr);
        LambdaExprRef(u32::try_from(self.pool.len() - 1).unwrap())
    }

    ///The bound variables in scope of type `typ`, as expressions.
    fn bound_vars_of_type(&self, typ: &LambdaType) -> Vec<LambdaExpr<'src, T>> {
        self.context
            .iter()
            .enumerate()
            .filter(|(_, t)| *t == typ)
            .map(|(i, t)| LambdaExpr::BoundVariable(i, t.clone()))
            .collect()
    }

    ///All bound variables in scope, of any type, paired with their types.
    fn all_bound_vars(&self) -> Vec<(LambdaExpr<'src, T>, LambdaType)> {
        self.context
            .iter()
            .enumerate()
            .map(|(i, t)| (LambdaExpr::BoundVariable(i, t.clone()), t.clone()))
            .collect()
    }

    ///Checks if the subtree rooted at `root` uses the bound variable with De Bruijn index `idx`.
    fn uses_bvar(&self, root: LambdaExprRef, idx: usize) -> bool {
        let mut stack = vec![root];
        while let Some(r) = stack.pop() {
            match &self.pool[usize::try_from(r.0).unwrap()] {
                LambdaExpr::BoundVariable(x, _) if *x == idx => return true,
                expr => stack.extend(expr.get_children()),
            }
        }
        false
    }

    ///Checks if `body` (a lambda's body) is the site of an eta reduction, i.e. it is an
    /// application of a subformula that doesn't use the bound variable to that variable.
    fn is_eta_redex(&self, body: LambdaExprRef) -> bool {
        let LambdaExpr::Application {
            subformula,
            argument,
        } = &self.pool[usize::try_from(body.0).unwrap()]
        else {
            return false;
        };

        matches!(
            self.pool[usize::try_from(argument.0).unwrap()],
            LambdaExpr::BoundVariable(0, _)
        ) && !self.uses_bvar(*subformula, 0)
    }

    ///Checks if `f` is an involutory expression applied to an application of itself, e.g.
    ///`!(!p)`, which can be simplified.
    fn is_involutory(&self, f: LambdaExprRef, x: LambdaExprRef) -> bool {
        let LambdaExpr::LanguageOfThoughtExpr(outer, _) = &self.pool[usize::try_from(f.0).unwrap()]
        else {
            return false;
        };

        if !outer.involutory() {
            return false;
        }

        let LambdaExpr::Application { subformula, .. } = &self.pool[usize::try_from(x.0).unwrap()]
        else {
            return false;
        };

        matches!(
            &self.pool[usize::try_from(subformula.0).unwrap()],
            LambdaExpr::LanguageOfThoughtExpr(inner, _) if inner == outer
        )
    }
}

///All the ways `typ` can be applied to arguments to result in `target`. Each element is the list
///of argument types, shortest chain first.
fn arg_chains(typ: &LambdaType, target: &LambdaType) -> Vec<Vec<LambdaType>> {
    let mut chains = vec![];
    let mut args = vec![];
    let mut cur = typ;

    while let Ok((l, r)) = cur.split() {
        args.push(l.clone());
        if r == target {
            chains.push(args.clone());
        }
        cur = r;
    }

    chains
}

///All the ways to split `total` into `parts` sizes, each at least one.
fn compositions(total: usize, parts: usize) -> Vec<Vec<usize>> {
    if parts == 1 {
        return vec![vec![total]];
    }

    let mut result = vec![];
    for first in 1..=total - (parts - 1) {
        for rest in compositions(total - first, parts - 1) {
            let mut sizes = vec![first];
            sizes.extend(rest);
            result.push(sizes);
        }
    }
    result
}

///Picks a random target type if none was given.
fn pick_target(
    rng: &mut impl Rng,
    target: Option<LambdaType>,
    leaves: &[(LambdaExpr<'_, impl LambdaLanguageOfThought>, LambdaType)],
) -> Result<LambdaType, RandomError> {
    target.ok_or(()).or_else(|()| {
        leaves
            .choose(rng)
            .map(|(_, t)| t.clone())
            .ok_or(RandomError::NoBaseExpressions)
    })
}

///Filters out syncategorematic expressions (which bind variables directly and so cannot be used
///by random generation, mirroring the enumerator) and pairs the rest with their types.
fn mk_leaves<'src, T: LambdaLanguageOfThought + Clone>(
    base_expressions: &[T],
    free_var: &[(FreeVar<'src>, LambdaType)],
) -> Vec<(LambdaExpr<'src, T>, LambdaType)> {
    let mut leaves: Vec<(LambdaExpr<'src, T>, LambdaType)> = base_expressions
        .iter()
        .filter(|x| x.bind_vars() == crate::lambda::PrimitiveVarType::NoVar)
        .map(|x| {
            (
                LambdaExpr::LanguageOfThoughtExpr(x.clone(), ExprType::NoVar),
                x.typ().clone(),
            )
        })
        .collect();

    leaves.extend(
        free_var
            .iter()
            .map(|(f, t)| (LambdaExpr::FreeVariable(*f, t.clone()), t.clone())),
    );

    leaves
}

impl<'src, T: LambdaLanguageOfThought + Clone + PartialEq> RootedLambdaPool<'src, T> {
    ///Randomly generates an expression of type `target` with an [`RootedLambdaPool::appless_len`]
    ///of exactly `size`.
    ///
    ///If `target` is [`None`], a type is chosen at random from the types of the base expressions
    ///and free variables. The expression is guaranteed to be fully reduced (see
    ///[`RootedLambdaPool::is_reduced`]).
    ///
    ///# Errors
    ///Returns a [`RandomError`] if no expression of the target type and size can be constructed
    ///from the given base expressions and free variables.
    pub fn random_exact(
        rng: &mut impl Rng,
        target: Option<LambdaType>,
        size: usize,
        base_expressions: &[T],
        free_var: &[(FreeVar<'src>, LambdaType)],
    ) -> Result<Self, RandomError> {
        let leaves = mk_leaves(base_expressions, free_var);
        let typ = pick_target(rng, target, &leaves)?;

        let mut builder = RandomExprBuilder {
            pool: vec![],
            context: vec![],
            leaves: &leaves,
            budget: BUDGET,
        };

        builder
            .generate(rng, &typ, size)
            .map(|root| RootedLambdaPool {
                pool: LambdaPool(builder.pool),
                root,
            })
            .map_err(|()| RandomError::SizeNotConstructible { typ, size })
    }

    ///Randomly generates an expression of type `target` with an [`RootedLambdaPool::appless_len`]
    ///of at most `max_size`, roughly uniformly distributed over the achievable sizes.
    ///
    ///If `target` is [`None`], a type is chosen at random from the types of the base expressions
    ///and free variables. The expression is guaranteed to be fully reduced (see
    ///[`RootedLambdaPool::is_reduced`]).
    ///
    ///# Errors
    ///Returns a [`RandomError`] if no expression of the target type can be constructed from the
    ///given base expressions and free variables.
    pub fn random_up_to(
        rng: &mut impl Rng,
        target: Option<LambdaType>,
        max_size: usize,
        base_expressions: &[T],
        free_var: &[(FreeVar<'src>, LambdaType)],
    ) -> Result<Self, RandomError> {
        let leaves = mk_leaves(base_expressions, free_var);
        let typ = pick_target(rng, target, &leaves)?;

        let mut sizes: Vec<usize> = (1..=max_size).collect();
        sizes.shuffle(rng);

        for size in sizes {
            let mut builder = RandomExprBuilder {
                pool: vec![],
                context: vec![],
                leaves: &leaves,
                budget: BUDGET,
            };

            if let Ok(root) = builder.generate(rng, &typ, size) {
                return Ok(RootedLambdaPool {
                    pool: LambdaPool(builder.pool),
                    root,
                });
            }
        }

        Err(RandomError::NotConstructible { typ })
    }
}

#[cfg(test)]
mod test {
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use crate::{
        lambda::{
            Literal,
            types::LambdaType,
            {FreeVar, RootedLambdaPool},
        },
        language::{
            ActorOrEvent,
            Constant::{self, Property},
            Expr,
        },
    };

    use super::*;

    fn base_expressions() -> Vec<Expr<'static>> {
        let mut expressions = vec![
            Expr::Constant(Constant::Literal(Literal::Actor("John"))),
            Expr::Constant(Property("a", ActorOrEvent::Actor)),
            Expr::Constant(Property("e", ActorOrEvent::Event)),
        ];
        expressions.extend(Expr::basic_ops().iter().cloned());
        expressions
    }

    #[test]
    fn test_random_exact() -> anyhow::Result<()> {
        let mut rng = ChaCha8Rng::seed_from_u64(0);

        //There is no bare `t` constant, so size 1 is not constructible.
        let err = RootedLambdaPool::<Expr<'static>>::random_exact(
            &mut rng,
            Some(LambdaType::T),
            1,
            &base_expressions(),
            &[],
        )
        .unwrap_err();
        assert_eq!(
            err,
            RandomError::SizeNotConstructible {
                typ: LambdaType::T,
                size: 1
            }
        );

        //Size 4 is not constructible either: the only size 3 `t` is `~(pa(John))`, so `~` at size 4
        //would be a repeated involutory application, and `&` needs 1 + 2 + 2 = 5 nodes.
        let err = RootedLambdaPool::<Expr<'static>>::random_exact(
            &mut rng,
            Some(LambdaType::T),
            4,
            &base_expressions(),
            &[],
        )
        .unwrap_err();
        assert_eq!(
            err,
            RandomError::SizeNotConstructible {
                typ: LambdaType::T,
                size: 4
            }
        );

        for _ in 0..200 {
            for size in [2, 3, 5, 6] {
                let expr = RootedLambdaPool::<Expr<'static>>::random_exact(
                    &mut rng,
                    Some(LambdaType::T),
                    size,
                    &base_expressions(),
                    &[],
                )?;
                assert!(expr.is_reduced(), "{expr} is not fully reduced");
                assert_eq!(expr.appless_len(), size);
                assert_eq!(expr.get_type()?, LambdaType::T);
            }
        }

        Ok(())
    }

    #[test]
    fn test_random_up_to() -> anyhow::Result<()> {
        let mut rng = ChaCha8Rng::seed_from_u64(1);

        for _ in 0..200 {
            let expr = RootedLambdaPool::<Expr<'static>>::random_up_to(
                &mut rng,
                None,
                6,
                &base_expressions(),
                &[],
            )?;
            assert!(expr.is_reduced(), "{expr} is not fully reduced");
            assert!(expr.appless_len() <= 6);
            expr.get_type()?;
        }

        Ok(())
    }

    #[test]
    fn test_free_vars() -> anyhow::Result<()> {
        let mut rng = ChaCha8Rng::seed_from_u64(2);
        let free_var = vec![(FreeVar::Named("x"), LambdaType::E)];

        for _ in 0..100 {
            let expr = RootedLambdaPool::<Expr<'static>>::random_up_to(
                &mut rng,
                Some(LambdaType::T),
                5,
                &base_expressions(),
                &free_var,
            )?;
            assert!(expr.is_reduced(), "{expr} is not fully reduced");
            assert_eq!(expr.get_type()?, LambdaType::T);
        }

        Ok(())
    }

    #[test]
    fn test_not_constructible() -> anyhow::Result<()> {
        let mut rng = ChaCha8Rng::seed_from_u64(3);

        //No base expression can produce an `e` (iota is syncategorematic and so unusable).
        let err = RootedLambdaPool::<Expr<'static>>::random_exact(
            &mut rng,
            Some(LambdaType::E),
            3,
            &base_expressions(),
            &[],
        )
        .unwrap_err();

        assert_eq!(
            err,
            RandomError::SizeNotConstructible {
                typ: LambdaType::E,
                size: 3
            }
        );

        //Nothing to generate from at all.
        let err = RootedLambdaPool::<Expr<'static>>::random_up_to(&mut rng, None, 3, &[], &[])
            .unwrap_err();
        assert_eq!(err, RandomError::NoBaseExpressions);

        Ok(())
    }
}
