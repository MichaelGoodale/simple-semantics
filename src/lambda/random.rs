//! Randomly generates lambda expressions of a language of thought.
//!
//!Unlike [`crate::lambda::enumerator`], which enumerates *all* expressions up to a size, this
//!module randomly descends through the space of well-typed, beta-eta normal expressions and
//!generates a single one. Applications are "free" w.r.t. size (see
//![`RootedLambdaPool::appless_len`]), so the generator uses head applications to go deeper
//!without spending size.

use rand::{
    Rng, RngExt,
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

///How many attempts the root of a generation gets before giving up. Failed attempts are retried
///with fresh random choices, and each child node gets a fraction of its parent's attempts (see
///[`child_attempts`]), which bounds the search.
const ATTEMPTS: usize = 256;

///The state of a single random descent.
struct RandomExprBuilder<'src, 'a, T> {
    pool: Vec<LambdaExpr<'src, T>>,
    ///The types of the bound variables in scope, indexed by De Bruijn index.
    context: Vec<LambdaType>,
    ///The usable base expressions and free variables, with their types.
    leaves: &'a [(LambdaExpr<'src, T>, LambdaType)],
}

impl<'src, T: LambdaLanguageOfThought + Clone + PartialEq> RandomExprBuilder<'src, '_, T> {
    ///Randomly generates an expression of exactly `size` (in the [`RootedLambdaPool::appless_len`]
    ///sense) of type `target`. Failed attempts are rolled back and retried with fresh random
    ///choices, up to `attempts` times.
    fn generate(
        &mut self,
        rng: &mut impl Rng,
        target: &LambdaType,
        size: usize,
        attempts: usize,
    ) -> Result<LambdaExprRef, ()> {
        for _ in 0..attempts {
            let pool_mark = self.pool.len();
            let context_mark = self.context.len();

            if let Some(r) = self.try_generate(rng, target, size, attempts) {
                return Ok(r);
            }

            self.pool.truncate(pool_mark);
            self.context.truncate(context_mark);
        }

        Err(())
    }

    ///A single attempt: randomly picks what kind of node to build and builds it, recursing.
    fn try_generate(
        &mut self,
        rng: &mut impl Rng,
        target: &LambdaType,
        size: usize,
        attempts: usize,
    ) -> Option<LambdaExprRef> {
        if size == 0 {
            return None;
        }
        if size == 1 {
            return self.random_leaf(rng, target);
        }

        //The choices are a lambda (if the target is a function type) or a head applied to
        //arguments.
        let heads = self.app_head_count(target, size - 1);
        let count = usize::from(target.is_function()) + heads;
        if count == 0 {
            return None;
        }
        let choice = rng.random_range(0..count);

        if target.is_function() && choice == 0 {
            let (arg, res) = target.split().ok()?;

            self.context.insert(0, arg.clone());
            let body = self.generate(rng, res, size - 1, child_attempts(attempts));
            self.context.remove(0);
            let body = body.ok()?;

            //The bound variable must be used and the body must not be an eta redex.
            if !self.uses_bvar(body, 0) || self.is_eta_redex(body) {
                return None;
            }

            Some(self.push(LambdaExpr::Lambda(body, arg.clone())))
        } else {
            let head = choice - usize::from(target.is_function());
            self.random_application(rng, target, size, head, attempts)
        }
    }

    ///Pushes a random leaf (base expression, free variable or bound variable) of type `typ`.
    fn random_leaf(&mut self, rng: &mut impl Rng, typ: &LambdaType) -> Option<LambdaExprRef> {
        let head = random_index(rng, self.head_count(), |i| self.head_type(i) == typ)?;
        Some(self.push(self.head_expr(head)))
    }

    ///Pushes the `head`-th applicable head (of those that can be applied to reach `target`)
    ///applied to randomly generated arguments.
    fn random_application(
        &mut self,
        rng: &mut impl Rng,
        target: &LambdaType,
        size: usize,
        head: usize,
        attempts: usize,
    ) -> Option<LambdaExprRef> {
        //Find the `head`-th head with an argument chain to `target`.
        let head = (0..self.head_count())
            .filter(|&i| chain_len(self.head_type(i), target, size - 1).is_some())
            .nth(head)?;
        let args = chain_len(self.head_type(head), target, size - 1)?;

        let head_type = self.head_type(head).clone();
        let mut cur = self.push(self.head_expr(head));
        let mut typ = &head_type;

        for s in split_size(rng, size - 1, args)? {
            let (arg_typ, rest) = typ.split().ok()?;

            let argument = self
                .generate(rng, arg_typ, s, child_attempts(attempts))
                .ok()?;
            if self.is_involutory(cur, argument) {
                return None;
            }

            cur = self.push(LambdaExpr::Application {
                subformula: cur,
                argument,
            });
            typ = rest;
        }

        Some(cur)
    }

    fn push(&mut self, expr: LambdaExpr<'src, T>) -> LambdaExprRef {
        self.pool.push(expr);
        LambdaExprRef(u32::try_from(self.pool.len() - 1).unwrap())
    }

    fn get(&self, r: LambdaExprRef) -> &LambdaExpr<'src, T> {
        &self.pool[usize::try_from(r.0).unwrap()]
    }

    ///The total number of heads: leaves plus bound variables in scope.
    fn head_count(&self) -> usize {
        self.leaves.len() + self.context.len()
    }

    ///The number of heads that can be applied to (at most `max_len`) arguments to reach `target`.
    fn app_head_count(&self, target: &LambdaType, max_len: usize) -> usize {
        (0..self.head_count())
            .filter(|&i| chain_len(self.head_type(i), target, max_len).is_some())
            .count()
    }

    ///The type of the `i`-th head.
    fn head_type(&self, i: usize) -> &LambdaType {
        self.leaves
            .get(i)
            .map(|(_, t)| t)
            .unwrap_or_else(|| &self.context[i - self.leaves.len()])
    }

    ///A clone of the expression of the `i`-th head.
    fn head_expr(&self, i: usize) -> LambdaExpr<'src, T> {
        match self.leaves.get(i) {
            Some((x, _)) => x.clone(),
            None => {
                let j = i - self.leaves.len();
                LambdaExpr::BoundVariable(j, self.context[j].clone())
            }
        }
    }

    ///Checks if the subtree rooted at `root` uses the bound variable with De Bruijn index `idx`.
    fn uses_bvar(&self, root: LambdaExprRef, idx: usize) -> bool {
        let mut stack = vec![root];
        while let Some(r) = stack.pop() {
            match self.get(r) {
                LambdaExpr::BoundVariable(x, _) if *x == idx => return true,
                expr => stack.extend(expr.get_children()),
            }
        }
        false
    }

    ///Checks if `body` (a lambda's body) is the site of an eta reduction, i.e. it applies a
    ///subformula that doesn't use the bound variable to that variable.
    fn is_eta_redex(&self, body: LambdaExprRef) -> bool {
        let LambdaExpr::Application {
            subformula,
            argument,
        } = self.get(body)
        else {
            return false;
        };

        matches!(self.get(*argument), LambdaExpr::BoundVariable(0, _))
            && !self.uses_bvar(*subformula, 0)
    }

    ///Checks if `f` is an involutory expression applied to an application of itself, e.g.
    ///`!(!p)`, which can be simplified.
    fn is_involutory(&self, f: LambdaExprRef, x: LambdaExprRef) -> bool {
        let LambdaExpr::LanguageOfThoughtExpr(outer, _) = self.get(f) else {
            return false;
        };

        if !outer.involutory() {
            return false;
        }

        let LambdaExpr::Application { subformula, .. } = self.get(x) else {
            return false;
        };

        matches!(
            self.get(*subformula),
            LambdaExpr::LanguageOfThoughtExpr(inner, _) if inner == outer
        )
    }
}

///The number of arguments `typ` can be applied to (at most `max_len`) to result in `target`.
fn chain_len(typ: &LambdaType, target: &LambdaType, max_len: usize) -> Option<usize> {
    let mut len = 0;
    let mut cur = typ;
    while let Ok((_, r)) = cur.split() {
        len += 1;
        if len > max_len {
            return None;
        }
        if r == target {
            return Some(len);
        }
        cur = r;
    }
    None
}

///Randomly splits `total` into `parts` sizes, each at least one.
fn split_size(rng: &mut impl Rng, total: usize, parts: usize) -> Option<Vec<usize>> {
    if total < parts {
        return None;
    }

    let mut sizes = vec![1; parts];
    for _ in 0..total - parts {
        sizes[rng.random_range(0..parts)] += 1;
    }

    Some(sizes)
}

///How many attempts a child node gets, given the attempts of its parent.
fn child_attempts(attempts: usize) -> usize {
    (attempts / 8).max(1)
}

///Picks a random index `0..n` satisfying `f`, or [`None`] if there are none.
fn random_index(rng: &mut impl Rng, n: usize, f: impl Fn(usize) -> bool) -> Option<usize> {
    let count = (0..n).filter(|&i| f(i)).count();
    if count == 0 {
        return None;
    }

    (0..n).filter(|&i| f(i)).nth(rng.random_range(0..count))
}

///Picks a random target type if none was given.
fn pick_target(
    rng: &mut impl Rng,
    target: Option<LambdaType>,
    leaves: &[(LambdaExpr<'_, impl LambdaLanguageOfThought>, LambdaType)],
) -> Result<LambdaType, RandomError> {
    match target {
        Some(t) => Ok(t),
        None => leaves
            .choose(rng)
            .map(|(_, t)| t.clone())
            .ok_or(RandomError::NoBaseExpressions),
    }
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

///Runs a single random descent, returning [`None`] if it fails.
fn generate_pool<'src, T: LambdaLanguageOfThought + Clone + PartialEq>(
    rng: &mut impl Rng,
    typ: &LambdaType,
    size: usize,
    leaves: &[(LambdaExpr<'src, T>, LambdaType)],
) -> Option<RootedLambdaPool<'src, T>> {
    let mut builder = RandomExprBuilder {
        pool: vec![],
        context: vec![],
        leaves,
    };

    builder
        .generate(rng, typ, size, ATTEMPTS)
        .ok()
        .map(|root| RootedLambdaPool {
            pool: LambdaPool(builder.pool),
            root,
        })
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

        generate_pool(rng, &typ, size, &leaves)
            .ok_or(RandomError::SizeNotConstructible { typ, size })
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

        sizes
            .iter()
            .find_map(|&size| generate_pool(rng, &typ, size, &leaves))
            .ok_or(RandomError::NotConstructible { typ })
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
