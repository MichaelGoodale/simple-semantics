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
use smallvec::SmallVec;
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

///The number of ways to choose `r` things from `n` (in any order).
fn binom(n: usize, r: usize) -> usize {
    if r > n {
        return 0;
    }
    let r = r.min(n - r);
    let mut c = 1;
    for i in 0..r {
        c = c * (n - i) / (i + 1);
    }
    c
}

///The number of ways `total` can be split into `parts` sizes, each at least one.
fn compositions_count(total: usize, parts: usize) -> usize {
    if total < parts {
        return 0;
    }
    binom(total - 1, parts - 1)
}

///The `idx`-th (in lexicographic order) way to split `total` into `parts` sizes, each at least
///one.
fn unrank_composition(idx: usize, total: usize, parts: usize) -> SmallVec<[usize; 4]> {
    let mut sizes = SmallVec::new();
    let (mut total, mut parts, mut idx) = (total, parts, idx);

    while parts > 1 {
        let mut first = 1;
        loop {
            let count = compositions_count(total - first, parts - 1);
            if idx < count {
                sizes.push(first);
                total -= first;
                parts -= 1;
                break;
            }
            idx -= count;
            first += 1;
        }
    }
    sizes.push(total);

    sizes
}

///The length of the `j`-th way `typ` can be applied to arguments to result in `target`, with at
///most `max_len` arguments.
fn chain_length(
    typ: &LambdaType,
    target: &LambdaType,
    max_len: usize,
    mut j: usize,
) -> Option<usize> {
    let mut len = 0;
    let mut cur = typ;
    while let Ok((_, r)) = cur.split() {
        len += 1;
        if len > max_len {
            break;
        }
        if r == target {
            if j == 0 {
                return Some(len);
            }
            j -= 1;
        }
        cur = r;
    }
    None
}

///A decoded candidate for a node, addressed by index so no candidates are materialized until one
///is chosen.
enum DecodedChoice {
    ///The `n`-th leaf of the target type.
    Leaf(usize),
    ///The bound variable with the given De Bruijn index.
    BoundVar(usize),
    ///A lambda of the target (function) type.
    Lambda,
    ///The `chain`-th argument chain of the `head`-th head expression, with the `comp`-th split
    ///of the remaining size over the arguments.
    Application {
        head: usize,
        chain: usize,
        comp: usize,
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
    ///
    ///Candidates are counted and addressed by index (see [`DecodedChoice`]) rather than
    ///collected, so backtracking allocates nothing. They are attempted starting from a random
    ///index, wrapping around, which covers every candidate.
    fn generate(
        &mut self,
        rng: &mut impl Rng,
        target: &LambdaType,
        size: usize,
    ) -> Result<LambdaExprRef, ()> {
        if size == 0 || self.budget == 0 {
            return Err(());
        }

        let count = self.choice_count(target, size);
        if count == 0 {
            return Err(());
        }

        let start = rng.random_range(0..count);
        for k in 0..count {
            if self.budget == 0 {
                return Err(());
            }
            self.budget -= 1;

            let idx = (start + k) % count;
            let pool_mark = self.pool.len();
            let context_mark = self.context.len();

            let choice = self.decode(idx, target, size);
            if let Some(r) = self.try_choice(rng, choice, target, size) {
                return Ok(r);
            }

            self.pool.truncate(pool_mark);
            self.context.truncate(context_mark);
        }

        Err(())
    }

    ///The number of candidates for a node of type `target` and size `size`.
    fn choice_count(&self, target: &LambdaType, size: usize) -> usize {
        if size == 1 {
            return self.leaf_count(target) + self.bound_var_count(target);
        }

        let mut count = usize::from(target.is_function());
        for head in 0..self.head_count() {
            let typ = self.head_type(head);
            let mut len = 0;
            let mut cur = typ;
            while let Ok((_, r)) = cur.split() {
                len += 1;
                if len > size - 1 {
                    break;
                }
                if r == target {
                    count += compositions_count(size - 1, len);
                }
                cur = r;
            }
        }

        count
    }

    ///Decodes a candidate index into the candidate it refers to.
    fn decode(&self, idx: usize, target: &LambdaType, size: usize) -> DecodedChoice {
        if size == 1 {
            let leaves = self.leaf_count(target);
            if idx < leaves {
                return DecodedChoice::Leaf(self.nth_leaf(target, idx));
            }
            return DecodedChoice::BoundVar(self.nth_bound_var(target, idx - leaves));
        }

        if target.is_function() && idx == 0 {
            return DecodedChoice::Lambda;
        }

        let mut idx = idx - usize::from(target.is_function());
        for head in 0..self.head_count() {
            let typ = self.head_type(head);
            let mut len = 0;
            let mut chain = 0;
            let mut cur = typ;
            while let Ok((_, r)) = cur.split() {
                len += 1;
                if len > size - 1 {
                    break;
                }
                if r == target {
                    let count = compositions_count(size - 1, len);
                    if idx < count {
                        return DecodedChoice::Application {
                            head,
                            chain,
                            comp: idx,
                        };
                    }
                    idx -= count;
                    chain += 1;
                }
                cur = r;
            }
        }

        panic!("Invalid candidate index {idx} for type {target} of size {size}!")
    }

    ///Attempts a single choice, returning [`None`] (leaving the builder in a rolled-back state)
    ///if it dead-ends.
    fn try_choice(
        &mut self,
        rng: &mut impl Rng,
        choice: DecodedChoice,
        target: &LambdaType,
        size: usize,
    ) -> Option<LambdaExprRef> {
        match choice {
            DecodedChoice::Leaf(i) => {
                let expr = self.leaves[i].0.clone();
                Some(self.push(expr))
            }
            DecodedChoice::BoundVar(i) => {
                let expr = LambdaExpr::BoundVariable(i, self.context[i].clone());
                Some(self.push(expr))
            }
            DecodedChoice::Lambda => {
                let Ok((arg, res)) = target.split() else {
                    return None;
                };

                self.context.insert(0, arg.clone());
                let body = self.generate(rng, res, size - 1);
                self.context.remove(0);
                let body = body.ok()?;

                //The bound variable must be used and the body must not be an eta redex.
                if !self.uses_bvar(body, 0) || self.is_eta_redex(body) {
                    return None;
                }

                Some(self.push(LambdaExpr::Lambda(body, arg.clone())))
            }
            DecodedChoice::Application { head, chain, comp } => {
                let typ = self.head_type(head).clone();
                let len = chain_length(&typ, target, size - 1, chain)?;
                let sizes = unrank_composition(comp, size - 1, len);

                let mut cur = self.push(self.head_expr(head));
                let mut typ = &typ;
                for s in sizes {
                    let Ok((arg_typ, r)) = typ.split() else {
                        return None;
                    };

                    let argument = self.generate(rng, arg_typ, s).ok()?;
                    if self.is_involutory(cur, argument) {
                        return None;
                    }

                    cur = self.push(LambdaExpr::Application {
                        subformula: cur,
                        argument,
                    });
                    typ = r;
                }

                Some(cur)
            }
        }
    }

    fn push(&mut self, expr: LambdaExpr<'src, T>) -> LambdaExprRef {
        self.pool.push(expr);
        LambdaExprRef(u32::try_from(self.pool.len() - 1).unwrap())
    }

    ///The number of leaves (base expressions and free variables) of type `typ`.
    fn leaf_count(&self, typ: &LambdaType) -> usize {
        self.leaves.iter().filter(|(_, t)| *t == *typ).count()
    }

    ///The index into `leaves` of the `j`-th leaf of type `typ`.
    fn nth_leaf(&self, typ: &LambdaType, j: usize) -> usize {
        self.leaves
            .iter()
            .enumerate()
            .filter(|(_, (_, t))| *t == *typ)
            .nth(j)
            .map(|(i, _)| i)
            .unwrap_or_else(|| panic!("Invalid leaf index {j} for type {typ}!"))
    }

    ///The number of bound variables in scope of type `typ`.
    fn bound_var_count(&self, typ: &LambdaType) -> usize {
        self.context.iter().filter(|t| *t == typ).count()
    }

    ///The De Bruijn index of the `j`-th bound variable of type `typ`.
    fn nth_bound_var(&self, typ: &LambdaType, j: usize) -> usize {
        self.context
            .iter()
            .enumerate()
            .filter(|(_, t)| *t == typ)
            .nth(j)
            .map(|(i, _)| i)
            .unwrap_or_else(|| panic!("Invalid bound variable index {j} for type {typ}!"))
    }

    ///The total number of heads: leaves plus bound variables in scope.
    fn head_count(&self) -> usize {
        self.leaves.len() + self.context.len()
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
