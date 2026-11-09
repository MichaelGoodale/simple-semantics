//! Ways to sample random expressions from a language of thought.

use rand::{Rng, RngExt, seq::SliceRandom};
use thiserror::Error;

use crate::lambda::{
    ExprType, FreeVar, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool,
    RootedLambdaPool, types::LambdaType,
};

///Errors that arise from sampling with [`RootedLambdaPool::random_exact`] and
///[`RootedLambdaPool::random_up_to`]
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum SamplingError {
    ///No expression of type typ (or any type) with size <= max_size
    CantFindInSizeUpTo {
        ///The type which could not be constructed (none if no provided type).
        typ: Option<LambdaType>,
        ///The biggest possible size
        max_size: usize,
    },
    ///No expression of type typ (or any type) with size = max_size
    CantFindOfSize {
        ///The type which could not be constructed (none if no provided type).
        typ: Option<LambdaType>,
        ///The size that no expression for could be found
        size: usize,
    },
    ///Can't generate anything because there are no expressions
    NoBaseExpressions,
}

impl std::fmt::Display for SamplingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SamplingError::CantFindInSizeUpTo {
                typ: Some(typ),
                max_size,
            } => write!(
                f,
                "Cannot find any expression of type {typ} of size {max_size} or less"
            ),
            SamplingError::CantFindInSizeUpTo {
                typ: None,
                max_size,
            } => write!(f, "Cannot find any expression of size {max_size} or less"),
            SamplingError::CantFindOfSize {
                typ: Some(typ),
                size,
            } => write!(
                f,
                "Cannot find any expression of type {typ} with size of {size}"
            ),
            SamplingError::CantFindOfSize { typ: None, size } => {
                write!(f, "Cannot find any expression with size of {size}")
            }
            SamplingError::NoBaseExpressions => write!(
                f,
                "You need to provide base expressions, otherwise there is nothing to sample"
            ),
        }
    }
}

const GENERATION_ATTEMPTS: usize = 256;

struct RandomExprBuilder<'src, 'a, T: LambdaLanguageOfThought> {
    pool: LambdaPool<'src, T>,
    context: Vec<LambdaType>,
    leaves: &'a [LambdaExpr<'src, T>],
}

impl<'src, T: LambdaLanguageOfThought + Clone + PartialEq> RandomExprBuilder<'src, '_, T> {
    ///Attempt to generate an expression with roll-back to re-attempt if there is a failure.
    fn generate(
        &mut self,
        rng: &mut impl Rng,
        target: &LambdaType,
        size: usize,
        attempts: usize,
    ) -> Result<LambdaExprRef, ()> {
        for _ in 0..attempts {
            let mark = self.pool.0.len();

            if let Some(r) = self.try_generate(rng, target, size, attempts) {
                return Ok(r);
            }

            //undo anything that was added
            self.pool.0.truncate(mark);
        }

        Err(())
    }

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
            return self.random_expression(rng, target);
        }

        //Add lambda as an option if we can.
        let count =
            self.n_possible_heads(target, 1, size - 1) + if target.is_function() { 1 } else { 0 };
        if count == 0 {
            return None;
        }
        let choice = rng.random_range(0..count);

        if target.is_function() && choice == count - 1 {
            let (arg, res) = target.split().ok()?;

            self.context.insert(0, arg.clone());
            let body = self.generate(rng, res, size - 1, child_attempts(attempts));
            self.context.remove(0);
            let body = body.ok()?;

            let lambda = self.pool.add(LambdaExpr::Lambda(body, arg.clone()));
            if !self.pool.uses_bvar(body) || self.pool.is_eta_opportunity(lambda) {
                return None;
            }
            Some(lambda)
        } else {
            self.random_application(rng, target, size, choice, attempts)
        }
    }

    ///Pushes random single expression
    fn random_expression(&mut self, rng: &mut impl Rng, typ: &LambdaType) -> Option<LambdaExprRef> {
        let count = self.n_possible_heads(typ, 0, 0);
        if count == 0 {
            None
        } else {
            let head = rng.random_range(0..count);
            Some(
                self.pool
                    .add(self.head_expr(self.nth_possible_head(head, typ, 0, 0).unwrap())),
            )
        }
    }

    fn random_application(
        &mut self,
        rng: &mut impl Rng,
        target: &LambdaType,
        size: usize,
        head: usize,
        attempts: usize,
    ) -> Option<LambdaExprRef> {
        let head = self.nth_possible_head(head, target, 1, size - 1)?;
        let args = n_apps_until_type(self.head_type(head), target, size - 1)?;

        let mut cur = self.pool.add(self.head_expr(head));
        let mut typ = &self.head_type(head).clone();

        for s in split_size(rng, size - 1, args)? {
            let (arg_typ, rest) = typ.split().ok()?;

            let argument = self
                .generate(rng, arg_typ, s, child_attempts(attempts))
                .ok()?;
            if self.is_involutory_repetition(cur, argument) {
                return None;
            }

            cur = self.pool.add(LambdaExpr::Application {
                subformula: cur,
                argument,
            });
            typ = rest;
        }

        Some(cur)
    }

    ///Number of possible base expressions at this point
    fn n_heads(&self) -> usize {
        self.leaves.len() + self.context.len()
    }

    ///How many heads are or can be turned into something of type t with at most max_len applications
    fn n_possible_heads(&self, target: &LambdaType, min_len: usize, max_len: usize) -> usize {
        (0..self.n_heads())
            .filter(|&i| {
                n_apps_until_type(self.head_type(i), target, max_len).is_some_and(|x| x >= min_len)
            })
            .count()
    }

    fn nth_possible_head(
        &self,
        head: usize,
        target: &LambdaType,
        min_len: usize,
        max_len: usize,
    ) -> Option<usize> {
        (0..self.n_heads())
            .filter(|&i| {
                n_apps_until_type(self.head_type(i), target, max_len).is_some_and(|x| x >= min_len)
            })
            .nth(head)
    }

    fn head_type(&self, i: usize) -> &LambdaType {
        self.leaves
            .get(i)
            .map(|x| x.get_typ().unwrap())
            .unwrap_or_else(|| &self.context[i - self.leaves.len()])
    }

    fn head_expr(&self, i: usize) -> LambdaExpr<'src, T> {
        match self.leaves.get(i) {
            Some(x) => x.clone(),
            None => {
                let j = i - self.leaves.len();
                LambdaExpr::BoundVariable(j, self.context[j].clone())
            }
        }
    }

    ///Checks if an expression is a redudant involution (e.g. `~~phi`)
    fn is_involutory_repetition(&self, f: LambdaExprRef, x: LambdaExprRef) -> bool {
        let LambdaExpr::LanguageOfThoughtExpr(outer, _) = self.pool.get(f) else {
            return false;
        };

        if !outer.involutory() {
            return false;
        }

        let LambdaExpr::Application { subformula, .. } = self.pool.get(x) else {
            return false;
        };

        matches!(
            self.pool.get(*subformula),
            LambdaExpr::LanguageOfThoughtExpr(inner, _) if inner == outer
        )
    }
}

///The number of arguments `typ` can be applied to (between `min_len` and `max_len`) to result in `target`.
fn n_apps_until_type(typ: &LambdaType, target: &LambdaType, max_len: usize) -> Option<usize> {
    if typ == target {
        return Some(0);
    }
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

fn child_attempts(attempts: usize) -> usize {
    (attempts / 8).max(1)
}

fn mk_leaves<'src, T: LambdaLanguageOfThought + Clone>(
    base_expressions: &[T],
    free_var: &[(FreeVar<'src>, LambdaType)],
) -> Result<Vec<LambdaExpr<'src, T>>, SamplingError> {
    let mut leaves: Vec<_> = base_expressions
        .iter()
        .map(|x| LambdaExpr::LanguageOfThoughtExpr(x.clone(), ExprType::NoVar))
        .collect();

    leaves.extend(
        free_var
            .iter()
            .map(|(f, t)| LambdaExpr::FreeVariable(*f, t.clone())),
    );

    if leaves.is_empty() {
        Err(SamplingError::NoBaseExpressions)
    } else {
        Ok(leaves)
    }
}

fn generate_pool<'src, T: LambdaLanguageOfThought + Clone + PartialEq>(
    rng: &mut impl Rng,
    typ: &LambdaType,
    size: usize,
    leaves: &[LambdaExpr<'src, T>],
) -> Option<RootedLambdaPool<'src, T>> {
    let mut builder = RandomExprBuilder {
        pool: LambdaPool(vec![]),
        context: vec![],
        leaves,
    };

    builder
        .generate(rng, typ, size, GENERATION_ATTEMPTS)
        .ok()
        .map(|root| RootedLambdaPool {
            pool: builder.pool,
            root,
        })
}

impl<'src, T: LambdaLanguageOfThought + Clone + PartialEq> RootedLambdaPool<'src, T> {
    ///Randomly generate an expression with a length of `size` (length measured with
    ///[`RootedLambdaPool::appless_len`]
    ///
    ///If no `target` type is passed, it will randomly sample a typ.
    ///
    ///# Errors
    ///Returns a [`SamplingError`] if no expression be found under these parameters
    pub fn random_exact(
        target: Option<&LambdaType>,
        size: usize,
        base_expressions: &[T],
        free_var: &[(FreeVar<'src>, LambdaType)],
        rng: &mut impl Rng,
    ) -> Result<Self, SamplingError> {
        let leaves = mk_leaves(base_expressions, free_var)?;
        let no_target = target.is_none();
        let typ = match target {
            Some(x) => x,
            None => &LambdaType::random(rng),
        };

        let mut sol = generate_pool(rng, typ, size, &leaves);

        let mut t = 0;
        while no_target && sol.is_none() && t < GENERATION_ATTEMPTS {
            let typ = LambdaType::random(rng);
            sol = generate_pool(rng, &typ, size, &leaves);
            t += 1;
        }
        sol.ok_or(SamplingError::CantFindOfSize {
            typ: if no_target { None } else { Some(typ.clone()) },
            size,
        })
    }

    ///Randomly generate an expression with a length from 1 to `max_size` (length measured with
    ///[`RootedLambdaPool::appless_len`]
    ///
    ///If no `target` type is passed, it will randomly sample a typ.
    ///
    ///# Errors
    ///Returns a [`SamplingError`] if no expression be found under these parameters
    pub fn random_up_to(
        target: Option<&LambdaType>,
        max_size: usize,
        base_expressions: &[T],
        free_var: &[(FreeVar<'src>, LambdaType)],
        rng: &mut impl Rng,
    ) -> Result<Self, SamplingError> {
        let leaves = mk_leaves(base_expressions, free_var)?;
        let no_target = target.is_none();
        let typ = match target {
            Some(x) => x,
            None => &LambdaType::random(rng),
        };

        let mut sizes: Vec<usize> = (1..=max_size).collect();
        sizes.shuffle(rng);

        let mut sol = sizes
            .iter()
            .find_map(|&size| generate_pool(rng, typ, size, &leaves));
        let mut t = 0;
        while no_target && sol.is_none() && t < GENERATION_ATTEMPTS {
            let typ = LambdaType::random(rng);
            sol = sizes
                .iter()
                .find_map(|&size| generate_pool(rng, &typ, size, &leaves));
            t += 1;
        }

        sol.ok_or(SamplingError::CantFindInSizeUpTo {
            typ: if no_target { None } else { Some(typ.clone()) },
            max_size,
        })
    }
}

#[cfg(test)]
mod test {
    use itertools::Itertools;
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use crate::{
        lambda::{
            LambdaExpr, Literal,
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

        //No expression of size 1 of type t.
        let err = RootedLambdaPool::<Expr<'static>>::random_exact(
            Some(&LambdaType::T),
            1,
            &base_expressions(),
            &[],
            &mut rng,
        )
        .unwrap_err();
        assert_eq!(
            err,
            SamplingError::CantFindOfSize {
                typ: Some(LambdaType::T),
                size: 1
            }
        );

        for _ in 0..25 {
            for size in [2, 3, 4, 5, 6] {
                let expr = RootedLambdaPool::<Expr<'static>>::random_exact(
                    Some(&LambdaType::T),
                    size,
                    &base_expressions(),
                    &[],
                    &mut rng,
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

        for _ in 0..25 {
            let expr = RootedLambdaPool::<Expr<'static>>::random_up_to(
                None,
                6,
                &base_expressions(),
                &[],
                &mut rng,
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

        let mut contains_free_var = false;
        for _ in 0..25 {
            let expr = RootedLambdaPool::<Expr<'static>>::random_up_to(
                Some(&LambdaType::T),
                5,
                &base_expressions(),
                &free_var,
                &mut rng,
            )?;
            assert!(expr.is_reduced(), "{expr} is not fully reduced");
            assert_eq!(expr.get_type()?, LambdaType::T);
            if expr.pool.0.contains(&LambdaExpr::FreeVariable(
                FreeVar::Named("x"),
                LambdaType::E,
            )) {
                contains_free_var = true;
            }
        }

        assert!(contains_free_var, "The free variable was never sampled!");

        Ok(())
    }

    #[test]
    fn test_not_constructible() -> anyhow::Result<()> {
        //given we have no atomic events in `base_expressions`, it can't sample an event of size one.
        let mut rng = ChaCha8Rng::seed_from_u64(3);

        let err = RootedLambdaPool::<Expr<'static>>::random_exact(
            Some(&LambdaType::E),
            1,
            &base_expressions(),
            &[],
            &mut rng,
        )
        .unwrap_err();

        assert_eq!(
            err,
            SamplingError::CantFindOfSize {
                typ: Some(LambdaType::E),
                size: 1
            }
        );

        let err = RootedLambdaPool::<Expr<'static>>::random_up_to(None, 1, &[], &[], &mut rng)
            .unwrap_err();
        assert_eq!(err, SamplingError::NoBaseExpressions);

        Ok(())
    }

    #[test]
    fn test_at_sampling() -> anyhow::Result<()> {
        let mut rng = ChaCha8Rng::seed_from_u64(4);

        for _ in 0..25 {
            let expr = RootedLambdaPool::<Expr<'static>>::random_exact(
                Some(LambdaType::at()),
                1,
                &base_expressions(),
                &[],
                &mut rng,
            )?;
            assert_eq!(expr.get_type()?, *LambdaType::at());
            assert_eq!(expr.appless_len(), 1);
        }

        Ok(())
    }

    #[test]
    fn test_lambdas() -> anyhow::Result<()> {
        let mut rng = ChaCha8Rng::seed_from_u64(5);
        let (mut generated, mut lambdas, mut bvars) = (0, 0, 0);

        for _ in 0..25 {
            let Ok(expr) = RootedLambdaPool::<Expr<'static>>::random_exact(
                Some(LambdaType::at()),
                4,
                &base_expressions(),
                &[],
                &mut rng,
            ) else {
                continue;
            };

            assert!(expr.is_reduced(), "{expr} is not fully reduced");
            assert_eq!(expr.get_type()?, *LambdaType::at());
            assert_eq!(expr.appless_len(), 4);
            generated += 1;

            if expr
                .pool
                .0
                .iter()
                .any(|x| matches!(x, LambdaExpr::Lambda(..)))
            {
                lambdas += 1;
            }
            if expr
                .pool
                .0
                .iter()
                .any(|x| matches!(x, LambdaExpr::BoundVariable(..)))
            {
                bvars += 1;
            }
        }

        assert!(generated > 0, "nothing was generated");
        assert!(lambdas > 0, "no lambdas were generated");
        assert!(bvars > 0, "no bvars were generated");
        Ok(())
    }

    ///Check all expressions can be generated (at least for small numbers)
    #[test]
    fn test_full_coverage() -> anyhow::Result<()> {
        use crate::lambda::enumerator::Generator;
        use std::collections::HashSet;

        let types = [
            LambdaType::A,
            LambdaType::E,
            LambdaType::T,
            LambdaType::at().clone(),
            LambdaType::et().clone(),
            LambdaType::tt().clone(),
        ];

        let bases = base_expressions();
        let mut generator: Generator<Expr> = Generator::new(bases.clone(), vec![]);
        let mut rng = ChaCha8Rng::seed_from_u64(6);

        for typ in &types {
            //All expressions of this type up to size 3, bucketed by their appless length.
            let mut expected: Vec<HashSet<RootedLambdaPool<Expr>>> =
                vec![HashSet::new(), HashSet::new(), HashSet::new()];

            for id in generator.enumerate_or_generate(typ.clone(), 3) {
                let expr = generator.to_rooted_lambda_pool(id).unwrap();
                expected[expr.appless_len() - 1].insert(expr);
            }

            for (i, expected) in expected.iter().enumerate() {
                let size = i + 1;
                let mut seen = HashSet::new();

                for _ in 0..150 {
                    let Ok(expr) = RootedLambdaPool::<Expr<'static>>::random_exact(
                        Some(typ),
                        size,
                        &bases,
                        &[],
                        &mut rng,
                    ) else {
                        continue;
                    };

                    assert_eq!(expr.get_type()?, *typ);
                    assert_eq!(expr.appless_len(), size);
                    seen.insert(expr);
                }

                assert_eq!(
                    seen,
                    *expected,
                    "sampling type {typ} of size {size} doesn't match enumeration because {{{}}} != {{{}}}",
                    seen.iter().map(|x| x.to_string()).join(","),
                    expected.iter().map(|x| x.to_string()).join(",")
                );
            }
        }

        Ok(())
    }
}
