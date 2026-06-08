use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::lambda::{
    LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool, RootedLambdaPool,
};

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub(crate) enum ArgumentIterator<A, B, C, D> {
    A(A),
    B(B),
    C(C),
    D(D),
}

impl<A, B, C, D, Item> Iterator for ArgumentIterator<A, B, C, D>
where
    A: Iterator<Item = Item>,
    B: Iterator<Item = Item>,
    C: Iterator<Item = Item>,
    D: Iterator<Item = Item>,
{
    type Item = Item;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ArgumentIterator::A(a) => a.next(),
            ArgumentIterator::B(b) => b.next(),
            ArgumentIterator::C(c) => c.next(),
            ArgumentIterator::D(d) => d.next(),
        }
    }
}

///A representation of an expression in a [`RootedLambdaPool`]. This is used for fancy
///datastructures that involve breaking down a [`RootedLambdaPool`] such as
///[tries](https://en.wikipedia.org/wiki/Trie).
///
///The internal content of the expression is hidden and can be reconstructed by passing it as an iterator
///to [`RootedLambdaPool::from_beads`].
///
///It includes all the data necessary to reconstruct a [`RootedLambdaPool`] by putting each token as
///a bead, along with a record of which index is the root (referred to in docs as a root bead).
#[derive(Debug, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct ExpressionBead<'a, T: LambdaLanguageOfThought>(ExpressionBeadInner<'a, T>);

#[derive(Debug, Clone, Eq, PartialEq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
enum ExpressionBeadInner<'a, T: LambdaLanguageOfThought> {
    Expr(#[serde(borrow)] LambdaExpr<'a, T>),
    Root(LambdaExprRef),
}

///An error that arises when constructing a [`RootedLambdaPool`] from beads.
#[derive(Error, Debug)]
pub enum BeadError {
    ///The iterator is missing a root.
    #[error("This bead iterator is missing its root!")]
    MissingRoot,
    ///The iterator has multiple roots.
    #[error("This bead iterator has multiple roots!")]
    MultipleRoots,
    ///The resulting expression is malformed.
    #[error("This bead iterator creates a malformed RootedLambdaPool")]
    MalformedPool,
}

impl<'a, T: LambdaLanguageOfThought> RootedLambdaPool<'a, T> {
    ///Converts a [`RootedLambdaPool`] into beads for use in fancy data structures.
    pub fn into_beads(self) -> impl Iterator<Item = ExpressionBead<'a, T>> {
        std::iter::once(ExpressionBead(ExpressionBeadInner::Root(self.root))).chain(
            self.pool
                .0
                .into_iter()
                .map(|x| ExpressionBead(ExpressionBeadInner::Expr(x))),
        )
    }

    ///Reconstruct a [`RootedLambdaPool`] from an iterator of beads.
    ///
    ///# Errors
    ///
    ///Returrns [`BeadError`] if the
    pub fn from_beads(
        iter: impl IntoIterator<Item = ExpressionBead<'a, T>>,
    ) -> Result<RootedLambdaPool<'a, T>, BeadError> {
        let mut root = None;
        let pool = LambdaPool(
            iter.into_iter()
                .filter_map(|x| match x.0 {
                    ExpressionBeadInner::Expr(lambda_expr) => Some(Ok(lambda_expr)),
                    ExpressionBeadInner::Root(_) if root.is_some() => {
                        Some(Err(BeadError::MultipleRoots))
                    }
                    ExpressionBeadInner::Root(x) => {
                        root = Some(x);
                        None
                    }
                })
                .collect::<Result<Vec<_>, _>>()?,
        );
        let root = root.ok_or(BeadError::MissingRoot)?;
        if root.0 as usize >= pool.0.len() {
            return Err(BeadError::MalformedPool);
        }
        pool.get_type(root).map_err(|_| BeadError::MalformedPool)?;
        Ok(RootedLambdaPool { pool, root })
    }

    ///Reconstruct a [`RootedLambdaPool`] from an iterator of beads.
    ///
    ///# Panics
    ///Will panic if there is no root bead or multiple root beads.
    ///
    ///# Safety
    ///This version of the function does not check if the corresponding expression is wellformed.
    ///If the beads are not presented in the correct order, the resulting code may panic or loop
    ///indefinitely elsewhere.
    pub unsafe fn from_beads_unchecked(
        iter: impl IntoIterator<Item = ExpressionBead<'a, T>>,
    ) -> RootedLambdaPool<'a, T> {
        let mut root = None;
        let pool = LambdaPool(
            iter.into_iter()
                .filter_map(|x| match x.0 {
                    ExpressionBeadInner::Expr(lambda_expr) => Some(lambda_expr),
                    ExpressionBeadInner::Root(_) if root.is_some() => {
                        panic!("RootedLambdaPool can only have one root but the beads have multiple roots!");
                    }
                    ExpressionBeadInner::Root(x) => {
                        root = Some(x);
                        None
                    }
                })
                .collect::<Vec<_>>(),
        );
        let root = root.unwrap();
        RootedLambdaPool { pool, root }
    }
}

impl<'a, T: LambdaLanguageOfThought + Clone> RootedLambdaPool<'a, T> {
    ///Converts a [`RootedLambdaPool`] into beads for use in fancy data structures without
    ///ownership.
    pub fn as_beads(&self) -> impl Iterator<Item = ExpressionBead<'a, T>> {
        std::iter::once(ExpressionBead(ExpressionBeadInner::Root(self.root))).chain(
            self.pool
                .0
                .iter()
                .map(|x| ExpressionBead(ExpressionBeadInner::Expr(x.clone()))),
        )
    }
}
#[cfg(test)]
mod test {
    use super::{BeadError, ExpressionBeadInner};
    use crate::{lambda::RootedLambdaPool, language::Expr};

    const TEST_EXPR: [&str; 28] = [
        "a_john",
        "every(x, ~pa_a(x), every_e(y, pa_a(x), pe_e(y)))",
        "iota_e(x, ~(pa_a(a_john) | PatientOf(a_john, x)))",
        "iota_e(x, pe_e(x) | some_e(y, pa_a(a_john), pe_e(y)))",
        "lambda <e,a> P some(x, pa_a(a_john), pa_a(a_john))",
        "lambda a x lambda t phi ~(phi & ~~pa_a(a_john))",
        "iota(x, pe_e(iota_e(y, pe_e(y) | ~pa_a(x))))",
        "iota(x, pa_a(x))",
        "iota(x, some_e(y, ~pe_e(y), PatientOf(x, y)))",
        "iota_e(x, pa_a(a_john) | every_e(y, pe_e(y), AgentOf(a_john, x)))",
        "iota_e(x, pa_a(a_john) | ~pe_e(x))",
        "iota_e(x, ~pe_e(iota_e(y, pe_e(y) | pe_e(x))))",
        "iota_e(x, every_e(y, pe_e(x), pe_e(y)))",
        "iota(x, ~PatientOf(x, iota_e(y, pe_e(y))))",
        "iota_e(x, some_e(y, ~pe_e(y), ~pe_e(x)))",
        "lambda a x lambda a y ~pa_a(x) & ~pa_a(y)",
        "lambda a x lambda a y ~every_e(z, pa_a(y), AgentOf(x, z))",
        "lambda a x lambda a y AgentOf(x, iota_e(z, PatientOf(y, z)))",
        "lambda a x lambda a y ~some(z, all_a, ~pa_a(a_john))",
        "lambda a x lambda a y pa_a(iota(z, pa_a(y)))",
        "lambda a x lambda a y ~(pa_a(y) & pa_a(x))",
        "lambda a x lambda a y some(z, all_a, pa_a(y))",
        "lambda a x lambda a y AgentOf(a_john, iota_e(z, pa_a(a_john)))",
        "lambda a x lambda a y ~~(pa_a(x) | pa_a(y))",
        "lambda a x lambda a y ~pa_a(y) | pa_a(x) | pa_a(y)",
        "lambda a x lambda a y some(z, ~~pa_a(z), pa_a(a_john))",
        "lambda a x lambda a y every_e(z, pa_a(x), AgentOf(y, z))",
        "lambda a x lambda a y AgentOf(x, iota_e(z, ~AgentOf(y, z)))",
    ];

    #[test]
    fn bead_round_trip_into() -> Result<(), anyhow::Error> {
        for expr_str in TEST_EXPR {
            let original = RootedLambdaPool::parse(expr_str)?;
            let clone = original.clone();
            assert_eq!(clone, RootedLambdaPool::from_beads(original.into_beads())?);
        }
        Ok(())
    }

    #[test]
    fn bead_round_trip_as_beads() -> Result<(), anyhow::Error> {
        for expr_str in TEST_EXPR {
            let original = RootedLambdaPool::parse(expr_str)?;
            assert_eq!(original, RootedLambdaPool::from_beads(original.as_beads())?);
        }
        Ok(())
    }

    #[test]
    fn bead_round_trip_unchecked() -> Result<(), anyhow::Error> {
        for expr_str in TEST_EXPR {
            let original = RootedLambdaPool::parse(expr_str)?;
            let safe = RootedLambdaPool::from_beads(original.as_beads())?;
            let unchecked = unsafe { RootedLambdaPool::from_beads_unchecked(original.as_beads()) };
            assert_eq!(safe, unchecked);
        }
        Ok(())
    }

    #[test]
    fn bead_missing_root_error() -> Result<(), anyhow::Error> {
        for expr_str in TEST_EXPR {
            let original = RootedLambdaPool::parse(expr_str)?;
            let beads: Vec<_> = original
                .into_beads()
                .filter(|b| matches!(b.0, ExpressionBeadInner::Expr(_)))
                .collect();
            assert!(matches!(
                RootedLambdaPool::from_beads(beads),
                Err(BeadError::MissingRoot)
            ));
        }
        Ok(())
    }

    #[test]
    fn bead_multiple_roots_error() -> Result<(), anyhow::Error> {
        for expr_str in TEST_EXPR {
            let original = RootedLambdaPool::parse(expr_str)?;
            let mut beads: Vec<_> = original.into_beads().collect();
            let root_clone = beads
                .iter()
                .find(|b| matches!(b.0, ExpressionBeadInner::Root(_)))
                .unwrap()
                .clone();
            beads.push(root_clone);
            assert!(matches!(
                RootedLambdaPool::from_beads(beads),
                Err(BeadError::MultipleRoots)
            ));
        }
        Ok(())
    }

    #[test]
    fn bead_malformed_pool_error() -> Result<(), anyhow::Error> {
        for expr_str in TEST_EXPR {
            let original = RootedLambdaPool::parse(expr_str)?;
            let mut beads: Vec<_> = original.into_beads().collect();
            beads.retain(|b| matches!(b.0, ExpressionBeadInner::Root(_)));
            let result = RootedLambdaPool::from_beads(beads);
            if result.is_ok() {
                continue;
            }
            assert!(matches!(result, Err(BeadError::MalformedPool)));
        }
        Ok(())
    }

    #[test]
    fn bead_missing_root_empty_iterator() {
        assert!(matches!(
            RootedLambdaPool::<'static, Expr<'static>>::from_beads(std::iter::empty()),
            Err(BeadError::MissingRoot)
        ));
    }

    #[test]
    fn bead_root_position_invariance() -> Result<(), anyhow::Error> {
        for expr_str in TEST_EXPR {
            let original = RootedLambdaPool::parse(expr_str)?;
            let (root_beads, expr_beads): (Vec<_>, Vec<_>) = original
                .as_beads()
                .partition(|b| matches!(b.0, ExpressionBeadInner::Root(_)));
            let root_bead = root_beads.into_iter().next().unwrap();

            let mut end_order = expr_beads.clone();
            end_order.push(root_bead.clone());

            let mid = expr_beads.len() / 2;
            let mut mid_order = expr_beads.clone();
            mid_order.insert(mid, root_bead.clone());

            let mut start_order = expr_beads;
            start_order.insert(0, root_bead);

            let from_start = RootedLambdaPool::from_beads(start_order)?;
            assert_eq!(from_start, RootedLambdaPool::from_beads(mid_order)?);
            assert_eq!(from_start, RootedLambdaPool::from_beads(end_order)?);
        }
        Ok(())
    }

    #[test]
    #[should_panic(expected = "RootedLambdaPool can only have one root")]
    fn bead_unchecked_panics_on_multiple_roots() {
        let original = RootedLambdaPool::parse(TEST_EXPR[0]).unwrap();
        let mut beads: Vec<_> = original.into_beads().collect();
        let root_clone = beads
            .iter()
            .find(|b| matches!(b.0, ExpressionBeadInner::Root(_)))
            .unwrap()
            .clone();
        beads.push(root_clone);
        unsafe { RootedLambdaPool::from_beads_unchecked(beads) };
    }
}
