use std::{fmt::Display, sync::LazyLock};

use chumsky::{
    extra::ParserExtra,
    label::LabelError,
    prelude::*,
    text::{TextExpected, inline_whitespace},
};
use rand::{Rng, seq::IteratorRandom};

use thiserror::Error;

use crate::ChumskyParsingError;

#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum TypeError {
    #[error("Cannot split a primitive type")]
    NotAFunction,
    #[error("Cannot apply {0} to {1}!")]
    CantApply(LambdaType, LambdaType),
}

#[derive(Debug, Clone, Eq, PartialEq, Default, Hash)]
pub enum InnerLambdaType {
    #[default]
    A,
    E,
    T,
    Composition(Box<LambdaType>, Box<LambdaType>),
}

#[derive(Debug, Clone, Eq, PartialEq, Default, Hash)]
pub struct LambdaType(InnerLambdaType);

/*
#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct LambdaType(Vec<Option<InnerLambdaType>>);
*/

pub(crate) fn core_type_parser<'src, E>() -> impl Parser<'src, &'src str, LambdaType, E> + Clone
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>,
{
    let atom = choice((
        just('e').to(LambdaType::e().clone()),
        just('t').to(LambdaType::t().clone()),
        just('a').to(LambdaType::a().clone()),
    ));
    recursive(|expr| {
        atom.or((expr.clone().then_ignore(just(',').padded()).then(expr))
            .map(|(x, y)| LambdaType::compose(x, y))
            .delimited_by(
                just('<').then(inline_whitespace()),
                inline_whitespace().then(just('>')),
            ))
    })
}

fn type_parser<'a>() -> impl Parser<'a, &'a str, LambdaType, extra::Err<Rich<'a, char>>> + Clone {
    core_type_parser().padded().then_ignore(end())
}

impl LambdaType {
    pub fn from_string<'a>(s: &'a str) -> Result<Self, ChumskyParsingError<'a>> {
        type_parser().parse(s).into_result().map_err(|x| x.into())
    }

    pub fn a() -> &'static Self {
        static A: LazyLock<LambdaType> = LazyLock::new(|| LambdaType(InnerLambdaType::A));
        &A
    }
    pub fn e() -> &'static Self {
        static E: LazyLock<LambdaType> = LazyLock::new(|| LambdaType(InnerLambdaType::E));
        &E
    }

    pub fn t() -> &'static Self {
        static T: LazyLock<LambdaType> = LazyLock::new(|| LambdaType(InnerLambdaType::T));
        &T
    }

    pub fn compose(a: Self, b: Self) -> Self {
        LambdaType(InnerLambdaType::Composition(Box::new(a), Box::new(b)))
    }

    pub fn at() -> &'static Self {
        static VAL: LazyLock<LambdaType> =
            LazyLock::new(|| LambdaType::compose(LambdaType::a().clone(), LambdaType::t().clone()));
        &VAL
    }

    pub fn et() -> &'static Self {
        static VAL: LazyLock<LambdaType> =
            LazyLock::new(|| LambdaType::compose(LambdaType::e().clone(), LambdaType::t().clone()));
        &VAL
    }
    pub fn eet() -> &'static Self {
        static VAL: LazyLock<LambdaType> = LazyLock::new(|| {
            LambdaType::compose(
                LambdaType::e().clone(),
                LambdaType::compose(LambdaType::e().clone(), LambdaType::t().clone()),
            )
        });
        &VAL
    }
    pub fn ett() -> &'static Self {
        static VAL: LazyLock<LambdaType> = LazyLock::new(|| {
            LambdaType::compose(
                LambdaType::compose(LambdaType::e().clone(), LambdaType::t().clone()),
                LambdaType::t().clone(),
            )
        });
        &VAL
    }

    pub fn can_apply(&self, other: &Self) -> bool {
        matches!(&self.0, InnerLambdaType::Composition(a, _) if a.as_ref() == other)
    }

    pub fn split(&self) -> Result<(&LambdaType, &LambdaType), TypeError> {
        match &self.0 {
            InnerLambdaType::Composition(a, b) => Ok((a, b)),
            _ => Err(TypeError::NotAFunction),
        }
    }

    pub fn apply(&self, other: &Self) -> Result<&Self, TypeError> {
        if !self.can_apply(other) {
            return Err(TypeError::CantApply(other.clone(), self.clone()));
        }
        self.rhs()
    }

    pub fn is_function(&self) -> bool {
        matches!(&self.0, InnerLambdaType::Composition(_, _))
    }

    pub fn lhs(&self) -> Result<&Self, TypeError> {
        Ok(self.split()?.0)
    }

    pub fn rhs(&self) -> Result<&Self, TypeError> {
        Ok(self.split()?.1)
    }
}

impl Display for LambdaType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            InnerLambdaType::E => write!(f, "e"),
            InnerLambdaType::T => write!(f, "t"),
            InnerLambdaType::A => write!(f, "a"),
            InnerLambdaType::Composition(lhs, rhs) => write!(f, "<{lhs},{rhs}>"),
        }
    }
}

const RECURSE_PROB: f64 = 0.2;
const MAX_DEPTH: u8 = 64;

impl LambdaType {
    fn random_inner(r: &mut impl Rng, depth: u8, no_e: bool) -> Self {
        if depth < MAX_DEPTH && r.random_bool(RECURSE_PROB) {
            LambdaType::compose(
                LambdaType::random_inner(r, depth + 1, false),
                LambdaType::random_inner(r, depth + 1, no_e),
            )
        } else if no_e {
            if r.random_bool(0.5) {
                LambdaType::t().clone()
            } else {
                LambdaType::a().clone()
            }
        } else {
            let i = (0..3).choose(r).unwrap();
            [LambdaType::t(), LambdaType::a(), LambdaType::e()][i].clone()
        }
    }

    pub fn random(r: &mut impl Rng) -> Self {
        LambdaType::random_inner(r, 0, false)
    }

    ///Returns a random type, except for ``LambdaType::E``
    pub fn random_no_e(r: &mut impl Rng) -> Self {
        LambdaType::random_inner(r, 0, true)
    }
}

#[cfg(test)]
mod test {
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    use super::*;

    #[test]
    fn random_lambdas() -> anyhow::Result<()> {
        let mut r = ChaCha8Rng::seed_from_u64(32);
        for _ in 0..10_000 {
            let t = LambdaType::random(&mut r);
            println!("{t}");
        }
        Ok(())
    }

    #[test]
    fn check_application() -> anyhow::Result<()> {
        let et = LambdaType::et();
        let et_to_et = LambdaType::compose(et.clone(), et.clone());
        let et_squared_to_et_squared = LambdaType::compose(et_to_et.clone(), et_to_et.clone());
        assert!(et.can_apply(LambdaType::e()));
        assert!(et_to_et.can_apply(et));
        assert!(et_squared_to_et_squared.can_apply(&et_to_et));
        assert!(!et.can_apply(LambdaType::t()));
        assert!(!et_to_et.can_apply(&et_squared_to_et_squared));
        assert!(!et_squared_to_et_squared.can_apply(&et_squared_to_et_squared));

        assert_eq!(&et_to_et, et_squared_to_et_squared.rhs()?);

        assert_eq!(et, et_to_et.rhs()?);

        assert_eq!(LambdaType::t(), et.rhs()?);
        Ok(())
    }

    #[test]
    fn parse_types() {
        let parser = type_parser();
        assert_eq!(&parser.parse("e").unwrap(), LambdaType::e());
        assert_eq!(&parser.parse(" e ").unwrap(), LambdaType::e());
        assert_eq!(&parser.parse("e  ").unwrap(), LambdaType::e());
        assert!(parser.parse("e  z").has_errors());

        assert_eq!(&parser.parse("t").unwrap(), LambdaType::t());

        let et = LambdaType::et();
        assert_eq!(&parser.parse("<e, t>").unwrap(), et);

        let et_to_et = LambdaType::compose(et.clone(), et.clone());

        assert_eq!(parser.parse("<<e, t>, <e,t>>").unwrap(), et_to_et);

        let et_squared_to_et_squared = LambdaType::compose(et_to_et.clone(), et_to_et);
        assert_eq!(
            parser.parse("<< <e, t>, <e,t>>, <<e,t>, <e,t>>>").unwrap(),
            et_squared_to_et_squared
        );
    }

    #[test]
    fn check_printing() {
        let parser = type_parser();
        for s in ["e", "t", "<e,t>", "<e,<e,t>>", "<t,<<t,t>,<e,t>>>"] {
            assert_eq!(parser.parse(s).unwrap().to_string(), s);
        }
    }
}
