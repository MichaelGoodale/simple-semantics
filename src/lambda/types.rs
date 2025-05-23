use std::{fmt::Display, sync::LazyLock};

use anyhow::bail;
use chumsky::{
    extra::ParserExtra,
    label::LabelError,
    prelude::*,
    text::{TextExpected, inline_whitespace},
};
use rand::Rng;

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub enum InnerLambdaType {
    #[default]
    A,
    E,
    T,
    Composition,
}

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct LambdaType(Vec<Option<InnerLambdaType>>);

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

fn type_parser<'a>() -> impl Parser<'a, &'a str, LambdaType> + Clone {
    core_type_parser().padded().then_ignore(end())
}

impl LambdaType {
    pub fn from_string(s: &str) -> anyhow::Result<Self> {
        type_parser().parse(s).into_result().map_err(|x| {
            anyhow::anyhow!(
                x.into_iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(",")
            )
        })
    }

    pub fn a() -> &'static Self {
        static A: LazyLock<LambdaType> =
            LazyLock::new(|| LambdaType(vec![Some(InnerLambdaType::A)]));
        &*A
    }
    pub fn e() -> &'static Self {
        static E: LazyLock<LambdaType> =
            LazyLock::new(|| LambdaType(vec![Some(InnerLambdaType::E)]));
        &*E
    }

    pub fn t() -> &'static Self {
        static T: LazyLock<LambdaType> =
            LazyLock::new(|| LambdaType(vec![Some(InnerLambdaType::T)]));
        &*T
    }

    pub fn compose(a: Self, b: Self) -> Self {
        todo!();
    }

    pub fn at() -> &'static Self {
        static VAL: LazyLock<LambdaType> = LazyLock::new(|| {
            LambdaType(vec![
                Some(InnerLambdaType::Composition),
                Some(InnerLambdaType::A),
                Some(InnerLambdaType::T),
            ])
        });
        &VAL
    }

    pub fn et() -> &'static Self {
        static VAL: LazyLock<LambdaType> =
            LazyLock::new(|| LambdaType::compose(LambdaType::e().clone(), LambdaType::t().clone()));
        &VAL
    }
    pub fn eet() -> Self {
        LambdaType::compose(
            LambdaType::e().clone(),
            LambdaType::compose(LambdaType::e().clone(), LambdaType::t().clone()),
        )
    }
    pub fn ett() -> Self {
        LambdaType::compose(
            LambdaType::compose(LambdaType::e().clone(), LambdaType::t().clone()),
            LambdaType::t().clone(),
        )
    }

    pub fn can_apply(&self, other: &Self) -> bool {
        todo!();
    }

    pub fn apply_clone(self, other: &Self) -> anyhow::Result<Self> {
        if !self.can_apply(other) {
            bail!("Cannot apply {other} to {self}!")
        }

        todo!();
    }

    pub fn split(&self) -> anyhow::Result<(&LambdaType, &LambdaType)> {
        todo!();
    }

    pub fn apply(self, other: &Self) -> anyhow::Result<Self> {
        if !self.can_apply(other) {
            bail!("Cannot apply {other} to {self}!")
        }

        todo!();
    }

    pub fn is_function(&self) -> bool {
        self.0.len() > 1
    }

    pub fn rhs_clone(&self) -> anyhow::Result<Self> {
        todo!();
    }

    pub fn lhs_clone(&self) -> anyhow::Result<Self> {
        todo!();
    }
    pub fn lhs(self) -> anyhow::Result<Self> {
        todo!();
    }

    pub fn rhs(self) -> anyhow::Result<Self> {
        todo!();
    }
}

impl Display for LambdaType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!();
        /*
        match self {
            LambdaType::E => write!(f, "e"),
            LambdaType::T => write!(f, "t"),
            LambdaType::A => write!(f, "a"),
            LambdaType::Composition(lhs, rhs) => write!(f, "<{lhs},{rhs}>"),
        }*/
    }
}

impl LambdaType {
    pub fn random(r: &mut impl Rng) -> Self {
        let p: f64 = r.random();
        if p < 0.25 {
            LambdaType::e().clone()
        } else if p < 0.55 {
            LambdaType::a().clone()
        } else if p < 0.8 {
            LambdaType::t().clone()
        } else {
            LambdaType::compose(LambdaType::random(r), LambdaType::random(r))
        }
    }

    ///Returns a random type, except for ``LambdaType::E``
    pub fn random_no_e(r: &mut impl Rng) -> Self {
        let p: f64 = r.random();
        if p < 0.4 {
            LambdaType::e().clone()
        } else if p < 0.8 {
            LambdaType::t().clone()
        } else {
            LambdaType::compose(LambdaType::random(r), LambdaType::random_no_e(r))
        }
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
        for _ in 0..100 {
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
        assert!(et_to_et.can_apply(&et));
        assert!(et_squared_to_et_squared.can_apply(&et_to_et));
        assert!(!et.can_apply(LambdaType::t()));
        assert!(!et_to_et.can_apply(&et_squared_to_et_squared));
        assert!(!et_squared_to_et_squared.can_apply(&et_squared_to_et_squared));

        assert_eq!(et_to_et, et_squared_to_et_squared.clone().rhs()?);
        assert_eq!(et_to_et, et_squared_to_et_squared.rhs_clone()?);

        assert_eq!(et, &et_to_et.clone().rhs()?);
        assert_eq!(et, &et_to_et.rhs_clone()?);

        assert_eq!(LambdaType::t(), &et.clone().rhs()?);
        assert_eq!(LambdaType::t(), &et.rhs_clone()?);
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
