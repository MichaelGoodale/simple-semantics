use std::fmt::Display;

use anyhow::bail;
use chumsky::{
    extra::ParserExtra,
    label::LabelError,
    prelude::*,
    text::{TextExpected, inline_whitespace},
};
use rand::Rng;

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub enum LambdaType {
    #[default]
    A,
    E,
    T,
    Composition(Box<Self>, Box<Self>),
}

pub(crate) fn core_type_parser<'src, E>() -> impl Parser<'src, &'src str, LambdaType, E> + Clone
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>,
{
    let atom = choice((
        just('e').to(LambdaType::E),
        just('t').to(LambdaType::T),
        just('a').to(LambdaType::A),
    ));
    recursive(|expr| {
        atom.or((expr.clone().then_ignore(just(',').padded()).then(expr))
            .map(|(x, y)| LambdaType::Composition(Box::new(x), Box::new(y)))
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

    pub fn et() -> Self {
        LambdaType::Composition(Box::new(LambdaType::E), Box::new(LambdaType::T))
    }
    pub fn eet() -> Self {
        LambdaType::Composition(
            Box::new(LambdaType::E),
            Box::new(LambdaType::Composition(
                Box::new(LambdaType::E),
                Box::new(LambdaType::T),
            )),
        )
    }
    pub fn ett() -> Self {
        LambdaType::Composition(
            Box::new(LambdaType::Composition(
                Box::new(LambdaType::E),
                Box::new(LambdaType::T),
            )),
            Box::new(LambdaType::T),
        )
    }

    pub fn can_apply(&self, other: &Self) -> bool {
        match self {
            LambdaType::T | LambdaType::E | LambdaType::A => false,
            LambdaType::Composition(lhs, _) => **lhs == *other,
        }
    }

    pub fn apply_clone(self, other: &Self) -> anyhow::Result<Self> {
        if !self.can_apply(other) {
            bail!("Cannot apply {other} to {self}!")
        }

        match self {
            LambdaType::Composition(_, rhs) => Ok(*rhs),
            LambdaType::A | LambdaType::T | LambdaType::E => {
                bail!("Cannot apply to a primitive type")
            }
        }
    }

    pub fn split(self) -> anyhow::Result<(LambdaType, LambdaType)> {
        match self {
            LambdaType::Composition(a, b) => Ok((*a, *b)),
            LambdaType::A | LambdaType::E | LambdaType::T => bail!("Cannot split an atomic type"),
        }
    }

    pub fn apply(self, other: &Self) -> anyhow::Result<Self> {
        if !self.can_apply(other) {
            bail!("Cannot apply {other} to {self}!")
        }

        match self {
            LambdaType::Composition(_, rhs) => Ok(*rhs),
            LambdaType::A | LambdaType::T | LambdaType::E => {
                bail!("Cannot apply to a primitive type")
            }
        }
    }

    pub fn is_function(&self) -> bool {
        match self {
            LambdaType::Composition(..) => true,
            LambdaType::A | LambdaType::E | LambdaType::T => false,
        }
    }

    pub fn rhs_clone(&self) -> anyhow::Result<Self> {
        match self {
            LambdaType::Composition(_, rhs) => Ok(*rhs.clone()),
            LambdaType::A | LambdaType::E | LambdaType::T => bail!("Type clash!"),
        }
    }

    pub fn lhs_clone(&self) -> anyhow::Result<Self> {
        match self {
            LambdaType::Composition(lhs, ..) => Ok(*lhs.clone()),
            LambdaType::A | LambdaType::E | LambdaType::T => bail!("Type clash!"),
        }
    }
    pub fn lhs(self) -> anyhow::Result<Self> {
        match self {
            LambdaType::Composition(lhs, ..) => Ok(*lhs.clone()),
            LambdaType::A | LambdaType::E | LambdaType::T => bail!("Type clash!"),
        }
    }

    pub fn rhs(self) -> anyhow::Result<Self> {
        match self {
            LambdaType::Composition(_, rhs) => Ok(*rhs),
            LambdaType::A | LambdaType::E | LambdaType::T => bail!("Type clash!"),
        }
    }
}

impl Display for LambdaType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LambdaType::E => write!(f, "e"),
            LambdaType::T => write!(f, "t"),
            LambdaType::A => write!(f, "a"),
            LambdaType::Composition(lhs, rhs) => write!(f, "<{lhs},{rhs}>"),
        }
    }
}

impl LambdaType {
    pub fn random(r: &mut impl Rng) -> Self {
        let p: f64 = r.random();
        if p < 0.25 {
            LambdaType::E
        } else if p < 0.55 {
            LambdaType::A
        } else if p < 0.8 {
            LambdaType::T
        } else {
            LambdaType::Composition(
                Box::new(LambdaType::random(r)),
                Box::new(LambdaType::random(r)),
            )
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
        let et_to_et = LambdaType::Composition(Box::new(et.clone()), Box::new(et.clone()));
        let et_squared_to_et_squared =
            LambdaType::Composition(Box::new(et_to_et.clone()), Box::new(et_to_et.clone()));
        assert!(et.can_apply(&LambdaType::E));
        assert!(et_to_et.can_apply(&et));
        assert!(et_squared_to_et_squared.can_apply(&et_to_et));
        assert!(!et.can_apply(&LambdaType::T));
        assert!(!et_to_et.can_apply(&et_squared_to_et_squared));
        assert!(!et_squared_to_et_squared.can_apply(&et_squared_to_et_squared));

        assert_eq!(et_to_et, et_squared_to_et_squared.clone().rhs()?);
        assert_eq!(et_to_et, et_squared_to_et_squared.rhs_clone()?);

        assert_eq!(et, et_to_et.clone().rhs()?);
        assert_eq!(et, et_to_et.rhs_clone()?);

        assert_eq!(LambdaType::T, et.clone().rhs()?);
        assert_eq!(LambdaType::T, et.rhs_clone()?);
        Ok(())
    }

    #[test]
    fn parse_types() {
        let parser = type_parser();
        assert_eq!(parser.parse("e").unwrap(), LambdaType::E);
        assert_eq!(parser.parse(" e ").unwrap(), LambdaType::E);
        assert_eq!(parser.parse("e  ").unwrap(), LambdaType::E);
        assert!(parser.parse("e  z").has_errors());

        assert_eq!(parser.parse("t").unwrap(), LambdaType::T);

        let et = LambdaType::et();
        assert_eq!(parser.parse("<e, t>").unwrap(), et);

        let et_to_et = LambdaType::Composition(Box::new(et.clone()), Box::new(et));

        assert_eq!(parser.parse("<<e, t>, <e,t>>").unwrap(), et_to_et);

        let et_squared_to_et_squared =
            LambdaType::Composition(Box::new(et_to_et.clone()), Box::new(et_to_et));
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
