//! Defines the basic type system of the lambda calculus
use chumsky::{
    extra::ParserExtra,
    label::LabelError,
    prelude::*,
    text::{TextExpected, inline_whitespace},
};
#[cfg(feature = "sampling")]
use rand::{Rng, RngExt, seq::IteratorRandom};
use std::{fmt::Display, sync::LazyLock};
use thiserror::Error;

///Unable to parse a type.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub struct TypeParsingError(String);

impl From<Vec<Rich<'_, char>>> for TypeParsingError {
    fn from(value: Vec<Rich<'_, char>>) -> Self {
        TypeParsingError(
            value
                .iter()
                .map(std::string::ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n"),
        )
    }
}

impl Display for TypeParsingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone, Error, PartialEq, Eq)]
///An error from applying types incorrectly.
pub enum TypeError {
    ///Trying to split a primitive type into two.
    #[error("Cannot split a primitive type")]
    NotAFunction,
    ///Applying a something of the wrong type to something else.
    #[error("Cannot apply {0} to {1}!")]
    CantApply(LambdaType, LambdaType),
}

#[derive(Debug, Clone, Eq, PartialEq, Default, Hash, PartialOrd, Ord)]
///The basic type system of the lambda calculus and LOT.
pub enum LambdaType {
    #[default]
    ///A type for [`crate::Actor`]s
    A,
    ///A type for [`crate::Event`]s
    E,
    ///A type for truth values.
    T,
    ///A type for functions
    Composition(Box<LambdaType>, Box<LambdaType>),
}

pub(crate) fn core_type_parser<'src, E>()
-> impl Parser<'src, &'src str, LambdaType, E> + Clone + 'src
where
    E: ParserExtra<'src, &'src str> + 'src,
    E::Error: LabelError<'src, &'src str, TextExpected<&'src str>>,
    E::Error: LabelError<'src, &'src str, TextExpected<()>>,
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

#[derive(Debug, Clone, PartialEq, Eq)]
///A struct which recursively gets the right hand side of a given lambda expression
pub struct RetrievableTypeIterator<'a>(&'a LambdaType);

impl<'a> Iterator for RetrievableTypeIterator<'a> {
    type Item = (&'a LambdaType, &'a LambdaType);

    fn next(&mut self) -> Option<Self::Item> {
        match self.0.split() {
            Ok((lhs, rhs)) => {
                self.0 = rhs;
                Some((lhs, rhs))
            }
            Err(_) => None,
        }
    }
}

impl LambdaType {
    ///Takes a type x and returns <<x,t>, t>
    #[must_use]
    pub fn lift_type(self) -> LambdaType {
        let t = LambdaType::compose(self, LambdaType::T);

        LambdaType::compose(t, LambdaType::T)
    }

    ///Get all types which can be created from this type (what you would need to pass before to produce
    ///that type).
    ///
    ///### Examples
    /// - <a,t> can create t (arg: a)
    /// - <a,<a,t>> can create t: (arg: a) or <a,t> (arg: a)
    /// - <a, <<a,t>, <t,t>>> can create <<a,t>, <t,t>> (arg: a), <t,t> (arg: <a,t>) or t
    ///
    ///```
    ///# use simple_semantics::lambda::types::LambdaType;
    ///let x = LambdaType::from_string("<a, <<a,t>, <t,t>>>")?
    ///    .retrievable_types()
    ///    .map(|(_, x)| x.to_string())
    ///    .collect::<Vec<_>>();
    ///assert_eq!(x, vec!["<<a,t>,<t,t>>", "<t,t>", "t"]);
    ///# Ok::<(), anyhow::Error>(())
    ///```
    ///
    #[must_use]
    pub fn retrievable_types(&self) -> RetrievableTypeIterator<'_> {
        RetrievableTypeIterator(self)
    }

    ///Checks if the type is the lifted version of another.
    #[must_use]
    pub fn is_lifted_type_of(&self, t: &LambdaType) -> bool {
        let Ok((a, LambdaType::T)) = self.split() else {
            return false;
        };
        let Ok((a, LambdaType::T)) = a.split() else {
            return false;
        };

        a == t
    }

    ///Takes a type t and argument x and returns <t, x>
    pub fn add_right_argument(&mut self, other: LambdaType) {
        let mut t = LambdaType::A;
        std::mem::swap(&mut t, self);
        *self = LambdaType::Composition(Box::new(t), Box::new(other));
    }
    ///Takes a type t and argument x and returns <x, t>
    pub fn add_left_argument(&mut self, other: LambdaType) {
        let mut t = LambdaType::A;
        std::mem::swap(&mut t, self);
        *self = LambdaType::Composition(Box::new(other), Box::new(t));
    }

    ///Parse a type
    ///
    ///```
    ///# use simple_semantics::lambda::types::LambdaType;
    /////Create a type of e to e to t.
    ///let x = LambdaType::from_string("<e,<e,t>>")?;
    ///# Ok::<(), anyhow::Error>(())
    ///```
    ///
    ///# Errors
    ///Returns a [`TypeParsingError`] if the string is malformed and doesn't represent a type.
    pub fn from_string(s: &str) -> Result<Self, TypeParsingError> {
        type_parser()
            .parse(s)
            .into_result()
            .map_err(std::convert::Into::into)
    }

    ///Get the atomic type `a`
    #[must_use]
    pub fn a() -> &'static Self {
        &LambdaType::A
    }

    ///get the atomic type `e`
    #[must_use]
    pub fn e() -> &'static Self {
        &LambdaType::E
    }

    ///Get the atomic type `t`
    #[must_use]
    pub fn t() -> &'static Self {
        &LambdaType::T
    }

    ///Compose two functions
    #[must_use]
    pub fn compose(a: Self, b: Self) -> Self {
        LambdaType::Composition(Box::new(a), Box::new(b))
    }

    ///Get the `a` to `t` function type.
    #[must_use]
    pub fn at() -> &'static Self {
        static VAL: LazyLock<LambdaType> =
            LazyLock::new(|| LambdaType::compose(LambdaType::a().clone(), LambdaType::t().clone()));
        &VAL
    }

    ///Get the `e` to `t` function type.
    #[must_use]
    pub fn et() -> &'static Self {
        static VAL: LazyLock<LambdaType> =
            LazyLock::new(|| LambdaType::compose(LambdaType::e().clone(), LambdaType::t().clone()));
        &VAL
    }

    ///Get the `<e,<e,t>>` function type
    #[must_use]
    pub fn eet() -> &'static Self {
        static VAL: LazyLock<LambdaType> = LazyLock::new(|| {
            LambdaType::compose(
                LambdaType::e().clone(),
                LambdaType::compose(LambdaType::e().clone(), LambdaType::t().clone()),
            )
        });
        &VAL
    }
    ///Get the `<<e,t>, t>` function type
    #[must_use]
    pub fn ett() -> &'static Self {
        static VAL: LazyLock<LambdaType> = LazyLock::new(|| {
            LambdaType::compose(
                LambdaType::compose(LambdaType::e().clone(), LambdaType::t().clone()),
                LambdaType::t().clone(),
            )
        });
        &VAL
    }

    ///The number of elements in this type
    #[must_use]
    pub fn size(&self) -> usize {
        match self {
            LambdaType::A | LambdaType::E | LambdaType::T => 1,
            LambdaType::Composition(a, b) => a.size() + b.size(),
        }
    }

    ///Check if `self` can have `other` applied to it.
    #[must_use]
    pub fn can_apply(&self, other: &Self) -> bool {
        matches!(&self, LambdaType::Composition(a, _) if a.as_ref() == other)
    }

    ///Split a function type into input and output.
    ///
    ///# Errors
    ///Returns a [`TypeError`] if the type is not a function.
    pub fn split(&self) -> Result<(&LambdaType, &LambdaType), TypeError> {
        match &self {
            LambdaType::Composition(a, b) => Ok((a, b)),
            _ => Err(TypeError::NotAFunction),
        }
    }

    ///Applies a function type to self.
    ///
    ///# Errors
    ///Returns a [`TypeError`] if the type is not the right type
    ///for the function.
    pub fn apply(&self, other: &Self) -> Result<&Self, TypeError> {
        if !self.can_apply(other) {
            return Err(TypeError::CantApply(other.clone(), self.clone()));
        }
        self.rhs()
    }

    ///Checks that the type is a function.
    #[must_use]
    pub fn is_function(&self) -> bool {
        matches!(&self, LambdaType::Composition(_, _))
    }

    ///Get the left-hand side of a function.
    ///
    ///# Errors
    ///Returns a [`TypeError`] if the type is not a function.
    pub fn lhs(&self) -> Result<&Self, TypeError> {
        Ok(self.split()?.0)
    }

    ///Checks if the type takes a primitive type and returns a primitive type
    #[must_use]
    pub fn is_one_place_function(&self) -> bool {
        if let Ok((lhs, rhs)) = self.split() {
            !lhs.is_function() && !rhs.is_function()
        } else {
            false
        }
    }

    ///Get the right-hand side of a function.
    ///
    ///# Errors
    ///Returns a [`TypeError`] if the type is not a function.
    pub fn rhs(&self) -> Result<&Self, TypeError> {
        Ok(self.split()?.1)
    }
}

impl Display for LambdaType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            LambdaType::E => write!(f, "e"),
            LambdaType::T => write!(f, "t"),
            LambdaType::A => write!(f, "a"),
            LambdaType::Composition(lhs, rhs) => write!(f, "<{lhs},{rhs}>"),
        }
    }
}

#[cfg(feature = "sampling")]
const RECURSE_PROB: f64 = 0.2;
#[cfg(feature = "sampling")]
const MAX_DEPTH: u8 = 64;

#[cfg(feature = "sampling")]
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

    ///Get a random lambda type.
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

    #[cfg(feature = "sampling")]
    use rand::SeedableRng;
    #[cfg(feature = "sampling")]
    use rand_chacha::ChaCha8Rng;

    use super::*;

    #[cfg(feature = "sampling")]
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

    #[test]
    fn check_lifting() -> anyhow::Result<()> {
        for s in ["e", "t", "<e,t>", "<e,<e,t>>", "<t,<<t,t>,<e,t>>>"] {
            let lifted_str = format!("<<{s},t>,t>");
            let lifted = LambdaType::from_string(&lifted_str)?;
            let base_type = LambdaType::from_string(s)?;
            assert!(lifted.is_lifted_type_of(&base_type));
            assert_eq!(base_type.lift_type(), lifted);
        }

        Ok(())
    }
}
