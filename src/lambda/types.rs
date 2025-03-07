use chumsky::prelude::*;

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub enum LambdaType {
    #[default]
    E,
    T,
    Composition(Box<Self>, Box<Self>),
}

fn type_parser<'a>() -> impl Parser<'a, &'a str, LambdaType> {
    let atom = choice((just('e').to(LambdaType::E), just('t').to(LambdaType::T)));
    let composition = recursive(|expr| {
        atom.or((expr.clone().then_ignore(just(',').padded()).then(expr))
            .map(|(x, y)| LambdaType::Composition(Box::new(x), Box::new(y)))
            .delimited_by(just('<'), just('>')))
            .padded()
    });
    composition.then_ignore(end())
}

impl LambdaType {
    pub fn from_string(s: &str) -> anyhow::Result<Self> {
        type_parser().parse(s).into_result().map_err(|x| {
            anyhow::anyhow!(x
                .into_iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join(","))
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

    pub fn can_apply(&self, other: &Self) -> bool {
        match self {
            LambdaType::T | LambdaType::E => false,
            LambdaType::Composition(lhs, _) => **lhs == *other,
        }
    }

    pub fn apply_clone(&self) -> Self {
        match self {
            LambdaType::Composition(_, rhs) => *rhs.clone(),
            LambdaType::E | LambdaType::T => panic!("Type clash!"),
        }
    }

    pub fn apply(self) -> Self {
        match self {
            LambdaType::Composition(_, rhs) => *rhs,
            LambdaType::E | LambdaType::T => panic!("Type clash!"),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn check_application() {
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

        assert_eq!(et_to_et, et_squared_to_et_squared.clone().apply());
        assert_eq!(et_to_et, et_squared_to_et_squared.apply_clone());

        assert_eq!(et, et_to_et.clone().apply());
        assert_eq!(et, et_to_et.apply_clone());

        assert_eq!(LambdaType::T, et.clone().apply());
        assert_eq!(LambdaType::T, et.apply_clone());
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
            parser.parse("<<<e, t>, <e,t>>, <<e,t>, <e,t>>>").unwrap(),
            et_squared_to_et_squared
        );
    }
}
