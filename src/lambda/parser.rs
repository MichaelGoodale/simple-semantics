use crate::{
    lambda::{
        Bvar, ExprType, FreeVar, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool,
        ReductionError, RootedLambdaPool,
        types::{LambdaType, TypeError, core_type_parser},
    },
    language::Expr,
};
use chumsky::{
    extra::ParserExtra,
    input::ValueInput,
    label::LabelError,
    pratt::prefix,
    prelude::*,
    text::{TextExpected, inline_whitespace},
    util::MaybeRef,
};
use std::{
    collections::{HashMap, VecDeque},
    fmt::{Debug, Display},
};

use thiserror::Error;

///Error in parsing a lambda expression
#[derive(Debug, Error, Clone)]
pub enum LambdaParseError {
    ///Core error in parsing
    #[error("ParseError({0})")]
    ParseError(String),

    ///A free variable was left untyped
    #[error("You must provide a type for unbound free variable {0} like so \"{0}#<e,t>\"")]
    UnTypedFreeVariable(String),

    ///When the expression was reduced, it lead to an error.
    #[error("Reduction Error: {0}")]
    ReductionError(#[from] ReductionError),

    ///There is a type error in  apply function types
    #[error("{0}")]
    TypeError(String),

    ///Type error in lower part
    #[error("Type error: {0}")]
    InnerTypeError(#[from] TypeError),
}

impl<'a, T: Display> From<Vec<Rich<'a, T>>> for LambdaParseError {
    fn from(value: Vec<Rich<'a, T>>) -> Self {
        LambdaParseError::ParseError(
            value
                .into_iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join("\n"),
        )
    }
}

impl<'src, T: LambdaLanguageOfThought> RootedLambdaPool<'src, T> {
    pub fn parse(s: &'src str) -> Result<RootedLambdaPool<'src, T>, LambdaParseError> {
        todo!()
    }
}

impl<'src, T: LambdaLanguageOfThought> ParseTree<'src, T> {
    fn add_to_pool(
        self,
        pool: &mut LambdaPool<'src, T>,
        variable_names: &mut VariableContext<'src>,
        lambda_depth: usize,
    ) -> Result<LambdaExprRef, LambdaParseError> {
        let expr: LambdaExpr<'src, T> = match self {
            ParseTree::Application {
                subformula,
                argument,
            } => {
                let subformula = subformula.add_to_pool(pool, variable_names, lambda_depth)?;
                let argument = argument.add_to_pool(pool, variable_names, lambda_depth)?;

                let f = pool.get_type(subformula)?;
                let arg = pool.get_type(argument)?;

                if !f.can_apply(&arg) {
                    return Err(LambdaParseError::TypeError(
                        "Can't apply subformula to argument".to_string(),
                    ));
                }

                LambdaExpr::Application {
                    subformula,
                    argument,
                }
            }
            ParseTree::Lambda {
                body,
                var,
                lambda_type,
            } => {
                variable_names.bind_var(var, lambda_depth + 1, lambda_type.clone());
                let body = body.add_to_pool(pool, variable_names, lambda_depth + 1)?;
                variable_names.unbind(var);
                LambdaExpr::Lambda(body, lambda_type.clone())
            }
            ParseTree::Variable(var) => variable_names.to_expr(var, None, lambda_depth)?,
            ParseTree::FreeVariable(var, lambda_type) => {
                variable_names.to_expr(var, Some(lambda_type.clone()), lambda_depth)?
            }
            ParseTree::LanguageOfThoughtExpr(e) => {
                LambdaExpr::LanguageOfThoughtExpr(e, ExprType::NoVar)
            }
            ParseTree::LanguageOfThoughtExprBindOne(..)
            | ParseTree::LanguageOfThoughtExprBindTwo(..) => todo!(),
        };
        Ok(pool.add(expr))
    }

    fn into_pool(self) -> Result<RootedLambdaPool<'src, T>, LambdaParseError> {
        let mut pool = LambdaPool::new();

        let mut var_labels = VariableContext::default();
        let root = self.add_to_pool(&mut pool, &mut var_labels, 0)?;
        Ok(RootedLambdaPool::new(pool, root))
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Default)]
struct VariableContext<'src>(HashMap<&'src str, Vec<(Bvar, LambdaType)>>, u32);

impl<'src> VariableContext<'src> {
    fn to_expr<T>(
        &self,
        variable: &'src str,
        lambda_type: Option<LambdaType>,
        lambda_depth: usize,
    ) -> Result<LambdaExpr<'src, T>, LambdaParseError> {
        Ok(match self.0.get(variable) {
            Some(vars) if !vars.is_empty() => {
                let (og_depth, lambda_type) = vars
                    .last()
                    .expect("There should never be an empty vec in the VariableContext");
                LambdaExpr::BoundVariable(lambda_depth - og_depth, lambda_type.clone())
            }
            //Do free var
            _ => match lambda_type {
                Some(lambda_type) => {
                    let free_var = variable
                        .parse::<usize>()
                        .map_or(FreeVar::Named(variable), FreeVar::Anonymous);

                    LambdaExpr::FreeVariable(free_var, lambda_type)
                }
                None => {
                    return Err(LambdaParseError::UnTypedFreeVariable(variable.to_string()));
                }
            },
        })
    }

    fn bind_var(&mut self, variable: &'src str, lambda_depth: usize, lambda_type: LambdaType) {
        self.0
            .entry(variable)
            .or_default()
            .push((lambda_depth, lambda_type));
    }

    fn unbind(&mut self, variable: &'src str) {
        self.0.get_mut(variable).unwrap().pop();
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum ParseTree<'src, T> {
    Lambda {
        body: Box<ParseTree<'src, T>>,
        lambda_type: LambdaType,
        var: &'src str,
    },
    Variable(&'src str),
    FreeVariable(&'src str, LambdaType),
    Application {
        subformula: Box<ParseTree<'src, T>>,
        argument: Box<ParseTree<'src, T>>,
    },
    LanguageOfThoughtExpr(T),
    LanguageOfThoughtExprBindOne(T, Box<ParseTree<'src, T>>),
    LanguageOfThoughtExprBindTwo(T, Box<ParseTree<'src, T>>, Box<ParseTree<'src, T>>),
}

fn keyword<'src, E>() -> impl Parser<'src, &'src str, &'src str, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
{
    one_of("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-")
        .repeated()
        .at_least(1)
        .to_slice()
}

type ChumskyErr<'tokens, 'src> = extra::Err<Rich<'tokens, Token<'src>, Span>>;

#[derive(Debug, Clone, Eq, PartialEq)]
enum Token<'src> {
    OpenDelim,
    ArgSep,
    CloseDelim,
    Lambda(LambdaType, &'src str),
    Variable(&'src str),
    FreeVariable(&'src str, LambdaType),
    LanguageOfThoughtToken,
}
impl Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::OpenDelim => write!(f, "("),
            Token::ArgSep => write!(f, ","),
            Token::CloseDelim => write!(f, ")"),
            Token::Lambda(lambda_type, t) => write!(f, "lambda {lambda_type} {t}"),
            Token::Variable(v) => write!(f, "{v}"),
            Token::FreeVariable(v, lambda_type) => write!(f, "{v}#{lambda_type}"),
            Token::LanguageOfThoughtToken => todo!(),
        }
    }
}

pub type Span = SimpleSpan;
pub type Spanned<T> = (T, Span);

fn lexer<'src, E>() -> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, E>
where
    E: ParserExtra<'src, &'src str> + 'src,
    E::Error: LabelError<'src, &'src str, TextExpected<&'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>
        + LabelError<'src, &'src str, &'static str>
        + LabelError<'src, &'src str, TextExpected<()>>,
{
    choice((
        just(',').to(Token::ArgSep),
        just('(').to(Token::OpenDelim),
        just(')').to(Token::CloseDelim),
        just("lambda")
            .then(inline_whitespace().at_least(1))
            .ignore_then(core_type_parser())
            .then_ignore(inline_whitespace().at_least(1))
            .then(keyword())
            .then_ignore(inline_whitespace().at_least(1))
            .map(|(t, x)| Token::Lambda(t, x)),
        keyword()
            .then(just("#").ignore_then(core_type_parser()).or_not())
            .map(|(var, lambda_type)| {
                if let Some(t) = lambda_type {
                    Token::FreeVariable(var, t)
                } else {
                    Token::Variable(var)
                }
            }),
    ))
    .map_with(|t, e| (t, e.span()))
    .padded()
    .repeated()
    .collect()
}

fn language_parser<'tokens, 'src: 'tokens, I, T>()
-> impl Parser<'tokens, I, ParseTree<'src, T>, extra::Err<Rich<'tokens, Token<'src>, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = SimpleSpan> + Clone,
    T: 'tokens,
{
    let var = select! {
        Token::Variable(a) => ParseTree::Variable(a),
        Token::FreeVariable(a, t) => ParseTree::FreeVariable(a, t)
    }
    .labelled("variable");

    recursive(|expr| {
        let application = choice((
            var,
            expr.clone()
                .delimited_by(just(Token::OpenDelim), just(Token::CloseDelim)),
        ))
        .then_ignore(just(Token::OpenDelim))
        .then(
            expr.clone()
                .separated_by(just(Token::ArgSep))
                .at_least(1)
                .collect::<VecDeque<_>>(),
        )
        .then_ignore(just(Token::CloseDelim))
        .map(|(t, mut args)| {
            let mut tree = ParseTree::Application {
                subformula: Box::new(t),
                argument: Box::new(args.pop_front().expect("previous primitive has at least 1")),
            };
            while let Some(x) = args.pop_front() {
                tree = ParseTree::Application {
                    subformula: Box::new(tree),
                    argument: Box::new(x),
                };
            }

            tree
        });

        let atom = choice((
            application,
            var,
            expr.delimited_by(just(Token::OpenDelim), just(Token::CloseDelim)),
        ));
        atom.pratt((prefix(
            0,
            select! {Token::Lambda(t, var) => (t, var)},
            |(lambda_type, var), r, _| ParseTree::Lambda {
                body: Box::new(r),
                var,
                lambda_type,
            },
        ),))
    })
}

///A function which maps strings to language of thought expressions. Crucially, it automatically performs all lambda reductions.
pub fn parse_lot(s: &str) -> Result<RootedLambdaPool<'_, Expr<'_>>, LambdaParseError> {
    let tokens = lexer::<extra::Err<Rich<char>>>()
        .then_ignore(end())
        .parse(s)
        .into_result()?;

    language_parser()
        .parse(
            tokens
                .as_slice()
                .map((s.len()..s.len()).into(), |(t, s)| (t, s)),
        )
        .into_result()?
        .into_pool()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Scenario, ThetaRoles};
    use std::collections::BTreeMap;

    fn check_lambdas(
        statement: &str,
        lambda_type: &str,
        gold_pool: RootedLambdaPool<Expr>,
    ) -> anyhow::Result<()> {
        println!("{statement}");
        let pool = parse_lot(statement)?;

        assert_eq!(
            pool.get_type()?,
            LambdaType::from_string(lambda_type).map_err(|e| anyhow::anyhow!(e.to_string()))?
        );
        assert_eq!(pool, gold_pool);

        Ok(())
    }

    #[test]
    fn parse_lambda() -> anyhow::Result<()> {
        check_lambdas(
            "lambda  <e,t> P  (lambda e x (P(x)))",
            "<<e,t>, <e,t>>",
            RootedLambdaPool::new(
                LambdaPool::from(vec![
                    LambdaExpr::BoundVariable(1, LambdaType::et().clone()),
                    LambdaExpr::BoundVariable(0, LambdaType::e().clone()),
                    LambdaExpr::Application {
                        subformula: LambdaExprRef(0),
                        argument: LambdaExprRef(1),
                    },
                    LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::e().clone()),
                    LambdaExpr::Lambda(LambdaExprRef(3), LambdaType::et().clone()),
                ]),
                LambdaExprRef(4),
            ),
        )?;
        check_lambdas(
            "hey#<e,t>(lol#e)",
            "t",
            RootedLambdaPool::new(
                LambdaPool::from(vec![
                    LambdaExpr::FreeVariable("hey".into(), LambdaType::et().clone()),
                    LambdaExpr::FreeVariable("lol".into(), LambdaType::e().clone()),
                    LambdaExpr::Application {
                        subformula: LambdaExprRef(0),
                        argument: LambdaExprRef(1),
                    },
                ]),
                LambdaExprRef(2),
            ),
        )?;

        Ok(())
    }

    #[test]
    fn parse_errors_test() -> anyhow::Result<()> {
        for statement in [
            "(wow#<a,<e,t>>(nice#a))(cool#e)",
            "every(x,lambda a y pa_John(y), pa_Blue(y#a))",
            "pa_cool(iota(x, pa_man(x)))",
            "pe_cool(iota_e(x, pe_man(x)))",
            "pa_cool(iota(x, (lambda a x pa_man(x))(x)))",
        ] {
            RootedLambdaPool::<()>::parse(statement)?;
        }

        for statement in [
            "wow#<e,t>(nice#a)",
            "(wow#<a,<e,t>>(nice#a))(cool#a)",
            "every(x,lambda a y pa_John(y), pa_Blue(y))",
        ] {
            let p = RootedLambdaPool::<()>::parse(statement);
            assert!(p.is_err());
        }
        Ok(())
    }
}
