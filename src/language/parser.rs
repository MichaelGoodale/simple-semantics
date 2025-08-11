use std::{
    collections::{HashMap, VecDeque},
    fmt::{Debug, Display},
};

use crate::{
    Actor, Entity, Event,
    lambda::{
        Bvar, LambdaExpr, LambdaExprRef, LambdaPool, ReductionError, RootedLambdaPool,
        types::{LambdaType, TypeError, core_type_parser},
    },
    language::{Constant, Expr, MonOp, lambda_implementation::LambdaConversionError},
};
use chumsky::{
    extra::ParserExtra,
    input::ValueInput,
    label::LabelError,
    text::{TextExpected, inline_whitespace},
    util::MaybeRef,
};
use chumsky::{pratt::*, prelude::*};

use super::{ActorOrEvent, BinOp, LanguageExpression, Quantifier};
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

    ///The expression was still a lambda expression and not yet runnable.
    #[error("{0}")]
    ConversionError(#[from] LambdaConversionError),
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

impl<'src> ParseTree<'src> {
    fn add_to_pool(
        &self,
        pool: &mut LambdaPool<'src, Expr<'src>>,
        variable_names: &mut VariableContext<'src>,
        lambda_depth: usize,
    ) -> Result<LambdaExprRef, LambdaParseError> {
        let expr: LambdaExpr<'src, Expr<'src>> = match &self {
            ParseTree::Constant(c) => LambdaExpr::LanguageOfThoughtExpr(Expr::Constant(*c)),
            ParseTree::Entity(e) => LambdaExpr::LanguageOfThoughtExpr(match e {
                Entity::Actor(a) => Expr::Actor(a),
                Entity::Event(e) => Expr::Event(*e),
            }),
            ParseTree::Unary(m, x) => {
                let x = x.add_to_pool(pool, variable_names, lambda_depth)?;
                let x_type = pool.get_type(x)?;
                if m.get_argument_type() != &x_type {
                    return Err(LambdaParseError::TypeError(format!(
                        "Can't apply {x_type} to {m} which takes type {}",
                        m.get_argument_type(),
                    )));
                }
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(*m, x.into()))
            }
            ParseTree::Binary(b, x, y) => {
                let x = x.add_to_pool(pool, variable_names, lambda_depth)?;
                let y = y.add_to_pool(pool, variable_names, lambda_depth)?;

                let x_type = pool.get_type(x)?;
                let y_type = pool.get_type(y)?;
                let b_type = b.get_argument_type();
                if b_type != [&x_type, &y_type] {
                    return Err(LambdaParseError::TypeError(format!(
                        "Can't apply [{x_type}, {y_type}] to {b} which takes type [{}, {}]",
                        b_type[0], b_type[1]
                    )));
                }

                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(*b, x.into(), y.into()))
            }
            ParseTree::Quantifier {
                quantifier,
                lambda_type: var_type,
                variable,
                restrictor,
                subformula,
            } => {
                let lambda_type: LambdaType = (*var_type).into();
                variable_names.bind_var(variable, lambda_depth + 1, lambda_type);
                let restrictor = restrictor.add_to_pool(pool, variable_names, lambda_depth + 1)?;

                let r_type = pool.get_type(restrictor)?;
                let required_type = match var_type {
                    ActorOrEvent::Actor => LambdaType::at(),
                    ActorOrEvent::Event => LambdaType::et(),
                };
                if &r_type != required_type && &r_type != LambdaType::t() {
                    return Err(LambdaParseError::TypeError(format!(
                        "Quantifier restrictor is {r_type} and not of type {required_type} or t",
                    )));
                }

                let subformula = subformula.add_to_pool(pool, variable_names, lambda_depth + 1)?;
                let sub_type = pool.get_type(subformula)?;
                if &sub_type != LambdaType::t() {
                    return Err(LambdaParseError::TypeError(format!(
                        "Quantifier body is {sub_type} and not of t",
                    )));
                }
                variable_names.unbind(variable);

                LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                    quantifier: *quantifier,
                    var_type: *var_type,
                    restrictor: restrictor.into(),
                    subformula: subformula.into(),
                })
            }
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
        };
        Ok(pool.add(expr))
    }

    fn to_pool(&self) -> Result<RootedLambdaPool<'src, Expr<'src>>, LambdaParseError> {
        let mut pool = LambdaPool::new();

        let mut var_labels = VariableContext::default();
        let root = self.add_to_pool(&mut pool, &mut var_labels, 0)?;
        Ok(RootedLambdaPool::new(pool, root))
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Default)]
struct VariableContext<'src>(HashMap<&'src str, Vec<(Bvar, LambdaType)>>, u32);

impl<'src> VariableContext<'src> {
    fn to_expr(
        &self,
        variable: &'src str,
        lambda_type: Option<LambdaType>,
        lambda_depth: usize,
    ) -> Result<LambdaExpr<'src, Expr<'src>>, LambdaParseError> {
        Ok(match self.0.get(variable) {
            Some(vars) if !vars.is_empty() => {
                let (og_depth, lambda_type) = vars
                    .last()
                    .expect("There should never be an empty vec in the VariableContext");
                LambdaExpr::BoundVariable(lambda_depth - og_depth, lambda_type.clone())
            }
            //Do free var
            _ => match lambda_type {
                Some(lambda_type) => LambdaExpr::FreeVariable(variable.into(), lambda_type),
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
enum ParseTree<'src> {
    Lambda {
        body: Box<ParseTree<'src>>,
        lambda_type: LambdaType,
        var: &'src str,
    },
    Variable(&'src str),
    FreeVariable(&'src str, LambdaType),
    Application {
        subformula: Box<ParseTree<'src>>,
        argument: Box<ParseTree<'src>>,
    },
    Constant(Constant<'src>),
    Unary(MonOp<'src>, Box<ParseTree<'src>>),
    Binary(BinOp, Box<ParseTree<'src>>, Box<ParseTree<'src>>),
    Quantifier {
        quantifier: Quantifier,
        lambda_type: ActorOrEvent,
        variable: &'src str,
        restrictor: Box<ParseTree<'src>>,
        subformula: Box<ParseTree<'src>>,
    },
    Entity(Entity<'src>),
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

fn unary_op<'tokens, 'src: 'tokens, I>(
    expr: impl Parser<'tokens, I, ParseTree<'src>, ChumskyErr<'tokens, 'src>> + Clone,
) -> impl Parser<'tokens, I, ParseTree<'src>, ChumskyErr<'tokens, 'src>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = SimpleSpan> + Clone,
{
    select! {Token::Property(s, a) => MonOp::Property(s, a)}
        .then(expr.delimited_by(just(Token::OpenDelim), just(Token::CloseDelim)))
        .map(|(op, arg)| ParseTree::Unary(op, Box::new(arg)))
}

type ChumskyErr<'tokens, 'src> = extra::Err<Rich<'tokens, Token<'src>, Span>>;

fn binary_operation<'tokens, 'src: 'tokens, I>(
    a: impl Parser<'tokens, I, ParseTree<'src>, ChumskyErr<'tokens, 'src>> + Clone,
    b: impl Parser<'tokens, I, ParseTree<'src>, ChumskyErr<'tokens, 'src>> + Clone,
) -> impl Parser<'tokens, I, ParseTree<'src>, ChumskyErr<'tokens, 'src>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = SimpleSpan> + Clone,
{
    select! { Token::BinOp(b) => b}
        .labelled("binary operation")
        .then_ignore(just(Token::OpenDelim))
        .then(a)
        .then_ignore(just(Token::ArgSep))
        .then(b)
        .then_ignore(just(Token::CloseDelim))
        .map(|((binop, actor), event)| ParseTree::Binary(binop, Box::new(actor), Box::new(event)))
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum Token<'src> {
    Bool(Constant<'src>),
    And,
    Or,
    Not,
    Actor(Actor<'src>),
    Event(Event),
    BinOp(BinOp),
    OpenDelim,
    ArgSep,
    CloseDelim,
    Constant(Constant<'src>),
    Property(&'src str, ActorOrEvent),
    Quantifier(Quantifier, ActorOrEvent),
    Lambda(LambdaType, &'src str),
    Variable(&'src str),
    FreeVariable(&'src str, LambdaType),
}
impl Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Actor(a) => write!(f, "a_{a}"),
            Token::Event(n) => write!(f, "e_{n}"),
            Token::OpenDelim => write!(f, "("),
            Token::ArgSep => write!(f, ","),
            Token::CloseDelim => write!(f, ")"),
            Token::Bool(constant) => write!(f, "{constant}"),
            Token::And => write!(f, "&"),
            Token::Or => write!(f, "|"),
            Token::Not => write!(f, "~"),
            Token::BinOp(bin_op) => write!(f, "{bin_op}"),
            Token::Constant(constant) => write!(f, "{constant}"),
            Token::Property(k, actor_or_event) => write!(f, "p{actor_or_event}_{k}"),
            Token::Quantifier(quantifier, actor_or_event) => write!(
                f,
                "{quantifier}{}",
                match actor_or_event {
                    ActorOrEvent::Actor => "",
                    ActorOrEvent::Event => "_e",
                }
            ),
            Token::Lambda(lambda_type, t) => write!(f, "lambda {lambda_type} {t}"),
            Token::Variable(v) => write!(f, "{v}"),
            Token::FreeVariable(v, lambda_type) => write!(f, "{v}#{lambda_type}"),
        }
    }
}

pub type Span = SimpleSpan;
pub type Spanned<T> = (T, Span);

fn lexer<'src, E>() -> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, E>
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>
        + LabelError<'src, &'src str, &'static str>,
{
    choice((
        just(',').to(Token::ArgSep),
        just('(').to(Token::OpenDelim),
        just(')').to(Token::CloseDelim),
        just("True").to(Token::Bool(Constant::Tautology)),
        just("False").to(Token::Bool(Constant::Contradiction)),
        just('&').to(Token::And),
        just('|').to(Token::Or),
        just('~').to(Token::Not),
        just("AgentOf").to(Token::BinOp(BinOp::AgentOf)),
        just("PatientOf").to(Token::BinOp(BinOp::PatientOf)),
        just("all_a").to(Token::Constant(Constant::Everyone)),
        just("all_e").to(Token::Constant(Constant::EveryEvent)),
        choice((
            just("every").to(Quantifier::Universal),
            just("some").to(Quantifier::Existential),
        ))
        .then(just("_e").or_not())
        .map(|(q, t)| {
            Token::Quantifier(
                q,
                if t.is_some() {
                    ActorOrEvent::Event
                } else {
                    ActorOrEvent::Actor
                },
            )
        }),
        just("a_").ignore_then(keyword()).map(Token::Actor),
        just("e_")
            .ignore_then(text::int(10))
            .map(|s: &str| Token::Event(s.parse().unwrap())),
        just("p")
            .ignore_then(
                just("a")
                    .to(ActorOrEvent::Actor)
                    .or(just("e").to(ActorOrEvent::Event)),
            )
            .then_ignore(just("_"))
            .then(keyword())
            .map(|(t, s)| Token::Property(s, t)),
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

fn language_parser<'tokens, 'src: 'tokens, I>()
-> impl Parser<'tokens, I, ParseTree<'src>, extra::Err<Rich<'tokens, Token<'src>, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = SimpleSpan> + Clone,
{
    let var = select! {
        Token::Variable(a) => ParseTree::Variable(a),
        Token::FreeVariable(a, t) => ParseTree::FreeVariable(a, t)
    }
    .labelled("variable");

    let ent = select! {
        Token::Actor(a) => ParseTree::Entity(Entity::Actor(a)),
        Token::Event(a) => ParseTree::Entity(Entity::Event(a)),
    }
    .labelled("entity");

    let bool = select! {
        Token::Bool(b) => ParseTree::Constant(b)
    }
    .labelled("boolean");

    let sets = select! {
        Token::Constant(c) => ParseTree::Constant(c),
        Token::Property(s, a) => ParseTree::Constant(Constant::Property(s,a))
    }
    .labelled("constant set");
    recursive(|expr| {
        let bin_op = binary_operation(expr.clone(), expr.clone());
        let mon_op = unary_op(expr.clone());

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

        let quantified = select!(Token::Quantifier(q, a) => (q,a))
            .then_ignore(just(Token::OpenDelim))
            .then(select! {Token::Variable(v) => v})
            .then_ignore(just(Token::ArgSep))
            .then(expr.clone())
            .then_ignore(just(Token::ArgSep))
            .then(expr.clone())
            .then_ignore(just(Token::CloseDelim))
            .map(
                |((((quantifier, lambda_type), variable), restrictor), subformula)| {
                    ParseTree::Quantifier {
                        quantifier,
                        variable,
                        lambda_type,
                        restrictor: Box::new(restrictor),
                        subformula: Box::new(subformula),
                    }
                },
            );

        let atom = choice((
            application,
            ent,
            var,
            bin_op,
            mon_op,
            quantified,
            bool,
            sets,
            expr.delimited_by(just(Token::OpenDelim), just(Token::CloseDelim)),
        ));
        atom.pratt((
            prefix(2, just(Token::Not), |_, r, _| {
                ParseTree::Unary(MonOp::Not, Box::new(r))
            }),
            prefix(
                0,
                select! {Token::Lambda(t, var) => (t, var)},
                |(lambda_type, var), r, _| ParseTree::Lambda {
                    body: Box::new(r),
                    var,
                    lambda_type,
                },
            ),
            infix(left(1), just(Token::And), |l, _, r, _| {
                ParseTree::Binary(BinOp::And, Box::new(l), Box::new(r))
            }),
            infix(left(1), just(Token::Or), |l, _, r, _| {
                ParseTree::Binary(BinOp::Or, Box::new(l), Box::new(r))
            }),
        ))
    })
}

///A function which maps strings to language of thought expressions. Crucially, it automatically performs all lambda reductions.
pub fn parse_lot<'a>(s: &'a str) -> Result<RootedLambdaPool<'a, Expr<'a>>, LambdaParseError> {
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
        .to_pool()
}

///A function which maps strings to language of thought expressions. Crucially, it automatically performs all lambda reductions.
pub fn parse_executable<'a>(s: &'a str) -> Result<LanguageExpression<'a>, LambdaParseError> {
    let mut pool = parse_lot(s)?;
    pool.reduce()?;
    Ok(pool.into_pool()?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language::{ExprRef, LanguageResult};
    use crate::{Scenario, ThetaRoles};
    use std::collections::BTreeMap;

    #[test]
    fn parse_entity() {
        for n in [1, 6, 3, 4, 5, 100, 40] {
            let str = format!("e_{n}");
            assert_eq!(
                parse_lot(&str).unwrap(),
                RootedLambdaPool::new(
                    LambdaPool(vec![LambdaExpr::LanguageOfThoughtExpr(Expr::Event(n))]),
                    LambdaExprRef(0)
                )
            );
        }
        for keyword in ["john", "mary", "phil", "Anna"] {
            let str = format!("a_{keyword}");
            assert_eq!(
                parse_lot(&str).unwrap(),
                RootedLambdaPool::new(
                    LambdaPool(vec![LambdaExpr::LanguageOfThoughtExpr(Expr::Actor(
                        keyword
                    ))]),
                    LambdaExprRef(0)
                )
            );
        }
    }

    #[test]
    fn parse_sets() {
        assert_eq!(
            parse_lot("all_e").unwrap(),
            RootedLambdaPool::new(
                LambdaPool(vec![LambdaExpr::LanguageOfThoughtExpr(Expr::Constant(
                    Constant::EveryEvent
                ))]),
                LambdaExprRef(0)
            )
        );
        assert_eq!(
            parse_lot("all_a").unwrap(),
            RootedLambdaPool::new(
                LambdaPool(vec![LambdaExpr::LanguageOfThoughtExpr(Expr::Constant(
                    Constant::Everyone
                ))]),
                LambdaExprRef(0)
            )
        );
        for keyword in ["john", "mary", "phil", "Anna"] {
            let str = format!("pa_{keyword}");
            assert_eq!(
                parse_lot(&str).unwrap(),
                RootedLambdaPool::new(
                    LambdaPool(vec![LambdaExpr::LanguageOfThoughtExpr(Expr::Constant(
                        Constant::Property(keyword, ActorOrEvent::Actor)
                    ))]),
                    LambdaExprRef(0)
                )
            );
            let str = format!("pe_{keyword}");
            assert_eq!(
                parse_lot(&str).unwrap(),
                RootedLambdaPool::new(
                    LambdaPool(vec![LambdaExpr::LanguageOfThoughtExpr(Expr::Constant(
                        Constant::Property(keyword, ActorOrEvent::Event)
                    ))]),
                    LambdaExprRef(0)
                )
            );
        }
    }

    fn get_parse<'a>(
        s: &'a str,
        simple_scenario: &'a Scenario,
    ) -> anyhow::Result<LanguageResult<'a>> {
        let pool = LanguageExpression::parse(s)?;
        Ok(pool.run(simple_scenario, None)?)
    }

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
            "lambda e x (pe_Red(x))",
            "<e,t>",
            RootedLambdaPool::new(
                LambdaPool::from(vec![
                    LambdaExpr::BoundVariable(0, LambdaType::e().clone()),
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                        MonOp::Property("Red", ActorOrEvent::Event),
                        ExprRef(0),
                    )),
                    LambdaExpr::Lambda(LambdaExprRef(1), LambdaType::e().clone()),
                ]),
                LambdaExprRef(2),
            ),
        )?;
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
            "lambda <a,t> P (P(a_0))",
            "<<a,t>,t>",
            RootedLambdaPool::new(
                LambdaPool::from(vec![
                    LambdaExpr::BoundVariable(0, LambdaType::at().clone()),
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Actor("0")),
                    LambdaExpr::Application {
                        subformula: LambdaExprRef(0),
                        argument: LambdaExprRef(1),
                    },
                    LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::at().clone()),
                ]),
                LambdaExprRef(3),
            ),
        )?;
        check_lambdas(
            "~hey#<e,t>(lol#e)",
            "t",
            RootedLambdaPool::new(
                LambdaPool::from(vec![
                    LambdaExpr::FreeVariable("hey".into(), LambdaType::et().clone()),
                    LambdaExpr::FreeVariable("lol".into(), LambdaType::e().clone()),
                    LambdaExpr::Application {
                        subformula: LambdaExprRef(0),
                        argument: LambdaExprRef(1),
                    },
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Not, ExprRef(2))),
                ]),
                LambdaExprRef(3),
            ),
        )?;

        check_lambdas(
            "(lambda <a,t> P (P(a_0)))(lambda a x (pa_Red(x)))",
            "t",
            RootedLambdaPool::new(
                LambdaPool::from(vec![
                    LambdaExpr::BoundVariable(0, LambdaType::at().clone()),
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Actor("0")),
                    LambdaExpr::Application {
                        subformula: LambdaExprRef(0),
                        argument: LambdaExprRef(1),
                    },
                    LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::at().clone()),
                    LambdaExpr::BoundVariable(0, LambdaType::a().clone()),
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                        MonOp::Property("Red", ActorOrEvent::Actor),
                        ExprRef(4),
                    )),
                    LambdaExpr::Lambda(LambdaExprRef(5), LambdaType::a().clone()),
                    LambdaExpr::Application {
                        subformula: LambdaExprRef(3),
                        argument: LambdaExprRef(6),
                    },
                ]),
                LambdaExprRef(7),
            ),
        )?;
        check_lambdas(
            "lambda t phi (lambda t psi (phi & psi))",
            "<t,<t,t>>",
            RootedLambdaPool::new(
                LambdaPool::from(vec![
                    LambdaExpr::BoundVariable(1, LambdaType::t().clone()),
                    LambdaExpr::BoundVariable(0, LambdaType::t().clone()),
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(
                        BinOp::And,
                        ExprRef(0),
                        ExprRef(1),
                    )),
                    LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::t().clone()),
                    LambdaExpr::Lambda(LambdaExprRef(3), LambdaType::t().clone()),
                ]),
                LambdaExprRef(4),
            ),
        )?;

        Ok(())
    }

    #[test]
    fn test_parse_with_beta_reduction() -> anyhow::Result<()> {
        parse_executable("(lambda <a,t> P (P(a_0)))(lambda a x (pa_Red(x)))")?;
        Ok(())
    }

    #[test]
    fn parse_with_keywords() -> anyhow::Result<()> {
        let mut properties = BTreeMap::default();

        properties.insert("Red", vec![Entity::Actor("John")]);
        properties.insert("Blue", vec![Entity::Actor("Mary"), Entity::Actor("John")]);

        let scenario = Scenario {
            question: vec![],
            actors: vec!["Mary", "John"],
            thematic_relations: vec![
                ThetaRoles {
                    agent: Some("Mary"),
                    patient: Some("Mary"),
                },
                ThetaRoles {
                    agent: Some("John"),
                    patient: Some("Mary"),
                },
            ],
            properties,
        };

        for statement in [
            "~AgentOf(a_John, e_0)",
            "pa_Red(a_John) & ~pa_Red(a_Mary)",
            "pa_Red(a_John) & ~pa_Red(a_Mary) & pa_Red(a_John)",
            "~(pa_Red(a_John) & ~(True & pa_Red(a_John)))",
            "every(x0, all_a, pa_Blue(x0))",
            "every(x0, pa_Blue, pa_Blue(x0))",
            "every(x, pa_Red, pa_Blue(x))",
            "every(x0, pa_Red, pa_Blue(x0))",
            "every_e(x0, all_e, (some(x1, all_a, AgentOf(x1, x0))))",
            "every_e(x0, all_e, (some(x1, all_a, PatientOf(x1, x0))))",
            "every_e(x0, all_e, PatientOf(a_Mary, x0))",
            "some(x0, (PatientOf(x0, e_0) & PatientOf(x0, e_1)), pa_Blue(x0))",
        ] {
            println!("{statement}");
            let expression = parse_executable(statement)?;
            assert_eq!(expression.run(&scenario, None)?, LanguageResult::Bool(true));
        }

        for (statement, result) in [
            ("a_Mary", LanguageResult::Actor("Mary")),
            ("pa_Red", LanguageResult::ActorSet(vec!["John"])),
            ("pa_Blue", LanguageResult::ActorSet(vec!["Mary", "John"])),
        ] {
            println!("{statement}");
            let expression = parse_executable(statement)?;
            assert_eq!(expression.run(&scenario, None)?, result);
        }

        Ok(())
    }

    #[test]
    fn parse_test() -> anyhow::Result<()> {
        let mut properties = BTreeMap::default();

        properties.insert("Red", vec![Entity::Actor("John")]);
        properties.insert("Blue", vec![Entity::Actor("Mary"), Entity::Actor("John")]);

        let scenario = Scenario {
            question: vec![],
            actors: vec!["Mary", "John"],
            thematic_relations: vec![
                ThetaRoles {
                    agent: Some("Mary"),
                    patient: Some("Mary"),
                },
                ThetaRoles {
                    agent: Some("John"),
                    patient: Some("Mary"),
                },
            ],
            properties,
        };

        for statement in [
            "True",
            "~~~False",
            "~AgentOf(a_John, e_0)",
            "~(True & False)",
            "True | False",
            "(True & False) | True",
            "~(True & False) | False",
            "pa_Red(a_John) & ~pa_Red(a_Mary)",
            "pa_Red(a_John) & ~pa_Red(a_Mary) & pa_Red(a_John)",
            "~(pa_Red(a_John) & ~(True & pa_Red(a_John)))",
            "every(x0, all_a, pa_Blue(x0))",
            "every(x0, pa_Blue, pa_Blue(x0))",
            "every_e(x0, all_e, (some(x1, all_a, AgentOf(x1, x0))))",
            "every_e(x0, all_e, (some(x1, all_a, PatientOf(x1, x0))))",
            "every_e(x0, all_e, PatientOf(a_Mary, x0))",
            "some(x0, (PatientOf(x0, e_0) & PatientOf(x0, e_1)), pa_Blue(x0))",
        ] {
            println!("{statement}");
            assert_eq!(get_parse(statement, &scenario)?, LanguageResult::Bool(true));
        }
        for (statement, result) in [
            ("a_Mary", LanguageResult::Actor("Mary")),
            ("e_0", LanguageResult::Event(0)),
            ("all_e", LanguageResult::EventSet(vec![0, 1])),
            ("all_a", LanguageResult::ActorSet(vec!["Mary", "John"])),
            ("pa_Red", LanguageResult::ActorSet(vec!["John"])),
            ("pa_Blue", LanguageResult::ActorSet(vec!["Mary", "John"])),
        ] {
            println!("{statement}");
            assert_eq!(get_parse(statement, &scenario)?, result);
        }

        Ok(())
    }

    #[test]
    fn parse_errors_test() -> anyhow::Result<()> {
        for statement in [
            "(wow#<a,<e,t>>(nice#a))(cool#e)",
            "every(x,lambda a y pa_John(y), pa_Blue(y#a))",
        ] {
            println!("{statement}");
            RootedLambdaPool::parse(statement)?;
        }

        for statement in [
            "wow#<e,t>(nice#a)",
            "(wow#<a,<e,t>>(nice#a))(cool#a)",
            "every(x,lambda a y pa_John(y), pa_Blue(y))",
        ] {
            let p = RootedLambdaPool::parse(statement);
            assert!(p.is_err());
        }
        Ok(())
    }
}
