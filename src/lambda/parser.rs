use crate::{
    Actor, Event,
    lambda::{
        Bvar, ExprType, FreeVar, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool,
        PrimitiveVarType::{self},
        RootedLambdaPool,
        types::{
            LambdaType::{self, A},
            core_type_parser,
        },
    },
    language::{ActorOrEvent, BinOp, Constant, Expr, MonOp, Quantifier},
};
use ariadne::{Color, Label, Report, Source};
use chumsky::{
    extra::ParserExtra,
    input::ValueInput,
    pratt::{infix, left, prefix},
    prelude::*,
    span::{SimpleSpan, Spanned},
    text::inline_whitespace,
};
use std::{
    collections::{HashMap, VecDeque},
    fmt::{Debug, Display},
    ops::Range,
};

use thiserror::Error;

///Error in parsing a lambda expression
#[derive(Error, Debug, Clone)]
pub struct LambdaParseError(Vec<OwnedParseError>, String);

#[derive(Debug, Clone, Eq, PartialEq)]
struct QuantifierProblem {
    span: Range<usize>,
    found: LambdaType,
}

#[derive(Debug, Clone)]
enum OwnedParseError {
    ParseError {
        message: String,
        reason: String,
        span: Range<usize>,
        contexts: Vec<(String, Range<usize>)>,
    },
    ApplicationError {
        span: Range<usize>,
        alpha: Range<usize>,
        beta: Range<usize>,
        alpha_type: LambdaType,
        beta_type: LambdaType,
    },
    QuantifierError {
        span: Range<usize>,
        quantifier_span: Range<usize>,
        intended: LambdaType,
        body_span: QuantifierProblem,
        second_body_span: Option<QuantifierProblem>,
        is_double: bool,
    },
    UnTypedFreeVariable {},
}

impl From<Rich<'_, String>> for OwnedParseError {
    fn from(e: Rich<String>) -> OwnedParseError {
        OwnedParseError::ParseError {
            message: e.to_string(),
            reason: e.reason().to_string(),
            span: e.span().into_range(),
            contexts: e
                .contexts()
                .map(|(label, span)| (label.to_string(), span.into_range()))
                .collect::<Vec<_>>(),
        }
    }
}

impl Display for LambdaParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buf = Vec::new();
        for e in &self.0 {
            match e {
                OwnedParseError::ParseError {
                    message,
                    reason,
                    span,
                    contexts,
                } => Report::build(ariadne::ReportKind::Error, span.clone())
                    .with_config(ariadne::Config::new().with_index_type(ariadne::IndexType::Byte))
                    .with_message(message)
                    .with_label(
                        Label::new(span.clone())
                            .with_message(reason)
                            .with_color(Color::Red),
                    )
                    .with_labels(contexts.iter().map(|(label, span)| {
                        Label::new(span.clone())
                            .with_message(format!("while parsing this {label}"))
                            .with_color(Color::Yellow)
                    }))
                    .finish(),
                OwnedParseError::ApplicationError {
                    span,
                    alpha,
                    beta,
                    alpha_type,
                    beta_type,
                } => Report::build(ariadne::ReportKind::Error, span.clone())
                    .with_config(ariadne::Config::new().with_index_type(ariadne::IndexType::Byte))
                    .with_message(format!("Can't apply {beta_type} to {alpha_type}"))
                    .with_label(
                        Label::new(alpha.clone())
                            .with_message(format!("Function has type {alpha_type}"))
                            .with_color(Color::Red),
                    )
                    .with_label(
                        Label::new(beta.clone())
                            .with_message(format!("Argument has type {beta_type}"))
                            .with_color(Color::Red),
                    )
                    .finish(),
                OwnedParseError::UnTypedFreeVariable {} => todo!(),
                OwnedParseError::QuantifierError {
                    span,
                    quantifier_span,
                    intended,
                    body_span:
                        QuantifierProblem {
                            span: body_span,
                            found,
                        },
                    second_body_span,
                    is_double,
                } => {
                    let r = Report::build(ariadne::ReportKind::Error, span.clone())
                        .with_config(
                            ariadne::Config::new().with_index_type(ariadne::IndexType::Byte),
                        )
                        .with_message("This expression's body is of the wrong type.")
                        .with_label(
                            Label::new(quantifier_span.clone())
                                .with_message(format!(
                                    "This expression has {} of type {intended}",
                                    if *is_double { "bodies" } else { "a body" }
                                ))
                                .with_color(Color::Yellow),
                        )
                        .with_label(
                            Label::new(body_span.clone())
                                .with_message(format!("This body is of type {found}"))
                                .with_color(Color::Red),
                        );

                    if let Some(QuantifierProblem { span, found }) = second_body_span {
                        r.with_label(
                            Label::new(span.clone())
                                .with_message(format!("This body is of type {found}"))
                                .with_color(Color::Red),
                        )
                        .finish()
                    } else {
                        r.finish()
                    }
                }
            }
            .write(Source::from(&self.1), &mut buf)
            .map_err(|_| std::fmt::Error)?;
        }
        let s = std::str::from_utf8(&buf).map_err(|_| std::fmt::Error)?;
        f.write_str(s)?;

        Ok(())
    }
}

impl<'src, T> RootedLambdaPool<'src, T>
where
    T: ParseLot<'src> + LambdaLanguageOfThought + Clone + PartialEq + Debug,
    T::Token: Display + Clone + PartialEq + Debug,
{
    pub fn parse(s: &'src str) -> Result<RootedLambdaPool<'src, T>, LambdaParseError> {
        parse_lot(s)
    }
}

fn add_to_pool<'src, T: LambdaLanguageOfThought + Debug>(
    ast: Spanned<ParseTree<'src, T>>,
    pool: &mut LambdaPool<'src, T>,
    variable_names: &mut VariableContext<'src>,
    errors: &mut Vec<OwnedParseError>,
    lambda_depth: usize,
) -> LambdaExprRef {
    let expr: LambdaExpr<'src, T> = match ast.inner {
        ParseTree::Application {
            subformula,
            argument,
        } => {
            let sub_span = subformula.span.into_range();
            let arg_span = argument.span.into_range();
            let subformula = add_to_pool(*subformula, pool, variable_names, errors, lambda_depth);
            let argument = add_to_pool(*argument, pool, variable_names, errors, lambda_depth);

            let f = pool.get_type(subformula).expect("wee");
            let arg = pool.get_type(argument).expect("woo");

            if !f.can_apply(&arg) {
                errors.push(OwnedParseError::ApplicationError {
                    span: ast.span.into_range(),
                    alpha: sub_span,
                    beta: arg_span,
                    alpha_type: f,
                    beta_type: arg,
                })
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
            let body = add_to_pool(*body, pool, variable_names, errors, lambda_depth + 1);
            variable_names.unbind(var);
            LambdaExpr::Lambda(body, lambda_type.clone())
        }
        ParseTree::LanguageOfThoughtExprBindOne { body, var, expr } => {
            let var_type = expr.var_type().unwrap_or_else(||panic!("Implementation error: {expr:?} is being parsed as a variable binding expression, but expr.var_type() returns None"));
            let (arg_type, _)= expr.typ().split().unwrap_or_else(|_| panic!("Implementation error: {expr:?} is parsed as a variable binding expression but is not a function"));
            let (implict_var_type, body_type) = arg_type.split().unwrap_or_else(|_| {
                panic!(
                    "Implementation error: {:?} is not at least a two place function",
                    expr.inner
                )
            });
            debug_assert_eq!(
                var_type, implict_var_type,
                "Implementation error: {:?}'s body must take as argument its {var_type:?}",
                expr.inner
            );

            variable_names.bind_var(var, lambda_depth + 1, var_type.clone());
            let body_span = body.span.into_range();
            let body_ref = add_to_pool(*body, pool, variable_names, errors, lambda_depth + 1);
            let found_body_type = pool.get_type(body_ref).unwrap();
            if &found_body_type != body_type {
                errors.push(OwnedParseError::QuantifierError {
                    span: ast.span.into_range(),
                    quantifier_span: expr.span.into_range(),
                    intended: body_type.clone(),
                    body_span: QuantifierProblem {
                        found: found_body_type,
                        span: body_span,
                    },
                    second_body_span: None,
                    is_double: false,
                })
            }

            variable_names.unbind(var);
            LambdaExpr::LanguageOfThoughtExpr(expr.inner, ExprType::BindVar(body_ref))
        }
        ParseTree::LanguageOfThoughtExprBindTwo {
            body1,
            body2,
            var,
            expr,
        } => {
            let var_type = expr.var_type().unwrap_or_else(||panic!("Implementation error: {expr:?} is being parsed as a variable binding expression, but expr.var_type() returns None"));
            let (arg_type, arg_return_type) = expr.typ().split().unwrap_or_else(|_| panic!("Implementation error: {expr:?} is parsed as a variable binding expression but is not a function"));
            let (arg_type2, return_type) = arg_return_type.split().unwrap_or_else(|_| panic!("Implementation error: {expr:?} is parsed as a variable binding expression but is not a function"));
            debug_assert_eq!(
                arg_type, arg_type2,
                "Implementation error: {:?}'s two bodies must have the same type.",
                expr.inner
            );

            let (implict_var_type, body_type) = arg_type.split().unwrap_or_else(|_| {
                panic!(
                    "Implementation error: {:?} is not at least a two place function",
                    expr.inner
                )
            });
            debug_assert_eq!(
                var_type, implict_var_type,
                "Implementation error: {:?}'s body must take as argument its {var_type:?}",
                expr.inner
            );

            variable_names.bind_var(var, lambda_depth + 1, var_type.clone());
            let bodies = [*body1, *body2];
            let mut refs = [None, None];
            let mut q_errors = [None, None];

            for (x, body) in bodies.into_iter().zip(refs.iter_mut()) {
                let body_span = x.span.into_range();
                let i = add_to_pool(x, pool, variable_names, errors, lambda_depth + 1);
                let found_body_type = pool.get_type(i).unwrap();

                if &found_body_type != body_type {
                    let q = QuantifierProblem {
                        found: found_body_type,
                        span: body_span,
                    };
                    if q_errors[0].is_some() {
                        q_errors[1] = Some(q);
                    } else {
                        q_errors[0] = Some(q);
                    }
                }
                *body = Some(i);
            }

            match q_errors {
                [Some(q), None] => errors.push(OwnedParseError::QuantifierError {
                    span: ast.span.into_range(),
                    intended: body_type.clone(),
                    quantifier_span: expr.span.into_range(),
                    body_span: q,
                    second_body_span: None,
                    is_double: true,
                }),
                [Some(q1), Some(q2)] => errors.push(OwnedParseError::QuantifierError {
                    span: ast.span.into_range(),
                    intended: body_type.clone(),
                    quantifier_span: expr.span.into_range(),
                    body_span: q1,
                    second_body_span: Some(q2),
                    is_double: true,
                }),
                _ => {}
            }

            variable_names.unbind(var);
            let [body1, body2] = refs;
            LambdaExpr::LanguageOfThoughtExpr(
                expr.inner,
                ExprType::BindVarTwoBodies(body1.unwrap(), body2.unwrap()),
            )
        }
        ParseTree::Variable(var) => variable_names.to_expr(var, None, lambda_depth).unwrap(),
        ParseTree::FreeVariable(var, lambda_type) => variable_names
            .to_expr(var, Some(lambda_type.clone()), lambda_depth)
            .unwrap(),
        ParseTree::LanguageOfThoughtExpr(e) => {
            LambdaExpr::LanguageOfThoughtExpr(e, ExprType::NoVar)
        }
    };
    pool.add(expr)
}

fn into_pool<'src, T: LambdaLanguageOfThought + Debug>(
    ast: Spanned<ParseTree<'src, T>>,
) -> Result<RootedLambdaPool<'src, T>, Vec<OwnedParseError>> {
    let mut pool = LambdaPool::new();

    let mut var_labels = VariableContext::default();
    let mut errors = vec![];
    let root = add_to_pool(ast, &mut pool, &mut var_labels, &mut errors, 0);
    if errors.is_empty() {
        Ok(RootedLambdaPool::new(pool, root))
    } else {
        Err(errors)
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
    ) -> Result<LambdaExpr<'src, T>, OwnedParseError> {
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
                    //TODO: I don't think this should actually ever occur, but should check
                    return Err(OwnedParseError::UnTypedFreeVariable {});
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
        body: Box<Spanned<ParseTree<'src, T>>>,
        lambda_type: LambdaType,
        var: &'src str,
    },
    Variable(&'src str),
    FreeVariable(&'src str, LambdaType),
    Application {
        subformula: Box<Spanned<ParseTree<'src, T>>>,
        argument: Box<Spanned<ParseTree<'src, T>>>,
    },
    LanguageOfThoughtExpr(T),
    LanguageOfThoughtExprBindOne {
        expr: Spanned<T>,
        body: Box<Spanned<ParseTree<'src, T>>>,
        var: &'src str,
    },
    LanguageOfThoughtExprBindTwo {
        expr: Spanned<T>,
        body1: Box<Spanned<ParseTree<'src, T>>>,
        body2: Box<Spanned<ParseTree<'src, T>>>,
        var: &'src str,
    },
}

fn keyword<'src, E>() -> impl Parser<'src, &'src str, &'src str, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
{
    one_of("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789")
        .repeated()
        .at_least(1)
        .to_slice()
}

pub trait ParseLot<'src> {
    type Token;

    fn tokenizer() -> impl Parser<'src, &'src str, Self::Token, extra::Err<Rich<'src, char>>>;
    fn is_infix(token: &Self::Token) -> bool;
    fn is_prefix(token: &Self::Token) -> bool;
    fn bind_var_type(token: &Self::Token) -> PrimitiveVarType;
    fn into_expr(token: Self::Token) -> Self;
}

impl<'src> ParseLot<'src> for () {
    type Token = &'static str;

    fn tokenizer() -> impl Parser<'src, &'src str, Self::Token, extra::Err<Rich<'src, char>>> {
        just("1").to("1")
    }

    fn is_infix(_: &Self::Token) -> bool {
        false
    }

    fn is_prefix(_: &Self::Token) -> bool {
        false
    }

    fn bind_var_type(_: &Self::Token) -> PrimitiveVarType {
        PrimitiveVarType::NoVar
    }

    fn into_expr(_: Self::Token) -> Self {}
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ExprToken<'src> {
    Constant(Constant<'src>),
    BinOp(BinOp),
    MonOp(MonOp),
    Actor(Actor<'src>),
    Event(Event),
    Iota(ActorOrEvent),
    Quantifier(Quantifier, ActorOrEvent),
}

impl Display for ExprToken<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprToken::Actor(a) => write!(f, "a_{a}"),
            ExprToken::Event(n) => write!(f, "e_{n}"),
            ExprToken::BinOp(bin_op) => write!(f, "{bin_op}"),
            ExprToken::Quantifier(quantifier, actor_or_event) => write!(
                f,
                "{quantifier}{}",
                match actor_or_event {
                    ActorOrEvent::Actor => "",
                    ActorOrEvent::Event => "_e",
                }
            ),
            ExprToken::Iota(ActorOrEvent::Event) => write!(f, "iota_e"),
            ExprToken::Iota(ActorOrEvent::Actor) => write!(f, "iota"),
            ExprToken::Constant(constant) => write!(f, "{constant}"),
            ExprToken::MonOp(mon_op) => write!(f, "{mon_op}"),
        }
    }
}

impl<'src> ParseLot<'src> for Expr<'src> {
    type Token = ExprToken<'src>;

    fn tokenizer() -> impl Parser<'src, &'src str, Self::Token, extra::Err<Rich<'src, char>>> {
        choice((
            just("True").to(ExprToken::Constant(Constant::Tautology)),
            just("False").to(ExprToken::Constant(Constant::Contradiction)),
            just("all_a").to(ExprToken::Constant(Constant::Everyone)),
            just("all_e").to(ExprToken::Constant(Constant::EveryEvent)),
            just('&').to(ExprToken::BinOp(BinOp::And)),
            just('|').to(ExprToken::BinOp(BinOp::Or)),
            just('~').to(ExprToken::MonOp(MonOp::Not)),
            just("AgentOf").to(ExprToken::BinOp(BinOp::AgentOf)),
            just("PatientOf").to(ExprToken::BinOp(BinOp::PatientOf)),
            just("iota_e").to(ExprToken::Iota(ActorOrEvent::Event)),
            just("iota").to(ExprToken::Iota(ActorOrEvent::Actor)),
            choice((
                just("every").to(Quantifier::Universal),
                just("some").to(Quantifier::Existential),
            ))
            .then(just("_e").or_not())
            .map(|(q, t)| {
                ExprToken::Quantifier(
                    q,
                    if t.is_some() {
                        ActorOrEvent::Event
                    } else {
                        ActorOrEvent::Actor
                    },
                )
            }),
            just("a_").ignore_then(keyword()).map(ExprToken::Actor),
            just("e_")
                .ignore_then(text::int(10))
                .map(|s: &str| ExprToken::Event(s.parse().unwrap())),
            just("p")
                .ignore_then(
                    just("a")
                        .to(ActorOrEvent::Actor)
                        .or(just("e").to(ActorOrEvent::Event)),
                )
                .then_ignore(just("_"))
                .then(keyword())
                .map(|(t, s)| ExprToken::Constant(Constant::Property(s, t))),
        ))
    }

    fn is_infix(token: &Self::Token) -> bool {
        matches!(token, ExprToken::BinOp(BinOp::And | BinOp::Or))
    }

    fn is_prefix(token: &Self::Token) -> bool {
        matches!(token, ExprToken::MonOp(MonOp::Not))
    }

    fn into_expr(token: Self::Token) -> Self {
        match token {
            ExprToken::Constant(constant) => Expr::Constant(constant),
            ExprToken::BinOp(bin_op) => Expr::Binary(bin_op),
            ExprToken::MonOp(mon_op) => Expr::Unary(mon_op),
            ExprToken::Actor(a) => Expr::Actor(a),
            ExprToken::Event(e) => Expr::Event(e),
            ExprToken::Iota(actor_or_event) => Expr::Unary(MonOp::Iota(actor_or_event)),
            ExprToken::Quantifier(quantifier, actor_or_event) => Expr::Quantifier {
                quantifier,
                var_type: actor_or_event,
            },
        }
    }

    fn bind_var_type(token: &Self::Token) -> PrimitiveVarType {
        match token {
            ExprToken::Iota(_) => PrimitiveVarType::BindVar,
            ExprToken::Quantifier(..) => PrimitiveVarType::BindVarTwoBodies,
            _ => PrimitiveVarType::NoVar,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum Token<'src, T: ParseLot<'src>> {
    OpenDelim,
    ArgSep,
    CloseDelim,
    Lambda(LambdaType, &'src str),
    Variable(&'src str),
    FreeVariable(&'src str, LambdaType),
    LanguageOfThought(T::Token),
}
impl<'src, T> Display for Token<'src, T>
where
    T: ParseLot<'src>,
    T::Token: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::OpenDelim => write!(f, "("),
            Token::ArgSep => write!(f, ","),
            Token::CloseDelim => write!(f, ")"),
            Token::Lambda(lambda_type, t) => write!(f, "lambda {lambda_type} {t}"),
            Token::Variable(v) => write!(f, "{v}"),
            Token::FreeVariable(v, lambda_type) => write!(f, "{v}#{lambda_type}"),
            Token::LanguageOfThought(t) => write!(f, "{t}"),
        }
    }
}

fn lexer<'src, T>()
-> impl Parser<'src, &'src str, Vec<Spanned<Token<'src, T>>>, extra::Err<Rich<'src, char>>>
where
    T: ParseLot<'src> + Clone,
    T::Token: Clone,
{
    choice((
        just(',').to(Token::ArgSep),
        just('(').to(Token::OpenDelim),
        just(')').to(Token::CloseDelim),
        T::tokenizer().map(Token::LanguageOfThought),
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
    .spanned()
    .padded()
    .repeated()
    .collect()
}

fn language_parser<'tokens, 'src: 'tokens, I, T>()
-> impl Parser<'tokens, I, Spanned<ParseTree<'src, T>>, extra::Err<Rich<'tokens, Token<'src, T>>>>
+ Clone
where
    I: ValueInput<'tokens, Token = Token<'src, T>, Span = SimpleSpan> + Clone,
    T: 'tokens + ParseLot<'src> + Clone + PartialEq,
    T::Token: Clone + PartialEq,
{
    let var = select! {
        Token::Variable(a) = e => ParseTree::Variable(a).with_span(e.span()),
        Token::FreeVariable(a, t) = e => ParseTree::FreeVariable(a, t).with_span(e.span())
    }
    .labelled("variable");

    let lot_prim = select! {
        Token::LanguageOfThought(x) = e if T::bind_var_type(&x) == PrimitiveVarType::NoVar && !T::is_infix(&x) => ParseTree::LanguageOfThoughtExpr(T::into_expr(x)).with_span(e.span()),
    }
    .labelled("LOT primitive");

    recursive(|expr: Recursive<_>| {
        let application = choice((
            var,
            lot_prim,
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
            let arg: Spanned<ParseTree<'src, T>> =
                args.pop_front().expect("previous primitive has at least 1");
            let t_span = t.span.union(arg.span);
            let mut tree: chumsky::span::Spanned<ParseTree<T>> = ParseTree::Application {
                subformula: Box::new(t),
                argument: Box::new(arg),
            }
            .with_span(t_span);

            while let Some(x) = args.pop_front() {
                let t_span = tree.span.union(x.span);
                tree = ParseTree::Application {
                    subformula: Box::new(tree),
                    argument: Box::new(x),
                }
                .with_span(t_span);
            }

            tree
        });

        let one_body= select! {
            Token::LanguageOfThought(x) = e if T::bind_var_type(&x) == PrimitiveVarType::BindVar => T::into_expr(x).with_span(e.span()),
        }.then(
            select! {Token::<T>::Variable(x) => x}
            .then_ignore(just(Token::ArgSep))
            .then(expr.clone())
            .delimited_by(just(Token::OpenDelim), just(Token::CloseDelim)))
         .map(|(expr, (var, body)) : (Spanned<T>, _)| {
                let span = expr.span.union(body.span);
                ParseTree::LanguageOfThoughtExprBindOne {
                    expr,
                    body: Box::new(body),
                    var,
                }.with_span(span)
            });

        let two_body = select! {
            Token::LanguageOfThought(x) = e if T::bind_var_type(&x) == PrimitiveVarType::BindVarTwoBodies => T::into_expr(x).with_span(e.span()),
        }.then(select! {Token::<T>::Variable(x) => x}
            .then_ignore(just(Token::ArgSep))
            .then(expr.clone())
            .then_ignore(just(Token::ArgSep))
            .then(expr.clone())
            .delimited_by(just(Token::OpenDelim), just(Token::CloseDelim)))
            .map(|(expr, ((var, body1), body2)): (Spanned<T>, _)| {
                let span = expr.span.union(body2.span);
                ParseTree::LanguageOfThoughtExprBindTwo {
                    expr,
                    body1: Box::new(body1),
                    body2: Box::new(body2),
                    var,
                }
                .with_span(span)
            });

        let atom = choice((
            application,
            var,
            lot_prim,
            one_body,
            two_body,
            expr.delimited_by(just(Token::OpenDelim), just(Token::CloseDelim)),
        ));
        atom.pratt((
            prefix(
                0,
                select! {Token::Lambda(t, var) = e => (t, var, e.span())},
                |(lambda_type, var, lambda_span), r, _| {
                    ParseTree::Lambda {
                        body: Box::new(r),
                        var,
                        lambda_type,
                    }
                    .with_span(lambda_span)
                },
            ),
            prefix(2, select! {Token::LanguageOfThought(x) = e if T::is_prefix(&x) => ParseTree::LanguageOfThoughtExpr(T::into_expr(x)).with_span(e.span())}, |op: Spanned<ParseTree<_>>, x: Spanned<ParseTree<_>>, _| {
                let span= op.span.union(x.span);
                 ParseTree::Application { subformula: Box::new(op), argument: Box::new(x) }.with_span(span)
            }),
            infix(left(1), select! {Token::LanguageOfThought(x) = e if T::is_infix(&x) => ParseTree::LanguageOfThoughtExpr(T::into_expr(x)).with_span(e.span())} , |l: Spanned<ParseTree<_>>, op: Spanned<ParseTree<_>>, r, _| {
                let op_l = op.span.union(l.span);
                let op_span = op_l.union(r.span);

                ParseTree::Application { subformula: Box::new(ParseTree::Application { subformula: Box::new(op), argument: Box::new(l) }.with_span(op_l)),
                    argument: Box::new(r)}.with_span(op_span)
            }),
        ))
    })
}

///A function which maps strings to language of thought expressions. Crucially, it automatically performs all lambda reductions.
pub fn parse_lot<'src, T>(s: &'src str) -> Result<RootedLambdaPool<'src, T>, LambdaParseError>
where
    T: ParseLot<'src> + LambdaLanguageOfThought + Clone + PartialEq + Debug,
    T::Token: Display + Clone + PartialEq + Debug,
{
    let (tokens, token_errs) = lexer::<T>()
        .then_ignore(end())
        .parse(s)
        .into_output_errors();

    let (parse_errs, semantic_errors) = if let Some(tokens) = &tokens {
        let e = tokens
            .iter()
            .map(|x| x.span)
            .reduce(|x, acc| acc.union(x))
            .unwrap();
        let (ast, parse_errs) = language_parser()
            .parse(tokens.as_slice().split_spanned(e))
            .into_output_errors();

        if let Some(ast) = ast {
            match into_pool(ast) {
                Ok(x) => return Ok(x),
                Err(e) => (parse_errs, e),
            }
        } else {
            (parse_errs, Vec::new())
        }
    } else {
        (Vec::new(), Vec::new())
    };

    Err(LambdaParseError(
        token_errs
            .into_iter()
            .map(|e| e.map_token(|c| c.to_string()).into())
            .chain(
                parse_errs
                    .into_iter()
                    .map(|e| e.map_token(|tok| tok.to_string()).into()),
            )
            .chain(semantic_errors)
            .collect(),
        s.to_string(),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

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
            RootedLambdaPool::<Expr>::parse(statement)?;
        }

        for statement in [
            "wow#<e,t>(nice#a)",
            "(wow#<a,<e,t>>(nice#a))(cool#a)",
            "every(x,lambda a y pa_John(y), pa_Blue(y))",
        ] {
            let p = RootedLambdaPool::<Expr>::parse(statement);
            assert!(p.is_err());
        }
        Ok(())
    }
}
