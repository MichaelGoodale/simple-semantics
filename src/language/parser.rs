use std::{collections::HashMap, fmt::Debug};

use crate::{
    Entity,
    lambda::{
        Bvar, LambdaExpr, LambdaExprRef, LambdaPool, ReductionError, RootedLambdaPool,
        types::{LambdaType, TypeError, core_type_parser},
    },
    language::{Constant, Expr, MonOp, lambda_implementation::LambdaConversionError},
};
use chumsky::prelude::*;
use chumsky::{
    extra::ParserExtra,
    label::LabelError,
    text::{TextExpected, inline_whitespace},
    util::MaybeRef,
};

use super::{ActorOrEvent, BinOp, LanguageExpression, Quantifier, Variable};
use thiserror::Error;

#[derive(Debug, Error, Clone)]
pub enum LambdaParseError {
    #[error("ParseError({0})")]
    ParseError(String),

    #[error("You must provide a type for unbound free variable {0} like so \"{0}#<e,t>\"")]
    UnTypedFreeVariable(String),

    #[error("Reduction Error: {0}")]
    ReductionError(#[from] ReductionError),

    #[error("{0}")]
    TypeError(String),

    #[error("Type error: {0}")]
    InnerTypeError(#[from] TypeError),

    #[error("{0}")]
    ConversionError(#[from] LambdaConversionError),
}

impl<'a> From<Vec<Rich<'a, char>>> for LambdaParseError {
    fn from(value: Vec<Rich<'a, char>>) -> Self {
        LambdaParseError::ParseError(
            value
                .into_iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join("\n"),
        )
    }
}

const RESERVED_KEYWORDS: [&str; 11] = [
    "lambda",
    "some",
    "every",
    "some_e",
    "every_e",
    "True",
    "False",
    "all_e",
    "all_a",
    "AgentOf",
    "PatientOf",
];

//TODO: Richer errors that reference where the type error is.
//TODO: Type errors elsewhere

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
                lambda_type: actor_or_event,
                variable,
                restrictor,
                subformula,
            } => {
                let var = variable_names.bind_fresh_quantifier(variable, *actor_or_event);
                let restrictor = restrictor.add_to_pool(pool, variable_names, lambda_depth)?;

                let r_type = pool.get_type(restrictor)?;
                let required_type = match actor_or_event {
                    ActorOrEvent::Actor => LambdaType::at(),
                    ActorOrEvent::Event => LambdaType::et(),
                };
                if &r_type != required_type && &r_type != LambdaType::t() {
                    return Err(LambdaParseError::TypeError(format!(
                        "Quantifier restrictor is {r_type} and not of type {required_type} or t",
                    )));
                }

                let subformula = subformula.add_to_pool(pool, variable_names, lambda_depth)?;
                let sub_type = pool.get_type(subformula)?;
                if &sub_type != LambdaType::t() {
                    return Err(LambdaParseError::TypeError(format!(
                        "Quantifier body is {sub_type} and not of t",
                    )));
                }
                variable_names.unbind(variable);

                LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                    quantifier: *quantifier,
                    var,
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
                variable_names.bind_lambda(var, lambda_depth + 1, lambda_type.clone());
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
#[derive(Debug, Clone, Eq, PartialEq)]
enum ContextVar {
    QuantifierVar(Variable),
    LambdaVar(Bvar, LambdaType),
}

#[derive(Debug, Clone, Eq, PartialEq, Default)]
struct VariableContext<'src>(HashMap<&'src str, Vec<ContextVar>>, u32);

impl<'src> VariableContext<'src> {
    fn to_expr(
        &self,
        variable: &'src str,
        lambda_type: Option<LambdaType>,
        lambda_depth: usize,
    ) -> Result<LambdaExpr<'src, Expr<'src>>, LambdaParseError> {
        //dbg!(&self, variable);
        Ok(match self.0.get(variable) {
            Some(vars) if !vars.is_empty() => match vars
                .last()
                .expect("There should never be an empty vec in the VariableContext")
            {
                ContextVar::QuantifierVar(q) => {
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(*q))
                }
                ContextVar::LambdaVar(og_depth, lambda_type) => {
                    LambdaExpr::BoundVariable(lambda_depth - og_depth, lambda_type.clone())
                }
            },
            //Do free var
            _ => match lambda_type {
                Some(lambda_type) => LambdaExpr::FreeVariable(variable, lambda_type),
                None => {
                    return Err(LambdaParseError::UnTypedFreeVariable(variable.to_string()));
                }
            },
        })
    }

    fn bind_lambda(&mut self, variable: &'src str, lambda_depth: usize, lambda_type: LambdaType) {
        self.0
            .entry(variable)
            .or_default()
            .push(ContextVar::LambdaVar(lambda_depth, lambda_type));
    }

    fn bind_fresh_quantifier(
        &mut self,
        variable: &'src str,
        actor_or_event: ActorOrEvent,
    ) -> Variable {
        let var = actor_or_event.to_variable(self.1);
        self.0
            .entry(variable)
            .or_default()
            .push(ContextVar::QuantifierVar(var));
        self.1 += 1;
        var
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

fn entity<'src, E>() -> impl Parser<'src, &'src str, ParseTree<'src>, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>
        + LabelError<'src, &'src str, &'static str>,
{
    let event = just("e_")
        .ignore_then(text::int(10))
        .map(|num: &str| Entity::Event(num.parse().unwrap()));

    let actor = just("a_").ignore_then(keyword()).map(Entity::Actor);

    choice((actor, event))
        .map(ParseTree::Entity)
        .labelled("entity")
}

fn bool_literal<'src, E>() -> impl Parser<'src, &'src str, ParseTree<'src>, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>,
{
    choice((
        just("True").to(Constant::Tautology),
        just("False").to(Constant::Contradiction),
    ))
    .map(ParseTree::Constant)
}

fn properties<'src, E>(
    expr: impl Parser<'src, &'src str, ParseTree<'src>, E> + Clone,
) -> impl Parser<'src, &'src str, ParseTree<'src>, E> + Clone
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>
        + LabelError<'src, &'src str, &'static str>,
{
    let entity_or_var = choice((entity(), variable(), expr))
        .padded()
        .delimited_by(just('('), just(')'));

    choice((
        just("p")
            .ignore_then(
                just("a")
                    .to(ActorOrEvent::Actor)
                    .or(just("e").to(ActorOrEvent::Event)),
            )
            .then_ignore(just("_"))
            .then(keyword())
            .map(|(a, s)| MonOp::Property(s, a))
            .then(entity_or_var.clone())
            .map(|(x, arg)| ParseTree::Unary(x, Box::new(arg))),
        variable()
            .then(entity_or_var)
            .map(|(x, arg)| ParseTree::Application {
                subformula: Box::new(x),
                argument: Box::new(arg),
            }),
    ))
}

fn sets<'src, E>() -> impl Parser<'src, &'src str, ParseTree<'src>, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>,
{
    choice((
        just("all_a").to(Constant::Everyone),
        just("all_e").to(Constant::EveryEvent),
        just("p")
            .ignore_then(
                just("a")
                    .to(ActorOrEvent::Actor)
                    .or(just("e").to(ActorOrEvent::Event)),
            )
            .then_ignore(just("_"))
            .then(keyword())
            .map(|(a, p): (_, &str)| Constant::Property(p, a)),
    ))
    .map(ParseTree::Constant)
}

fn just_variable<'src, E>() -> impl Parser<'src, &'src str, &'src str, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>
        + LabelError<'src, &'src str, &'static str>,
{
    keyword()
        .and_is(choice(RESERVED_KEYWORDS.map(|x| just(x))).not())
        .and_is(just("e_").ignore_then(text::int(10)).not())
        .and_is(just("a_").ignore_then(keyword()).not())
        .and_is(just("pa_").ignore_then(keyword()).not())
        .and_is(just("pe_").ignore_then(keyword()).not())
        .labelled("variable")
    //This is a stupid way to do it, but I can't get one_of to work for the life of me.
}

fn variable<'src, E>() -> impl Parser<'src, &'src str, ParseTree<'src>, E> + Clone
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>
        + LabelError<'src, &'src str, &'static str>,
{
    choice((
        just_variable()
            .then_ignore(just("#"))
            .then(core_type_parser())
            .map(|(s, lambda_type)| ParseTree::FreeVariable(s, lambda_type)),
        just_variable().map(ParseTree::Variable),
    ))
}

fn binary_operation<'src, E>(
    a: impl Parser<'src, &'src str, ParseTree<'src>, E> + Clone,
    b: impl Parser<'src, &'src str, ParseTree<'src>, E> + Clone,
) -> impl Parser<'src, &'src str, ParseTree<'src>, E> + Clone
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>
        + LabelError<'src, &'src str, &'static str>,
{
    choice((
        just("AgentOf").to(BinOp::AgentOf),
        just("PatientOf").to(BinOp::PatientOf),
    ))
    .then_ignore(just('('))
    .then(a.padded())
    .then_ignore(just(','))
    .then(b.padded())
    .then_ignore(just(')'))
    .map(|((binop, actor), event)| ParseTree::Binary(binop, Box::new(actor), Box::new(event)))
}

fn language_parser<'src, E>() -> impl Parser<'src, &'src str, ParseTree<'src>, E> + Clone
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>
        + LabelError<'src, &'src str, &'static str>,
{
    let ent = entity();
    let var = variable();
    let entity_or_variable = choice((ent, var));

    let true_or_false = bool_literal();
    let possible_sets = sets();
    recursive(|expr| {
        let quantified = choice((
            just("every").to(Quantifier::Universal),
            just("some").to(Quantifier::Existential),
        ))
        .labelled("quantifier")
        .then(just("_e").or_not().map(|s| match s {
            Some(_) => ActorOrEvent::Event,
            None => ActorOrEvent::Actor,
        }))
        .then_ignore(just('('))
        .then(just_variable())
        .then_ignore(just(','))
        .then(expr.clone().padded())
        .then_ignore(just(','))
        .then(expr.clone().padded())
        .then_ignore(just(')'))
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

        let lambda = just("lambda")
            .then(inline_whitespace().at_least(1))
            .ignore_then(core_type_parser().labelled("type label"))
            .then_ignore(inline_whitespace().at_least(1))
            .then(keyword().labelled("lambda variable"))
            .then_ignore(inline_whitespace().at_least(1))
            .then(expr.clone())
            .map(|((lambda_type, var), body)| ParseTree::Lambda {
                body: Box::new(body),
                var,
                lambda_type,
            })
            .labelled("lambda expression");

        let atom = true_or_false
            .or(binary_operation(expr.clone(), expr.clone()))
            .or(properties(lambda.clone()))
            .or(variable())
            .or(lambda)
            .or(quantified)
            .or(expr.clone().delimited_by(just('('), just(')')));

        let neg = just("~")
            .repeated()
            .foldr(atom, |_, b| ParseTree::Unary(MonOp::Not, Box::new(b)));

        let non_quantified = neg.clone().foldl(
            choice((just('&').to(BinOp::And), just('|').to(BinOp::Or)))
                .padded()
                .then(neg.clone())
                .repeated(),
            |lhs, (op, rhs)| ParseTree::Binary(op, Box::new(lhs), Box::new(rhs)),
        );

        choice((
            expr.clone()
                .delimited_by(just('('), just(')'))
                .then(expr.delimited_by(just('('), just(')')))
                .map(|(a, b)| ParseTree::Application {
                    subformula: Box::new(a),
                    argument: Box::new(b),
                }),
            non_quantified,
            possible_sets,
            entity_or_variable,
        ))
    })
}

pub struct UnprocessedParseTree<'a>(ParseTree<'a>);

impl<'a> UnprocessedParseTree<'a> {
    pub fn to_pool(&self) -> Result<RootedLambdaPool<'a, Expr<'a>>, LambdaParseError> {
        self.0.to_pool()
    }
}

///A parsing function that can be used to incorpate LOT parsers into other parsers.
pub fn lot_parser<'src, E>() -> impl Parser<'src, &'src str, UnprocessedParseTree<'src>, E> + Clone
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>
        + LabelError<'src, &'src str, &'static str>,
{
    language_parser().map(UnprocessedParseTree)
}

///A function which maps strings to language of thought expressions. Crucially, it automatically performs all lambda reductions.
pub fn parse_executable<'a>(s: &'a str) -> Result<LanguageExpression<'a>, LambdaParseError> {
    let mut pool = language_parser::<extra::Err<Rich<char>>>()
        .then_ignore(end())
        .parse(s)
        .into_result()?
        .to_pool()?;
    pool.reduce()?;
    Ok(pool.into_pool()?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language::{ExprPool, ExprRef, LanguageResult, VariableBuffer};
    use crate::{Scenario, ThetaRoles};
    use std::collections::HashMap;

    #[test]
    fn parse_entity() {
        for n in [1, 6, 3, 4, 5, 100, 40] {
            let str = format!("e_{n}");
            assert_eq!(
                entity::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                ParseTree::Entity(Entity::Event(n))
            );
        }
        for keyword in ["john", "mary", "phil", "Anna"] {
            let str = format!("a_{keyword}");
            assert_eq!(
                entity::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                ParseTree::Entity(Entity::Actor(keyword))
            );
        }
    }

    #[test]
    fn parse_bin_op() -> anyhow::Result<()> {
        for (s, result) in [
            (
                "AgentOf(a_32, e_2)",
                vec![
                    Expr::Actor("32"),
                    Expr::Event(2),
                    Expr::Binary(BinOp::AgentOf, ExprRef(0), ExprRef(1)),
                ],
            ),
            (
                "PatientOf(a_0, e_1)",
                vec![
                    Expr::Actor("0"),
                    Expr::Event(1),
                    Expr::Binary(BinOp::PatientOf, ExprRef(0), ExprRef(1)),
                ],
            ),
        ] {
            let (pool, root) = binary_operation::<extra::Err<Simple<_>>>(entity(), entity())
                .parse(s)
                .unwrap()
                .to_pool()?
                .into();
            let pool = pool.into_pool(root)?;
            assert_eq!(pool.pool.0, result);
        }
        Ok(())
    }

    #[test]
    fn parse_bool() {
        assert_eq!(
            bool_literal::<extra::Err<Simple<_>>>()
                .parse("True")
                .unwrap(),
            ParseTree::Constant(Constant::Tautology)
        );
        assert_eq!(
            bool_literal::<extra::Err<Simple<_>>>()
                .parse("False")
                .unwrap(),
            ParseTree::Constant(Constant::Contradiction)
        );
    }

    #[test]
    fn parse_sets() {
        assert_eq!(
            sets::<extra::Err<Simple<_>>>().parse("all_e").unwrap(),
            ParseTree::Constant(Constant::EveryEvent),
        );
        assert_eq!(
            sets::<extra::Err<Simple<_>>>().parse("all_a").unwrap(),
            ParseTree::Constant(Constant::Everyone),
        );
        for keyword in ["john", "mary", "phil", "Anna"] {
            let str = format!("pa_{keyword}");
            assert_eq!(
                sets::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                ParseTree::Constant(Constant::Property(keyword, ActorOrEvent::Actor)),
            );
            let str = format!("pe_{keyword}");
            assert_eq!(
                sets::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                ParseTree::Constant(Constant::Property(keyword, ActorOrEvent::Event)),
            );
        }
    }

    fn get_pool(s: &str) -> (ExprPool, ExprRef) {
        let (parse, root) = language_parser::<extra::Err<Rich<char>>>()
            .parse(s)
            .unwrap()
            .to_pool()
            .unwrap()
            .into();
        let LanguageExpression { pool, start } = parse.into_pool(root).unwrap();
        (pool, start)
    }

    fn get_parse<'a>(s: &'a str, simple_scenario: &'a Scenario) -> LanguageResult<'a> {
        let mut variables = VariableBuffer(vec![]);
        let (pool, root) = get_pool(s);
        pool.interp(root, simple_scenario, &mut variables).unwrap()
    }

    fn check_lambdas(
        statement: &str,
        lambda_type: &str,
        gold_pool: LambdaPool<Expr>,
        gold_root: u32,
    ) -> anyhow::Result<()> {
        let (pool, root) = language_parser::<extra::Err<Rich<char>>>()
            .parse(statement)
            .into_result()
            .map_err(|x| {
                anyhow::Error::msg(
                    x.into_iter()
                        .map(|x| x.to_string())
                        .collect::<Vec<_>>()
                        .join("\n"),
                )
            })?
            .to_pool()?
            .into();

        assert_eq!(
            pool.get_type(root)?,
            LambdaType::from_string(lambda_type).map_err(|e| anyhow::anyhow!(e.to_string()))?
        );
        assert_eq!(pool, gold_pool);
        assert_eq!(root, LambdaExprRef(gold_root));

        Ok(())
    }

    #[test]
    fn parse_lambda() -> anyhow::Result<()> {
        check_lambdas(
            "lambda e x (pe_Red(x))",
            "<e,t>",
            LambdaPool::from(vec![
                LambdaExpr::BoundVariable(0, LambdaType::e().clone()),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                    MonOp::Property("Red", ActorOrEvent::Event),
                    ExprRef(0),
                )),
                LambdaExpr::Lambda(LambdaExprRef(1), LambdaType::e().clone()),
            ]),
            2,
        )?;
        check_lambdas(
            "lambda  <e,t> P  (lambda e x (P(x)))",
            "<<e,t>, <e,t>>",
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
            4,
        )?;
        check_lambdas(
            "lambda <a,t> P (P(a_0))",
            "<<a,t>,t>",
            LambdaPool::from(vec![
                LambdaExpr::BoundVariable(0, LambdaType::at().clone()),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Actor("0")),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(0),
                    argument: LambdaExprRef(1),
                },
                LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::at().clone()),
            ]),
            3,
        )?;
        check_lambdas(
            "~hey#<e,t>(lol#e)",
            "t",
            LambdaPool::from(vec![
                LambdaExpr::FreeVariable("hey", LambdaType::et().clone()),
                LambdaExpr::FreeVariable("lol", LambdaType::e().clone()),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(0),
                    argument: LambdaExprRef(1),
                },
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Not, ExprRef(2))),
            ]),
            3,
        )?;

        check_lambdas(
            "(lambda <a,t> P (P(a_0)))(lambda a x (pa_Red(x)))",
            "t",
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
            7,
        )?;
        check_lambdas(
            "lambda t phi (lambda t psi (phi & psi))",
            "<t,<t,t>>",
            LambdaPool::from(vec![
                LambdaExpr::BoundVariable(1, LambdaType::t().clone()),
                LambdaExpr::BoundVariable(0, LambdaType::t().clone()),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(0), ExprRef(1))),
                LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::t().clone()),
                LambdaExpr::Lambda(LambdaExprRef(3), LambdaType::t().clone()),
            ]),
            4,
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
        let mut properties: HashMap<_, _, ahash::RandomState> = HashMap::default();

        properties.insert("Red", vec![Entity::Actor("John")]);
        properties.insert("Blue", vec![Entity::Actor("Mary"), Entity::Actor("John")]);

        let scenario = Scenario {
            question: None,
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
            assert_eq!(expression.run(&scenario)?, LanguageResult::Bool(true));
        }

        for (statement, result) in [
            ("a_Mary", LanguageResult::Actor("Mary")),
            ("pa_Red", LanguageResult::ActorSet(vec!["John"])),
            ("pa_Blue", LanguageResult::ActorSet(vec!["Mary", "John"])),
        ] {
            println!("{statement}");
            let expression = parse_executable(statement)?;
            assert_eq!(expression.run(&scenario)?, result);
        }

        Ok(())
    }

    #[test]
    fn parse_test() -> anyhow::Result<()> {
        let mut properties: HashMap<_, _, ahash::RandomState> = HashMap::default();

        properties.insert("Red", vec![Entity::Actor("John")]);
        properties.insert("Blue", vec![Entity::Actor("Mary"), Entity::Actor("John")]);

        let scenario = Scenario {
            question: None,
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
            assert_eq!(get_parse(statement, &scenario), LanguageResult::Bool(true));
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
            assert_eq!(get_parse(statement, &scenario), result);
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
