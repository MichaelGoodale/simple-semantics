use std::{collections::HashMap, fmt::Debug};

use crate::{
    Entity, LabelledScenarios,
    lambda::{
        Bvar, LambdaExpr, LambdaExprRef, LambdaPool, ReductionError, RootedLambdaPool,
        types::{LambdaType, core_type_parser},
    },
    language::{Constant, Expr, ExprRef, MonOp, lambda_implementation::LambdaConversionError},
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

impl<'src> ParseTree<'src> {
    fn add_to_pool(
        &'src self,
        pool: &mut LambdaPool<Expr>,
        labels: &mut LabelledScenarios,
        variable_names: &mut VariableContext<'src>,
        lambda_depth: usize,
    ) -> Result<LambdaExprRef, LambdaParseError> {
        let expr = match &self {
            ParseTree::Constant(c) => LambdaExpr::LanguageOfThoughtExpr(Expr::Constant(match c {
                LabeledConstant::Constant(x) => *x,
                LabeledConstant::LabeledProperty(p, a) => {
                    Constant::Property(labels.get_property_label(p), *a)
                }
            })),
            ParseTree::Entity(e) => LambdaExpr::LanguageOfThoughtExpr(match e {
                LabeledEntity::Unlabeled(entity) => match entity {
                    Entity::Actor(a) => Expr::Actor(*a),
                    Entity::Event(e) => Expr::Event(*e),
                },
                LabeledEntity::LabeledActor(label) => Expr::Actor(labels.get_actor_label(label)),
            }),
            ParseTree::Unary(m, x) => {
                let x = ExprRef(x.add_to_pool(pool, labels, variable_names, lambda_depth)?.0);
                let m = match m {
                    LabeledProperty::Property(mon_op) => *mon_op,
                    LabeledProperty::LabeledProperty(label, a) => {
                        MonOp::Property(labels.get_property_label(label), *a)
                    }
                };
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(m, x))
            }
            ParseTree::Binary(b, x, y) => {
                let x = ExprRef(x.add_to_pool(pool, labels, variable_names, lambda_depth)?.0);
                let y = ExprRef(y.add_to_pool(pool, labels, variable_names, lambda_depth)?.0);
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(*b, x, y))
            }
            ParseTree::Quantifier {
                quantifier,
                lambda_type,
                variable,
                restrictor,
                subformula,
            } => {
                let var = variable_names.bind_fresh_quantifier(variable, *lambda_type);
                let restrictor = ExprRef(
                    restrictor
                        .add_to_pool(pool, labels, variable_names, lambda_depth)?
                        .0,
                );

                let subformula = ExprRef(
                    subformula
                        .add_to_pool(pool, labels, variable_names, lambda_depth)?
                        .0,
                );
                variable_names.unbind(variable);
                LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                    quantifier: *quantifier,
                    var,
                    restrictor,
                    subformula,
                })
            }
            ParseTree::Application {
                subformula,
                argument,
            } => {
                let subformula =
                    subformula.add_to_pool(pool, labels, variable_names, lambda_depth)?;
                let argument = argument.add_to_pool(pool, labels, variable_names, lambda_depth)?;
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
                let body = body.add_to_pool(pool, labels, variable_names, lambda_depth + 1)?;
                variable_names.unbind(var);
                LambdaExpr::Lambda(body, lambda_type.clone())
            }
            ParseTree::Variable(var) => variable_names.to_expr(var, labels, None, lambda_depth)?,
            ParseTree::FreeVariable(var, lambda_type) => {
                variable_names.to_expr(var, labels, Some(lambda_type.clone()), lambda_depth)?
            }
        };
        Ok(pool.add(expr))
    }

    fn to_pool(
        &self,
        labels: &mut LabelledScenarios,
    ) -> Result<RootedLambdaPool<Expr>, LambdaParseError> {
        let mut pool = LambdaPool::new();

        let mut var_labels = VariableContext::default();
        let root = self.add_to_pool(&mut pool, labels, &mut var_labels, 0)?;
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
        labels: &mut LabelledScenarios,
        lambda_type: Option<LambdaType>,
        lambda_depth: usize,
    ) -> Result<LambdaExpr<Expr>, LambdaParseError> {
        Ok(match self.0.get(variable) {
            Some(vars) => match vars
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
            None => LambdaExpr::FreeVariable(
                labels.get_free_variable(variable),
                match lambda_type {
                    Some(x) => x,
                    None => {
                        return Err(LambdaParseError::UnTypedFreeVariable(variable.to_string()));
                    }
                },
            ),
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
        var: String,
    },
    Variable(&'src str),
    FreeVariable(&'src str, LambdaType),
    Application {
        subformula: Box<ParseTree<'src>>,
        argument: Box<ParseTree<'src>>,
    },
    Constant(LabeledConstant<'src>),
    Unary(LabeledProperty<'src>, Box<ParseTree<'src>>),
    Binary(BinOp, Box<ParseTree<'src>>, Box<ParseTree<'src>>),
    Quantifier {
        quantifier: Quantifier,
        lambda_type: ActorOrEvent,
        variable: &'src str,
        restrictor: Box<ParseTree<'src>>,
        subformula: Box<ParseTree<'src>>,
    },
    Entity(LabeledEntity<'src>),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum LabeledEntity<'a> {
    Unlabeled(Entity),
    LabeledActor(&'a str),
}

fn entity<'src, E>() -> impl Parser<'src, &'src str, ParseTree<'src>, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>
        + LabelError<'src, &'src str, &'static str>,
{
    let actor_or_event_number = one_of("ae")
        .then(text::int(10))
        .map(|(c, num): (char, &str)| {
            LabeledEntity::Unlabeled(match c {
                'a' => Entity::Actor(num.parse().unwrap()),
                'e' => Entity::Event(num.parse().unwrap()),
                _ => panic!("Unreachable because of one_of"),
            })
        });

    let actor_or_event_keyword = just("a_")
        .ignore_then(text::ident())
        .map(LabeledEntity::LabeledActor);

    choice((actor_or_event_keyword, actor_or_event_number))
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
    .map(|x| ParseTree::Constant(LabeledConstant::Constant(x)))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LabeledConstant<'a> {
    Constant(Constant),
    LabeledProperty(&'a str, ActorOrEvent),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LabeledProperty<'a> {
    Property(MonOp),
    LabeledProperty(&'a str, ActorOrEvent),
}

fn properties<'src, E>() -> impl Parser<'src, &'src str, ParseTree<'src>, E> + Clone
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>
        + LabelError<'src, &'src str, &'static str>,
{
    let entity_or_var = choice((entity(), variable()))
        .padded()
        .delimited_by(just('('), just(')'));

    choice((
        just("p")
            .ignore_then(
                just("a")
                    .to(ActorOrEvent::Actor)
                    .or(just("e").to(ActorOrEvent::Event)),
            )
            .then(text::int(10))
            .map(|(a, p): (_, &str)| MonOp::Property(p.parse().unwrap(), a))
            .map(LabeledProperty::Property)
            .or(just("p")
                .ignore_then(
                    just("a")
                        .to(ActorOrEvent::Actor)
                        .or(just("e").to(ActorOrEvent::Event)),
                )
                .then_ignore(just("_"))
                .then(text::ident())
                .map(|(a, p)| LabeledProperty::LabeledProperty(p, a)))
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
            .then(text::int(10))
            .map(|(a, p): (_, &str)| Constant::Property(p.parse().unwrap(), a)),
    ))
    .map(LabeledConstant::Constant)
    .or(just("p")
        .ignore_then(
            just("a")
                .to(ActorOrEvent::Actor)
                .or(just("e").to(ActorOrEvent::Event)),
        )
        .then_ignore(just("_"))
        .then(text::ident())
        .map(|(a, p)| LabeledConstant::LabeledProperty(p, a)))
    .map(ParseTree::Constant)
}

fn just_variable<'src, E>() -> impl Parser<'src, &'src str, &'src str, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>
        + LabelError<'src, &'src str, &'static str>,
{
    text::ident::<&'src str, E>()
        .and_is(choice(RESERVED_KEYWORDS.map(|x| just(x))).not())
        .and_is(one_of("ae").ignore_then(text::int(10)).not())
        .and_is(
            just("p")
                .ignore_then(one_of("ae"))
                .ignore_then(text::int(10))
                .not(),
        )
        .and_is(just("a_").ignore_then(text::ident()).not())
        .and_is(just("pa_").ignore_then(text::ident()).not())
        .and_is(just("pe_").ignore_then(text::ident()).not())
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
        let atom = true_or_false
            .or(binary_operation(expr.clone(), expr.clone()))
            .or(properties())
            .or(variable())
            .or(expr.clone().delimited_by(just('('), just(')')));

        let neg = just("~").repeated().foldr(atom, |_, b| {
            ParseTree::Unary(LabeledProperty::Property(MonOp::Not), Box::new(b))
        });

        let non_quantified = neg.clone().foldl(
            choice((just('&').to(BinOp::And), just('|').to(BinOp::Or)))
                .padded()
                .then(neg.clone())
                .repeated(),
            |lhs, (op, rhs)| ParseTree::Binary(op, Box::new(lhs), Box::new(rhs)),
        );

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
            .then(text::ident().padded().labelled("lambda variable"))
            .then(expr.clone().delimited_by(just('('), just(')')))
            .map(|((lambda_type, var_name), body)| ParseTree::Lambda {
                body: Box::new(body),
                var: var_name.to_string(),
                lambda_type,
            })
            .labelled("lambda expression");

        choice((
            expr.clone()
                .delimited_by(just('('), just(')'))
                .then(expr.delimited_by(just('('), just(')')))
                .map(|(a, b)| ParseTree::Application {
                    subformula: Box::new(a),
                    argument: Box::new(b),
                }),
            lambda,
            non_quantified,
            quantified,
            possible_sets,
            entity_or_variable,
        ))
    })
}

type ExtraType<'a> = extra::Full<Rich<'a, char>, extra::SimpleState<LabelledScenarios>, ()>;

pub struct UnprocessedParseTree<'a>(ParseTree<'a>);

impl UnprocessedParseTree<'_> {
    pub fn to_pool(
        &self,
        labels: &mut LabelledScenarios,
    ) -> Result<RootedLambdaPool<Expr>, LambdaParseError> {
        self.0.to_pool(labels)
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
pub fn parse_executable(
    s: &str,
    labels: &mut LabelledScenarios,
) -> Result<LanguageExpression, LambdaParseError> {
    let mut pool = language_parser::<extra::Err<Rich<char>>>()
        .then_ignore(end())
        .parse(s)
        .into_result()?
        .to_pool(labels)?;
    pool.reduce()?;
    Ok(pool.into_pool()?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language::{ExprPool, LanguageResult, VariableBuffer};
    use crate::{LabelledScenarios, Scenario, ThetaRoles};
    use std::collections::HashMap;

    #[test]
    fn parse_entity() {
        for n in [1, 6, 3, 4, 5, 100, 40] {
            let str = format!("a{n}");
            assert_eq!(
                entity::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                ParseTree::Entity(LabeledEntity::Unlabeled(Entity::Actor(n.into())))
            );
            let str = format!("e{n}");
            assert_eq!(
                entity::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                ParseTree::Entity(LabeledEntity::Unlabeled(Entity::Event(n)))
            );
        }
        for keyword in ["john", "mary", "phil", "Anna"] {
            let str = format!("a_{keyword}");
            assert_eq!(
                entity::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                ParseTree::Entity(LabeledEntity::LabeledActor(keyword))
            );
        }
    }

    #[test]
    fn parse_bin_op() -> anyhow::Result<()> {
        let mut labels = LabelledScenarios::default();

        for (s, result) in [
            (
                "AgentOf(a32, e2)",
                vec![
                    Expr::Actor(32),
                    Expr::Event(2),
                    Expr::Binary(BinOp::AgentOf, ExprRef(0), ExprRef(1)),
                ],
            ),
            (
                "PatientOf(a0, e1)",
                vec![
                    Expr::Actor(0),
                    Expr::Event(1),
                    Expr::Binary(BinOp::PatientOf, ExprRef(0), ExprRef(1)),
                ],
            ),
        ] {
            let (pool, root) = binary_operation::<extra::Err<Simple<_>>>(entity(), entity())
                .parse(s)
                .unwrap()
                .to_pool(&mut labels)?
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
            ParseTree::Constant(LabeledConstant::Constant(Constant::Tautology))
        );
        assert_eq!(
            bool_literal::<extra::Err<Simple<_>>>()
                .parse("False")
                .unwrap(),
            ParseTree::Constant(LabeledConstant::Constant(Constant::Contradiction))
        );
    }

    #[test]
    fn parse_sets() {
        for n in [1, 6, 3, 4, 5, 100, 1032, 40343] {
            let str = format!("pa{n}");
            assert_eq!(
                sets::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                ParseTree::Constant(LabeledConstant::Constant(Constant::Property(
                    n,
                    ActorOrEvent::Actor
                )))
            );
            let str = format!("pe{n}");
            assert_eq!(
                sets::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                ParseTree::Constant(LabeledConstant::Constant(Constant::Property(
                    n,
                    ActorOrEvent::Event
                ))),
            );
        }
        assert_eq!(
            sets::<extra::Err<Simple<_>>>().parse("all_e").unwrap(),
            ParseTree::Constant(LabeledConstant::Constant(Constant::EveryEvent)),
        );
        assert_eq!(
            sets::<extra::Err<Simple<_>>>().parse("all_a").unwrap(),
            ParseTree::Constant(LabeledConstant::Constant(Constant::Everyone)),
        );
        for keyword in ["john", "mary", "phil", "Anna"] {
            let str = format!("pa_{keyword}");
            assert_eq!(
                sets::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                ParseTree::Constant(LabeledConstant::LabeledProperty(
                    keyword,
                    ActorOrEvent::Actor
                )),
            );
        }
    }

    fn get_pool(s: &str) -> (ExprPool, ExprRef) {
        let mut labels = LabelledScenarios::default();
        let (parse, root) = language_parser::<extra::Err<Rich<char>>>()
            .parse(s)
            .unwrap()
            .to_pool(&mut labels)
            .unwrap()
            .into();
        let LanguageExpression { pool, start } = parse.into_pool(root).unwrap();
        (pool, start)
    }

    fn get_parse(s: &str, simple_scenario: &Scenario) -> LanguageResult {
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
        print!("{statement}");
        let mut properties: HashMap<_, _, ahash::RandomState> = HashMap::default();

        properties.insert(1, vec![Entity::Actor(1)]);
        properties.insert(4, vec![Entity::Actor(0), Entity::Actor(1)]);

        let simple_scenario = Scenario {
            question: None,
            actors: vec![0, 1],
            thematic_relations: vec![
                ThetaRoles {
                    agent: Some(0),
                    patient: Some(0),
                },
                ThetaRoles {
                    agent: Some(1),
                    patient: Some(0),
                },
            ],
            properties,
        };

        let actor_labels =
            HashMap::from_iter([("John", 1), ("Mary", 0)].map(|(x, y)| (x.to_string(), y)));
        let property_labels =
            HashMap::from_iter([("Red", 1), ("Blue", 4)].map(|(x, y)| (x.to_string(), y)));
        let mut labels = LabelledScenarios {
            scenarios: vec![simple_scenario],
            actor_labels,
            property_labels,
            free_variables: HashMap::default(),
            sentences: vec![],
            lemmas: vec![],
        };
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
            .to_pool(&mut labels)?
            .into();

        assert_eq!(
            pool.get_type(root)?,
            LambdaType::from_string(lambda_type).map_err(|e| anyhow::anyhow!(e.to_string()))?
        );
        assert_eq!(pool, gold_pool);
        assert_eq!(root, LambdaExprRef(gold_root));

        //try again with the context-sensitive parser
        let mut label_state = labels.clone();
        let (pool, root) = lot_parser::<extra::Err<Rich<_>>>()
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
            .to_pool(&mut label_state)?
            .into();

        assert_eq!(pool, gold_pool);
        assert_eq!(root, LambdaExprRef(gold_root));
        println!(" is good!");
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
                    MonOp::Property(1, ActorOrEvent::Event),
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
            "lambda <a,t> P (P(a0))",
            "<<a,t>,t>",
            LambdaPool::from(vec![
                LambdaExpr::BoundVariable(0, LambdaType::at().clone()),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Actor(0)),
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
                LambdaExpr::FreeVariable(0, LambdaType::et().clone()),
                LambdaExpr::FreeVariable(1, LambdaType::e().clone()),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(0),
                    argument: LambdaExprRef(1),
                },
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Not, ExprRef(2))),
            ]),
            3,
        )?;

        check_lambdas(
            "(lambda <a,t> P (P(a0)))(lambda a x (pa_Red(x)))",
            "t",
            LambdaPool::from(vec![
                LambdaExpr::BoundVariable(0, LambdaType::at().clone()),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Actor(0)),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(0),
                    argument: LambdaExprRef(1),
                },
                LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::at().clone()),
                LambdaExpr::BoundVariable(0, LambdaType::a().clone()),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                    MonOp::Property(1, ActorOrEvent::Actor),
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
        let mut properties: HashMap<_, _, ahash::RandomState> = HashMap::default();

        properties.insert(1, vec![Entity::Actor(1)]);
        properties.insert(4, vec![Entity::Actor(0), Entity::Actor(1)]);

        let simple_scenario = Scenario {
            question: None,
            actors: vec![0, 1],
            thematic_relations: vec![
                ThetaRoles {
                    agent: Some(0),
                    patient: Some(0),
                },
                ThetaRoles {
                    agent: Some(1),
                    patient: Some(0),
                },
            ],
            properties,
        };

        let actor_labels =
            HashMap::from_iter([("John", 1), ("Mary", 0)].map(|(x, y)| (x.to_string(), y)));
        let property_labels =
            HashMap::from_iter([("Red", 1), ("Blue", 4)].map(|(x, y)| (x.to_string(), y)));
        let mut labels = LabelledScenarios {
            scenarios: vec![simple_scenario],
            actor_labels,
            property_labels,
            free_variables: HashMap::default(),
            sentences: vec![],
            lemmas: vec![],
        };
        parse_executable(
            "(lambda <a,t> P (P(a0)))(lambda a x (pa_Red(x)))",
            &mut labels,
        )?;
        Ok(())
    }

    #[test]
    fn parse_with_keywords() -> anyhow::Result<()> {
        let mut properties: HashMap<_, _, ahash::RandomState> = HashMap::default();

        properties.insert(1, vec![Entity::Actor(1)]);
        properties.insert(4, vec![Entity::Actor(0), Entity::Actor(1)]);

        let simple_scenario = Scenario {
            question: None,
            actors: vec![0, 1],
            thematic_relations: vec![
                ThetaRoles {
                    agent: Some(0),
                    patient: Some(0),
                },
                ThetaRoles {
                    agent: Some(1),
                    patient: Some(0),
                },
            ],
            properties,
        };

        let actor_labels =
            HashMap::from_iter([("John", 1), ("Mary", 0)].map(|(x, y)| (x.to_string(), y)));
        let property_labels =
            HashMap::from_iter([("Red", 1), ("Blue", 4)].map(|(x, y)| (x.to_string(), y)));
        let mut labels = LabelledScenarios {
            scenarios: vec![simple_scenario.clone()],
            actor_labels,
            property_labels,
            free_variables: HashMap::default(),
            sentences: vec![],
            lemmas: vec![],
        };

        for statement in [
            "~AgentOf(a_John, e0)",
            "pa_Red(a_John) & ~pa_Red(a_Mary)",
            "pa_Red(a_John) & ~pa_Red(a_Mary) & pa_Red(a_John)",
            "~(pa_Red(a_John) & ~(True & pa_Red(a_John)))",
            "every(x0, all_a, pa_Blue(x0))",
            "every(x0, pa_Blue, pa_Blue(x0))",
            "every(x, pa1, pa4(x))",
            "every(x0, pa_Red, pa_Blue(x0))",
            "every_e(x0, all_e, (some(x1, all_a, AgentOf(x1, x0))))",
            "every_e(x0, all_e, (some(x1, all_a, PatientOf(x1, x0))))",
            "every_e(x0, all_e, PatientOf(a_Mary, x0))",
            "some(x0, (PatientOf(x0, e0) & PatientOf(x0, e1)), pa_Blue(x0))",
        ] {
            println!("{statement}");
            let expression = parse_executable(statement, &mut labels)?;
            assert_eq!(
                expression.run(&labels.scenarios[0])?,
                LanguageResult::Bool(true)
            );
        }

        for (statement, result) in [
            ("a_Mary", LanguageResult::Actor(0)),
            ("pa_Red", LanguageResult::ActorSet(vec![1])),
            ("pa_Blue", LanguageResult::ActorSet(vec![0, 1])),
        ] {
            println!("{statement}");
            let expression = parse_executable(statement, &mut labels)?;
            assert_eq!(expression.run(&labels.scenarios[0])?, result);
        }

        Ok(())
    }

    #[test]
    fn parse_test() -> anyhow::Result<()> {
        let mut properties: HashMap<_, _, ahash::RandomState> = HashMap::default();

        properties.insert(1, vec![Entity::Actor(1)]);
        properties.insert(4, vec![Entity::Actor(0), Entity::Actor(1)]);

        let simple_scenario = Scenario {
            question: None,
            actors: vec![0, 1],
            thematic_relations: vec![
                ThetaRoles {
                    agent: Some(0),
                    patient: Some(0),
                },
                ThetaRoles {
                    agent: Some(1),
                    patient: Some(0),
                },
            ],
            properties,
        };

        for statement in [
            "True",
            "~~~False",
            "~AgentOf(a1, e0)",
            "~(True & False)",
            "True | False",
            "(True & False) | True",
            "~(True & False) | False",
            "pa1(a1) & ~pa1(a0)",
            "pa1(a1) & ~pa1(a0) & pa1(a1)",
            "~(pa1(a1) & ~(True & pa1(a1)))",
            "every(x0, all_a, pa4(x0))",
            "every(x0, pa4, pa4(x0))",
            "every_e(x0, all_e, (some(x1, all_a, AgentOf(x1, x0))))",
            "every_e(x0, all_e, (some(x1, all_a, PatientOf(x1, x0))))",
            "every_e(x0, all_e, PatientOf(a0, x0))",
            "some(x0, (PatientOf(x0, e0) & PatientOf(x0, e1)), pa4(x0))",
        ] {
            println!("{statement}");
            assert_eq!(
                get_parse(statement, &simple_scenario),
                LanguageResult::Bool(true)
            );
        }
        for (statement, result) in [
            ("a0", LanguageResult::Actor(0)),
            ("e0", LanguageResult::Event(0)),
            ("all_e", LanguageResult::EventSet(vec![0, 1])),
            ("all_a", LanguageResult::ActorSet(vec![0, 1])),
            ("pa1", LanguageResult::ActorSet(vec![1])),
            ("pa4", LanguageResult::ActorSet(vec![0, 1])),
        ] {
            println!("{statement}");
            assert_eq!(get_parse(statement, &simple_scenario), result);
        }

        Ok(())
    }
}
