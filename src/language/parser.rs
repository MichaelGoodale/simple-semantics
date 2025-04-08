use std::{collections::HashMap, fmt::Debug};

use crate::{
    lambda::{
        types::{core_type_parser, LambdaType},
        Bvar, LambdaExpr, LambdaExprRef, LambdaPool, RootedLambdaPool,
    },
    language::{Constant, Expr, ExprRef, MonOp},
    Entity, LabelledScenarios,
};
use anyhow::bail;
use chumsky::prelude::*;
use chumsky::{
    extra::ParserExtra,
    label::LabelError,
    text::{inline_whitespace, TextExpected},
    util::MaybeRef,
};

use super::{BinOp, LanguageExpression, Quantifier, Variable};

const RESERVED_KEYWORDS: [&str; 9] = [
    "lambda",
    "some",
    "every",
    "True",
    "False",
    "all_e",
    "all_a",
    "AgentOf",
    "PatientOf",
];

#[derive(Debug, Clone, Eq, PartialEq)]
enum ParsingType {
    E,
    T,
    Composition(Option<Box<Self>>, Option<Box<Self>>),
    Unknown,
}

impl TryFrom<&ParsingType> for LambdaType {
    type Error = ();

    fn try_from(value: &ParsingType) -> Result<Self, Self::Error> {
        match value {
            ParsingType::E => Ok(LambdaType::E),
            ParsingType::T => Ok(LambdaType::T),
            ParsingType::Composition(Some(lhs), Some(rhs)) => Ok(LambdaType::Composition(
                Box::new(LambdaType::try_from(lhs.as_ref())?),
                Box::new(LambdaType::try_from(rhs.as_ref())?),
            )),
            _ => Err(()),
        }
    }
}
impl TryFrom<ParsingType> for LambdaType {
    type Error = ();
    fn try_from(value: ParsingType) -> Result<Self, Self::Error> {
        (&value).try_into()
    }
}

impl From<LambdaType> for ParsingType {
    fn from(value: LambdaType) -> Self {
        (&value).into()
    }
}

impl From<&LambdaType> for ParsingType {
    fn from(value: &LambdaType) -> Self {
        match value {
            LambdaType::E => ParsingType::E,
            LambdaType::T => ParsingType::T,
            LambdaType::Composition(lhs, rhs) => ParsingType::Composition(
                Some(Box::new(ParsingType::from(lhs.as_ref()))),
                Some(Box::new(ParsingType::from(rhs.as_ref()))),
            ),
        }
    }
}

impl ParsingType {
    fn et() -> Self {
        ParsingType::Composition(
            Some(Box::new(ParsingType::E)),
            Some(Box::new(ParsingType::T)),
        )
    }
    fn eet() -> Self {
        ParsingType::Composition(
            Some(Box::new(ParsingType::E)),
            Some(Box::new(ParsingType::et())),
        )
    }

    fn to_lambda_type(&self) -> anyhow::Result<LambdaType> {
        Ok(match self {
            ParsingType::E => LambdaType::E,
            ParsingType::T => LambdaType::T,
            ParsingType::Composition(Some(a), Some(b)) => LambdaType::Composition(
                Box::new(a.to_lambda_type()?),
                Box::new(b.to_lambda_type()?),
            ),
            _ => bail!("Cannot convert unknown type"),
        })
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct TypedParseTree<'src>(ParseTree<'src>, ParsingType);

impl<'src> TypedParseTree<'src> {
    fn add_to_pool(
        &'src self,
        pool: &mut LambdaPool<Expr>,
        labels: &mut LabelledScenarios,
        variable_names: &mut VariableContext<'src>,
        lambda_depth: usize,
    ) -> LambdaExprRef {
        let expr = match &self.0 {
            ParseTree::Constant(c) => LambdaExpr::LanguageOfThoughtExpr(Expr::Constant(match c {
                LabeledConstant::Constant(x) => *x,
                LabeledConstant::LabeledProperty(p) => {
                    Constant::Property(labels.get_property_label(p))
                }
            })),
            ParseTree::Entity(e) => LambdaExpr::LanguageOfThoughtExpr(Expr::Entity(match e {
                LabeledEntity::Unlabeled(entity) => *entity,
                LabeledEntity::LabeledActor(label) => Entity::Actor(labels.get_actor_label(label)),
            })),
            ParseTree::Unary(m, x) => {
                let x = ExprRef(x.add_to_pool(pool, labels, variable_names, lambda_depth).0);
                let m = match m {
                    LabeledProperty::Property(mon_op) => *mon_op,
                    LabeledProperty::LabeledProperty(label) => {
                        MonOp::Property(labels.get_property_label(label))
                    }
                };
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(m, x))
            }
            ParseTree::Binary(b, x, y) => {
                let x = ExprRef(x.add_to_pool(pool, labels, variable_names, lambda_depth).0);
                let y = ExprRef(y.add_to_pool(pool, labels, variable_names, lambda_depth).0);
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(*b, x, y))
            }
            ParseTree::Quantifier {
                quantifier,
                variable,
                restrictor,
                subformula,
            } => {
                let var = variable_names.bind_fresh_quantifier(variable);
                let restrictor = ExprRef(
                    restrictor
                        .add_to_pool(pool, labels, variable_names, lambda_depth)
                        .0,
                );

                let subformula = ExprRef(
                    subformula
                        .add_to_pool(pool, labels, variable_names, lambda_depth)
                        .0,
                );
                variable_names.unbind(variable);
                LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                    quantifier: *quantifier,
                    var: Variable(var),
                    restrictor,
                    subformula,
                })
            }
            ParseTree::Application {
                subformula,
                argument,
            } => {
                let subformula = subformula.add_to_pool(pool, labels, variable_names, lambda_depth);
                let argument = argument.add_to_pool(pool, labels, variable_names, lambda_depth);
                LambdaExpr::Application {
                    subformula,
                    argument,
                }
            }
            ParseTree::Lambda { body, var } => {
                let arg_type: LambdaType = (&self.1).try_into().unwrap();
                variable_names.bind_lambda(var, lambda_depth + 1, arg_type.clone());
                let body = body.add_to_pool(pool, labels, variable_names, lambda_depth + 1);
                variable_names.unbind(var);
                LambdaExpr::Lambda(body, arg_type)
            }
            ParseTree::Variable(var) => variable_names.to_expr(var, labels, &self.1, lambda_depth),
        };
        pool.add(expr)
    }

    fn to_pool(&self, labels: &mut LabelledScenarios) -> RootedLambdaPool<Expr> {
        let mut pool = LambdaPool::new();

        let mut var_labels = VariableContext::default();
        let root = self.add_to_pool(&mut pool, labels, &mut var_labels, 0);
        RootedLambdaPool::new(pool, root)
    }
}
#[derive(Debug, Clone, Eq, PartialEq)]
enum ContextVar {
    QuantifierVar(u32),
    LambdaVar(Bvar, LambdaType),
}

#[derive(Debug, Clone, Eq, PartialEq, Default)]
struct VariableContext<'src>(HashMap<&'src str, Vec<ContextVar>>, u32);

impl<'src> VariableContext<'src> {
    fn to_expr(
        &self,
        variable: &'src str,
        labels: &mut LabelledScenarios,
        lambda_type: &ParsingType,
        lambda_depth: usize,
    ) -> LambdaExpr<Expr> {
        match self.0.get(variable) {
            Some(vars) => match vars
                .last()
                .expect("There should never be an empty vec in the VariableContext")
            {
                ContextVar::QuantifierVar(q) => {
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(Variable(*q)))
                }
                ContextVar::LambdaVar(og_depth, lambda_type) => {
                    LambdaExpr::BoundVariable(lambda_depth - og_depth, lambda_type.clone())
                }
            },
            None => LambdaExpr::FreeVariable(
                labels.get_free_variable(variable),
                lambda_type.to_lambda_type().unwrap(),
            ),
        }
    }

    fn bind_lambda(&mut self, variable: &'src str, lambda_depth: usize, lambda_type: LambdaType) {
        self.0
            .entry(variable)
            .or_default()
            .push(ContextVar::LambdaVar(lambda_depth, lambda_type));
    }

    fn bind_fresh_quantifier(&mut self, variable: &'src str) -> u32 {
        let n = self.1;
        self.0
            .entry(variable)
            .or_default()
            .push(ContextVar::QuantifierVar(n));
        self.1 += 1;
        n
    }

    fn unbind(&mut self, variable: &'src str) {
        self.0.get_mut(variable).unwrap().pop();
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum ParseTree<'src> {
    Lambda {
        body: Box<TypedParseTree<'src>>,
        var: String,
    },
    Variable(&'src str),
    Application {
        subformula: Box<TypedParseTree<'src>>,
        argument: Box<TypedParseTree<'src>>,
    },
    Constant(LabeledConstant<'src>),
    Unary(LabeledProperty<'src>, Box<TypedParseTree<'src>>),
    Binary(BinOp, Box<TypedParseTree<'src>>, Box<TypedParseTree<'src>>),
    Quantifier {
        quantifier: Quantifier,
        variable: &'src str,
        restrictor: Box<TypedParseTree<'src>>,
        subformula: Box<TypedParseTree<'src>>,
    },
    Entity(LabeledEntity<'src>),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum LabeledEntity<'a> {
    Unlabeled(Entity),
    LabeledActor(&'a str),
}

fn entity<'src, E>() -> impl Parser<'src, &'src str, TypedParseTree<'src>, E> + Copy
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
        .map(|x| TypedParseTree(ParseTree::Entity(x), ParsingType::E))
        .labelled("entity")
}

fn bool_literal<'src, E>() -> impl Parser<'src, &'src str, TypedParseTree<'src>, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>,
{
    choice((
        just("True").to(Constant::Tautology),
        just("False").to(Constant::Contradiction),
    ))
    .map(|x| {
        TypedParseTree(
            ParseTree::Constant(LabeledConstant::Constant(x)),
            ParsingType::T,
        )
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LabeledConstant<'a> {
    Constant(Constant),
    LabeledProperty(&'a str),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LabeledProperty<'a> {
    Property(MonOp),
    LabeledProperty(&'a str),
}

fn properties<'src, E>() -> impl Parser<'src, &'src str, TypedParseTree<'src>, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>
        + LabelError<'src, &'src str, &'static str>,
{
    let var_expr = variable().map(|x| (true, TypedParseTree(x.0, ParsingType::E)));
    let entity_expr = entity().map(|x| (false, x));
    let entity_or_var = choice((entity_expr, var_expr))
        .padded()
        .delimited_by(just('('), just(')'));

    choice((
        just("p")
            .ignore_then(text::int(10))
            .map(|p: &str| MonOp::Property(p.parse().unwrap()))
            .map(LabeledProperty::Property)
            .or(just("p_")
                .ignore_then(text::ident())
                .map(LabeledProperty::LabeledProperty))
            .then(entity_or_var)
            .map(|(x, (arg_is_lambdavar, arg))| {
                TypedParseTree(
                    ParseTree::Unary(x, Box::new(arg)),
                    if arg_is_lambdavar {
                        ParsingType::et()
                    } else {
                        ParsingType::T
                    },
                )
            }),
        variable()
            .map(|x| TypedParseTree(x.0, ParsingType::et()))
            .then(entity_or_var)
            .map(|(x, (_arg_is_lambdavar, arg))| {
                TypedParseTree(
                    ParseTree::Application {
                        subformula: Box::new(x),
                        argument: Box::new(arg),
                    },
                    ParsingType::Unknown,
                )
            }),
    ))
}

fn sets<'src, E>() -> impl Parser<'src, &'src str, TypedParseTree<'src>, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>,
{
    choice((
        just("all_a").to(Constant::Everyone),
        just("all_e").to(Constant::EveryEvent),
        just("p")
            .ignore_then(text::int(10))
            .map(|p: &str| Constant::Property(p.parse().unwrap())),
    ))
    .map(LabeledConstant::Constant)
    .or(just("p_")
        .ignore_then(text::ident())
        .map(LabeledConstant::LabeledProperty))
    .map(|x| TypedParseTree(ParseTree::Constant(x), ParsingType::et()))
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
        .and_is(one_of("ape").ignore_then(text::int(10)).not())
        .and_is(just("a_").ignore_then(text::ident()).not())
        .and_is(just("p_").ignore_then(text::ident()).not())
        .labelled("variable")
    //This is a stupid way to do it, but I can't get one_of to work for the life of me.
}

fn variable<'src, E>() -> impl Parser<'src, &'src str, TypedParseTree<'src>, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>
        + LabelError<'src, &'src str, &'static str>,
{
    just_variable().map(|x| TypedParseTree(ParseTree::Variable(x), ParsingType::E))
}

fn binary_operation<'src, E>() -> impl Parser<'src, &'src str, TypedParseTree<'src>, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>
        + LabelError<'src, &'src str, &'static str>,
{
    let var_expr = variable().map(|x| (false, x));
    let entity_expr = entity().map(|x| (false, x));
    let entity_or_var = choice((entity_expr, var_expr)).padded();
    choice((
        just("AgentOf").to(BinOp::AgentOf),
        just("PatientOf").to(BinOp::PatientOf),
    ))
    .then_ignore(just('('))
    .then(entity_or_var)
    .then_ignore(just(','))
    .then(entity_or_var)
    .then_ignore(just(')'))
    .map(
        |((binop, (actor_is_lambda, actor)), (event_is_lambda, event))| {
            TypedParseTree(
                ParseTree::Binary(binop, Box::new(actor), Box::new(event)),
                match (actor_is_lambda, event_is_lambda) {
                    (true, true) => ParsingType::eet(),
                    (false, true) | (true, false) => ParsingType::et(),
                    (false, false) => ParsingType::T,
                },
            )
        },
    )
}

fn language_parser<'src, E>() -> impl Parser<'src, &'src str, TypedParseTree<'src>, E>
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
    let truth_value = recursive(|expr| {
        let atom = true_or_false
            .or(binary_operation())
            .or(properties())
            .or(variable())
            .or(expr.clone().delimited_by(just('('), just(')')));

        let neg = just("~").repeated().foldr(atom, |_, b| {
            let new_type = b.1.clone();
            TypedParseTree(
                ParseTree::Unary(LabeledProperty::Property(MonOp::Not), Box::new(b)),
                new_type,
            )
        });

        let non_quantified = neg.clone().foldl(
            choice((just('&').to(BinOp::And), just('|').to(BinOp::Or)))
                .padded()
                .then(neg.clone())
                .repeated(),
            |lhs, (op, rhs)| {
                let type1 = matches!(lhs.1, ParsingType::Composition(..));
                let type2 = matches!(rhs.1, ParsingType::Composition(..));
                let statement_type = match (type1, type2) {
                    (true, true) => ParsingType::Composition(None, Some(Box::new(ParsingType::T))),
                    (true, false) => lhs.1.clone(),
                    (false, true) => rhs.1.clone(),
                    (false, false) => ParsingType::T,
                };

                TypedParseTree(
                    ParseTree::Binary(op, Box::new(lhs), Box::new(rhs)),
                    statement_type,
                )
            },
        );

        let quantified = choice((
            just("every").to(Quantifier::Universal),
            just("some").to(Quantifier::Existential),
        ))
        .labelled("quantifier")
        .then_ignore(just('('))
        .then(just_variable())
        .then_ignore(just(','))
        .then(expr.clone().padded())
        .then_ignore(just(','))
        .then(expr.clone().padded())
        .then_ignore(just(')'))
        .map(|(((quantifier, variable), restrictor), subformula)| {
            TypedParseTree(
                ParseTree::Quantifier {
                    quantifier,
                    variable,
                    restrictor: Box::new(restrictor),
                    subformula: Box::new(subformula),
                },
                ParsingType::T,
            )
        });

        let lambda = just("lambda")
            .then(inline_whitespace().at_least(1))
            .ignore_then(core_type_parser().labelled("type label"))
            .then_ignore(inline_whitespace().at_least(1))
            .then(text::ident().padded().labelled("lambda variable"))
            .then(expr.clone().delimited_by(just('('), just(')')))
            .map(|((lambda_type, var_name), body)| {
                TypedParseTree(
                    ParseTree::Lambda {
                        body: Box::new(body),
                        var: var_name.to_string(),
                    },
                    lambda_type.into(),
                )
            })
            .labelled("lambda expression");

        choice((
            expr.clone()
                .delimited_by(just('('), just(')'))
                .then(expr.delimited_by(just('('), just(')')))
                .map(|(a, b)| {
                    TypedParseTree(
                        ParseTree::Application {
                            subformula: Box::new(a),
                            argument: Box::new(b),
                        },
                        ParsingType::Unknown,
                    )
                }),
            lambda,
            non_quantified,
            quantified,
            entity_or_variable,
            possible_sets,
        ))
    });
    truth_value
}

type ExtraType<'a> = extra::Full<Rich<'a, char>, extra::SimpleState<LabelledScenarios>, ()>;

///A parsing function that can be used to incorpate LOT parsers into other parsers.
pub fn lot_parser<'a>() -> impl Parser<'a, &'a str, RootedLambdaPool<Expr>, ExtraType<'a>> {
    language_parser::<ExtraType>().map_with(|x, e| x.to_pool(e.state()))
}

///A function which maps strings to language of thought expressions. Crucially, it automatically performs all lambda reductions.
pub fn parse_executable(
    s: &str,
    labels: &mut LabelledScenarios,
) -> anyhow::Result<LanguageExpression> {
    let mut pool = language_parser::<extra::Err<Rich<char>>>()
        .then_ignore(end())
        .parse(s)
        .into_result()
        .map_err(|x| {
            anyhow::Error::msg(
                x.into_iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join("\n"),
            )
        })?
        .to_pool(labels);
    pool.reduce()?;
    pool.into_pool()
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
                TypedParseTree(
                    ParseTree::Entity(LabeledEntity::Unlabeled(Entity::Actor(n.into()))),
                    ParsingType::E
                )
            );
            let str = format!("e{n}");
            assert_eq!(
                entity::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                TypedParseTree(
                    ParseTree::Entity(LabeledEntity::Unlabeled(Entity::Event(n))),
                    ParsingType::E
                )
            );
        }
        for keyword in ["john", "mary", "phil", "Anna"] {
            let str = format!("a_{keyword}");
            assert_eq!(
                entity::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                TypedParseTree(
                    ParseTree::Entity(LabeledEntity::LabeledActor(keyword)),
                    ParsingType::E
                )
            );
        }
    }

    #[test]
    fn parse_bin_op() -> anyhow::Result<()> {
        let mut labels = LabelledScenarios {
            scenarios: vec![],
            actor_labels: HashMap::default(),
            property_labels: HashMap::default(),
            free_variables: HashMap::default(),
        };

        for (s, result) in [
            (
                "AgentOf(a32, e2)",
                vec![
                    Expr::Entity(Entity::Actor(32)),
                    Expr::Entity(Entity::Event(2)),
                    Expr::Binary(BinOp::AgentOf, ExprRef(0), ExprRef(1)),
                ],
            ),
            (
                "PatientOf(a0, e1)",
                vec![
                    Expr::Entity(Entity::Actor(0)),
                    Expr::Entity(Entity::Event(1)),
                    Expr::Binary(BinOp::PatientOf, ExprRef(0), ExprRef(1)),
                ],
            ),
        ] {
            let (pool, root) = binary_operation::<extra::Err<Simple<_>>>()
                .parse(s)
                .unwrap()
                .to_pool(&mut labels)
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
            TypedParseTree(
                ParseTree::Constant(LabeledConstant::Constant(Constant::Tautology)),
                ParsingType::T
            )
        );
        assert_eq!(
            bool_literal::<extra::Err<Simple<_>>>()
                .parse("False")
                .unwrap(),
            TypedParseTree(
                ParseTree::Constant(LabeledConstant::Constant(Constant::Contradiction)),
                ParsingType::T
            )
        );
    }

    #[test]
    fn parse_sets() {
        for n in [1, 6, 3, 4, 5, 100, 1032, 40343] {
            let str = format!("p{n}");
            assert_eq!(
                sets::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                TypedParseTree(
                    ParseTree::Constant(LabeledConstant::Constant(Constant::Property(n))),
                    ParsingType::et()
                )
            );
        }
        assert_eq!(
            sets::<extra::Err<Simple<_>>>().parse("all_e").unwrap(),
            TypedParseTree(
                ParseTree::Constant(LabeledConstant::Constant(Constant::EveryEvent)),
                ParsingType::et()
            )
        );
        assert_eq!(
            sets::<extra::Err<Simple<_>>>().parse("all_a").unwrap(),
            TypedParseTree(
                ParseTree::Constant(LabeledConstant::Constant(Constant::Everyone)),
                ParsingType::et()
            )
        );
        for keyword in ["john", "mary", "phil", "Anna"] {
            let str = format!("p_{keyword}");
            assert_eq!(
                sets::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                TypedParseTree(
                    ParseTree::Constant(LabeledConstant::LabeledProperty(keyword)),
                    ParsingType::et()
                )
            );
        }
    }

    fn get_pool(s: &str) -> (ExprPool, ExprRef) {
        let mut labels = LabelledScenarios {
            scenarios: vec![],
            actor_labels: HashMap::default(),
            property_labels: HashMap::default(),
            free_variables: HashMap::default(),
        };
        let (parse, root) = language_parser::<extra::Err<Rich<char>>>()
            .parse(s)
            .unwrap()
            .to_pool(&mut labels)
            .into();
        let LanguageExpression { pool, start } = parse.into_pool(root).unwrap();
        (pool, start)
    }

    fn get_parse(s: &str, simple_scenario: &Scenario) -> LanguageResult {
        let mut variables = VariableBuffer(vec![]);
        let (pool, root) = get_pool(s);
        pool.interp(root, simple_scenario, &mut variables)
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
            .to_pool(&mut labels)
            .into();

        assert_eq!(pool.get_type(root)?, LambdaType::from_string(lambda_type)?);
        assert_eq!(pool, gold_pool);
        assert_eq!(root, LambdaExprRef(gold_root));

        //try again with the context-sensitive parser
        let mut label_state = extra::SimpleState(labels.clone());
        let (pool, root) = lot_parser()
            .parse_with_state(statement, &mut label_state)
            .into_result()
            .map_err(|x| {
                anyhow::Error::msg(
                    x.into_iter()
                        .map(|x| x.to_string())
                        .collect::<Vec<_>>()
                        .join("\n"),
                )
            })?
            .into();

        assert_eq!(pool, gold_pool);
        assert_eq!(root, LambdaExprRef(gold_root));
        println!(" is good!");
        Ok(())
    }

    #[test]
    fn parse_lambda() -> anyhow::Result<()> {
        check_lambdas(
            "lambda e x (p_Red(x))",
            "<e,t>",
            LambdaPool::from(vec![
                LambdaExpr::BoundVariable(0, LambdaType::E),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Property(1), ExprRef(0))),
                LambdaExpr::Lambda(LambdaExprRef(1), LambdaType::E),
            ]),
            2,
        )?;
        check_lambdas(
            "lambda  <e,t> P  (lambda e x (P(x)))",
            "<<e,t>, <e,t>>",
            LambdaPool::from(vec![
                LambdaExpr::BoundVariable(1, LambdaType::et()),
                LambdaExpr::BoundVariable(0, LambdaType::E),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(0),
                    argument: LambdaExprRef(1),
                },
                LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::E),
                LambdaExpr::Lambda(LambdaExprRef(3), LambdaType::et()),
            ]),
            4,
        )?;
        check_lambdas(
            "lambda <e,t> P (P(a0))",
            "<<e,t>,t>",
            LambdaPool::from(vec![
                LambdaExpr::BoundVariable(0, LambdaType::et()),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Entity(Entity::Actor(0))),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(0),
                    argument: LambdaExprRef(1),
                },
                LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::et()),
            ]),
            3,
        )?;
        check_lambdas(
            "~hey(lol)",
            "t",
            LambdaPool::from(vec![
                LambdaExpr::FreeVariable(0, LambdaType::et()),
                LambdaExpr::FreeVariable(1, LambdaType::E),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(0),
                    argument: LambdaExprRef(1),
                },
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Not, ExprRef(2))),
            ]),
            3,
        )?;

        check_lambdas(
            "(lambda <e,t> P (P(a0)))(lambda e x (p_Red(x)))",
            "t",
            LambdaPool::from(vec![
                LambdaExpr::BoundVariable(0, LambdaType::et()),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Entity(Entity::Actor(0))),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(0),
                    argument: LambdaExprRef(1),
                },
                LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::et()),
                LambdaExpr::BoundVariable(0, LambdaType::E),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Property(1), ExprRef(4))),
                LambdaExpr::Lambda(LambdaExprRef(5), LambdaType::E),
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
                LambdaExpr::BoundVariable(1, LambdaType::T),
                LambdaExpr::BoundVariable(0, LambdaType::T),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(0), ExprRef(1))),
                LambdaExpr::Lambda(LambdaExprRef(2), LambdaType::T),
                LambdaExpr::Lambda(LambdaExprRef(3), LambdaType::T),
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
        };
        parse_executable(
            "(lambda <e,t> P (P(a0)))(lambda e x (p_Red(x)))",
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
        };

        for statement in [
            "~AgentOf(a_John, e0)",
            "p_Red(a_John) & ~p_Red(a_Mary)",
            "p_Red(a_John) & ~p_Red(a_Mary) & p_Red(a_John)",
            "~(p_Red(a_John) & ~(True & p_Red(a_John)))",
            "every(x0, all_a, p_Blue(x0))",
            "every(x0, p_Blue, p_Blue(x0))",
            "every(x, p1, p4(x))",
            "every(x0, p_Red, p_Blue(x0))",
            "every(x0, all_e, (some(x1, all_a, AgentOf(x1, x0))))",
            "every(x0, all_e, (some(x1, all_a, PatientOf(x1, x0))))",
            "every(x0, all_e, PatientOf(a_Mary, x0))",
            "some(x0, (PatientOf(x0, e0) & PatientOf(x0, e1)), p_Blue(x0))",
        ] {
            println!("{statement}");
            let expression = parse_executable(statement, &mut labels)?;
            assert_eq!(
                expression.run(&labels.scenarios[0]),
                LanguageResult::Bool(true)
            );
        }

        for (statement, result) in [
            ("a_Mary", LanguageResult::Entity(Entity::Actor(0))),
            ("p_Red", LanguageResult::EntitySet(vec![Entity::Actor(1)])),
            (
                "p_Blue",
                LanguageResult::EntitySet(vec![Entity::Actor(0), Entity::Actor(1)]),
            ),
        ] {
            println!("{statement}");
            let expression = parse_executable(statement, &mut labels)?;
            assert_eq!(expression.run(&labels.scenarios[0]), result);
        }

        Ok(())
    }

    #[test]
    fn parse_test() -> anyhow::Result<()> {
        let mut properties: HashMap<_, _, ahash::RandomState> = HashMap::default();

        properties.insert(1, vec![Entity::Actor(1)]);
        properties.insert(4, vec![Entity::Actor(0), Entity::Actor(1)]);

        let simple_scenario = Scenario {
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
            "p1(a1) & ~p1(a0)",
            "p1(a1) & ~p1(a0) & p1(a1)",
            "~(p1(a1) & ~(True & p1(a1)))",
            "every(x0, all_a, p4(x0))",
            "every(x0, p4, p4(x0))",
            "every(x0, all_e, (some(x1, all_a, AgentOf(x1, x0))))",
            "every(x0, all_e, (some(x1, all_a, PatientOf(x1, x0))))",
            "every(x0, all_e, PatientOf(a0, x0))",
            "some(x0, (PatientOf(x0, e0) & PatientOf(x0, e1)), p4(x0))",
        ] {
            println!("{statement}");
            assert_eq!(
                get_parse(statement, &simple_scenario),
                LanguageResult::Bool(true)
            );
        }
        for (statement, result) in [
            ("a0", LanguageResult::Entity(Entity::Actor(0))),
            ("e0", LanguageResult::Entity(Entity::Event(0))),
            (
                "all_e",
                LanguageResult::EntitySet(vec![Entity::Event(0), Entity::Event(1)]),
            ),
            (
                "all_a",
                LanguageResult::EntitySet(vec![Entity::Actor(0), Entity::Actor(1)]),
            ),
            ("p1", LanguageResult::EntitySet(vec![Entity::Actor(1)])),
            (
                "p4",
                LanguageResult::EntitySet(vec![Entity::Actor(0), Entity::Actor(1)]),
            ),
        ] {
            println!("{statement}");
            assert_eq!(get_parse(statement, &simple_scenario), result);
        }

        Ok(())
    }
}
