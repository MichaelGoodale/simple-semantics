use std::{collections::HashMap, fmt::Debug};

use crate::{
    lambda::{LambdaExpr, LambdaExprRef, LambdaPool},
    language::{Constant, Expr, ExprPool, ExprRef, MonOp},
    Actor, Entity, LabelledScenarios, PropertyLabel,
};
use chumsky::prelude::*;
use chumsky::{extra::ParserExtra, label::LabelError, text::TextExpected, util::MaybeRef};

use super::{BinOp, LanguageExpression, Quantifier, Variable};

#[derive(Debug, Clone, Eq, PartialEq)]
enum ParsingType {
    E,
    T,
    Composition(Option<Box<Self>>, Option<Box<Self>>),
    Unknown,
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
}

#[derive(Debug, Eq, PartialEq)]
pub struct LabeledExprPool<'a> {
    pool: ExprPool,
    labels: &'a mut LabelledScenarios,
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct TypedParseTree<'src>(ParseTree<'src>, ParsingType);

impl<'src> TypedParseTree<'src> {
    fn add_to_pool(
        &'src self,
        pool: &mut LambdaPool<Expr>,
        labels: &mut LabelledScenarios,
        variable_names: &mut HashMap<&'src str, u32>,
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
                let x = ExprRef(x.add_to_pool(pool, labels, variable_names).0);
                let m = match m {
                    LabeledProperty::Property(mon_op) => *mon_op,
                    LabeledProperty::LabeledProperty(label) => {
                        MonOp::Property(labels.get_property_label(label))
                    }
                };
                LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(m, x))
            }
            ParseTree::Binary(b, x, y) => {
                let x = ExprRef(x.add_to_pool(pool, labels, variable_names).0);
                let y = ExprRef(y.add_to_pool(pool, labels, variable_names).0);
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(*b, x, y))
            }
            ParseTree::Quantifier {
                quantifier,
                variable,
                restrictor,
                subformula,
            } => {
                let n = variable_names.len();
                let v = *variable_names.entry(*variable).or_insert(n as u32);

                let restrictor = ExprRef(restrictor.add_to_pool(pool, labels, variable_names).0);
                let subformula = ExprRef(subformula.add_to_pool(pool, labels, variable_names).0);
                LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                    quantifier: *quantifier,
                    var: Variable(v),
                    restrictor,
                    subformula,
                })
            }
            ParseTree::Variable(str) => {
                let n = variable_names.len();
                let v = variable_names.entry(*str).or_insert(n as u32);
                LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(Variable(*v)))
            }
            _ => todo!(),
        };
        pool.add(expr)
    }

    fn to_pool(&self, labels: &mut LabelledScenarios) -> (LambdaPool<Expr>, LambdaExprRef) {
        let mut pool = LambdaPool::new();

        //TODO: Make the var labels into a HashMap<&str, Vec<u32>> with a stack to keep track of
        //scope.
        let mut var_labels = HashMap::default();
        let root = self.add_to_pool(&mut pool, labels, &mut var_labels);
        (pool, root)
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum ParseTree<'src> {
    Lambda {
        body: Box<TypedParseTree<'src>>,
        var: String,
    },
    BoundVariable(&'src str),
    FreeVariable(&'src str),
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
    Variable(&'src str),
    Entity(LabeledEntity<'src>),
}

impl<'a> LabeledExprPool<'a> {
    fn new(labels: &'a mut LabelledScenarios) -> Self {
        LabeledExprPool {
            pool: ExprPool::default(),
            labels,
        }
    }

    fn get_actor_label(&mut self, label: &str) -> Actor {
        self.labels.get_actor_label(label)
    }

    fn get_property_label(&mut self, label: &str) -> PropertyLabel {
        self.labels.get_property_label(label)
    }

    fn add(&mut self, e: Expr) -> ExprRef {
        self.pool.add(e)
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum LabeledEntity<'a> {
    Unlabeled(Entity),
    LabeledActor(&'a str),
}

impl LabeledEntity<'_> {
    fn to_expr_ref(self, state: &mut LabeledExprPool) -> ExprRef {
        match self {
            LabeledEntity::Unlabeled(c) => state.add(Expr::Entity(c)),
            LabeledEntity::LabeledActor(label) => {
                let actor = state.get_actor_label(label);
                state.add(Expr::Entity(Entity::Actor(actor)))
            }
        }
    }
}

fn entity<'src, E>() -> impl Parser<'src, &'src str, TypedParseTree<'src>, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>,
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

impl LabeledConstant<'_> {
    fn to_expr_ref(self, state: &mut LabeledExprPool) -> ExprRef {
        match self {
            LabeledConstant::Constant(c) => state.add(Expr::Constant(c)),
            LabeledConstant::LabeledProperty(label) => {
                let property = state.get_property_label(label);
                state.add(Expr::Constant(Constant::Property(property)))
            }
        }
    }

    fn to_monop(self, state: &mut LabeledExprPool) -> MonOp {
        match self {
            LabeledConstant::Constant(c) => match c {
                //TODO: Make it so that everyevent is true iff event and likewise for everyone
                Constant::Tautology | Constant::Everyone | Constant::EveryEvent => MonOp::Tautology,
                Constant::Contradiction => MonOp::Contradiction,
                Constant::Property(p) => MonOp::Property(p),
            },
            LabeledConstant::LabeledProperty(label) => {
                let property = state.get_property_label(label);
                MonOp::Property(property)
            }
        }
    }
}

fn properties<'src, E>() -> impl Parser<'src, &'src str, TypedParseTree<'src>, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>,
{
    let lambda_expr = lambda_variable().map(|x| (true, TypedParseTree(x.0, ParsingType::E)));
    let var_expr = variable().map(|x| (false, x));
    let entity_expr = entity().map(|x| (false, x));
    let entity_or_var = choice((entity_expr, var_expr, lambda_expr)).padded();

    choice((just("p")
        .ignore_then(text::int(10))
        .map(|p: &str| MonOp::Property(p.parse().unwrap())),))
    .map(LabeledProperty::Property)
    .or(just("p_")
        .ignore_then(text::ident())
        .map(LabeledProperty::LabeledProperty))
    .then(entity_or_var.padded().delimited_by(just('('), just(')')))
    .map(|(x, (arg_is_lambdavar, arg))| {
        TypedParseTree(
            ParseTree::Unary(x, Box::new(arg)),
            if arg_is_lambdavar {
                ParsingType::et()
            } else {
                ParsingType::T
            },
        )
    })
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

fn lambda_variable<'src, E>() -> impl Parser<'src, &'src str, TypedParseTree<'src>, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>,
{
    choice((
        just("f_")
            .ignore_then(text::ident())
            .map(|x| TypedParseTree(ParseTree::FreeVariable(x), ParsingType::Unknown)),
        just("b_")
            .ignore_then(text::ident())
            .map(|x| TypedParseTree(ParseTree::BoundVariable(x), ParsingType::Unknown)),
    ))
}
fn just_variable<'src, E>() -> impl Parser<'src, &'src str, &'src str, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>,
{
    just('x').ignore_then(text::int(10))
}

fn variable<'src, E>() -> impl Parser<'src, &'src str, TypedParseTree<'src>, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>,
{
    just_variable().map(|x| TypedParseTree(ParseTree::Variable(x), ParsingType::E))
}

fn binary_operation<'src, E>() -> impl Parser<'src, &'src str, TypedParseTree<'src>, E> + Copy
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>,
{
    let lambda_expr = lambda_variable().map(|x| (true, TypedParseTree(x.0, ParsingType::E)));
    let var_expr = variable().map(|x| (false, x));
    let entity_expr = entity().map(|x| (false, x));
    let entity_or_var = choice((entity_expr, var_expr, lambda_expr)).padded();
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

fn language_parser<'a>() -> impl Parser<'a, &'a str, TypedParseTree<'a>> {
    let ent = entity();
    let var = variable();
    let entity_or_variable = choice((ent, var)).padded();

    let true_or_false = bool_literal().padded();
    let possible_sets = sets().padded();
    let truth_value = recursive(|expr| {
        let atom = true_or_false
            .or(binary_operation())
            .or(properties())
            .or(expr.clone().delimited_by(just('('), just(')')))
            .padded();

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
                TypedParseTree(
                    ParseTree::Binary(op, Box::new(lhs), Box::new(rhs)),
                    ParsingType::Unknown,
                )
            },
        );

        let quantified = choice((
            just("every").to(Quantifier::Universal),
            just("some").to(Quantifier::Existential),
        ))
        .then_ignore(just('('))
        .then(just_variable())
        .then_ignore(just(','))
        .then(
            possible_sets
                .or(entity_or_variable)
                .or(non_quantified.clone()),
        )
        .then_ignore(just(','))
        .then(non_quantified.clone())
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

        choice((
            non_quantified,
            quantified,
            entity_or_variable,
            possible_sets,
        ))
    });
    truth_value.then_ignore(end())
}

pub fn parse_executable(
    s: &str,
    labels: &mut LabelledScenarios,
) -> anyhow::Result<LanguageExpression> {
    let (pool, root) = language_parser()
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
    pool.into_pool(root)
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::language::{LanguageResult, Variable, VariableBuffer};
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
        };

        for (s, result) in [
            (
                "AgentOf(x0, x1)",
                vec![
                    Expr::Variable(Variable(0)),
                    Expr::Variable(Variable(1)),
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
                .to_pool(&mut labels);
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

    #[test]
    fn parse_variable() {
        for n in [1, 6, 3, 4, 5, 100, 1032, 40343] {
            let str = format!("x{n}");
            assert_eq!(
                variable::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                TypedParseTree(ParseTree::Variable(&n.to_string()), ParsingType::E)
            );
        }
    }

    fn get_pool(s: &str) -> (ExprPool, ExprRef) {
        let mut labels = LabelledScenarios {
            scenarios: vec![],
            actor_labels: HashMap::default(),
            property_labels: HashMap::default(),
        };
        let (parse, root) = language_parser().parse(s).unwrap().to_pool(&mut labels);
        let LanguageExpression { pool, start } = parse.into_pool(root).unwrap();
        (pool, start)
    }

    fn get_parse(s: &str, simple_scenario: &Scenario) -> LanguageResult {
        let mut variables = VariableBuffer(vec![]);
        let (pool, root) = get_pool(s);
        pool.interp(root, simple_scenario, &mut variables)
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
            scenarios: vec![simple_scenario],
            actor_labels,
            property_labels,
        };

        for statement in [
            "~AgentOf(a_John, e0)",
            "p_Red(a_John) & ~p_Red(a_Mary)",
            "p_Red(a_John) & ~p_Red(a_Mary) & p_Red(a_John)",
            "~(p_Red(a_John) & ~(True & p_Red(a_John)))",
            "every(x0, all_a, p_Blue(x0))",
            "every(x0, p_Blue, p_Blue(x0))",
            "every(x0, p1, p4(x0))",
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
