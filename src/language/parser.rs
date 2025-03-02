use std::{borrow::Borrow, fmt::Debug};

use crate::{
    language::{Constant, Expr, ExprPool, ExprRef, MonOp},
    Actor, Entity, LabelledScenarios, PropertyLabel,
};
use chumsky::{
    extra::{self, ParserExtra},
    input::StrInput,
    label::LabelError,
    text::{Char, TextExpected},
    util::MaybeRef,
};
use chumsky::{input::SliceInput, prelude::*};

use super::{BinOp, Quantifier, Variable};

struct LabeledExprPool<'a> {
    pool: ExprPool,
    labels: &'a mut LabelledScenarios,
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

type ExtraType<'a, 'b> = extra::Full<Simple<'a, char>, extra::SimpleState<LabeledExprPool<'b>>, ()>;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum LabeledEntity<'a> {
    Unlabeled(Entity),
    LabeledActor(&'a str),
}

fn entity<'src, E>() -> impl Parser<'src, &'src str, LabeledEntity<'src>, E>
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
}

pub fn bool_literal<'src, E>() -> impl Parser<'src, &'src str, Constant, E>
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, &'src str>,
{
    choice((
        text::ascii::keyword("True").to(Constant::Tautology),
        text::ascii::keyword("False").to(Constant::Contradiction),
    ))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LabeledConstant<'a> {
    Constant(Constant),
    LabeledProperty(&'a str),
}

impl LabeledConstant<'_> {
    fn to_expr_ref(self, state: &mut LabeledExprPool) -> ExprRef {
        match self {
            LabeledConstant::Constant(c) => state.add(Expr::Constant(c)),
            LabeledConstant::LabeledProperty(label) => {
                todo!();
            }
        }
    }
}

fn sets<'src, E>() -> impl Parser<'src, &'src str, LabeledConstant<'src>, E>
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
}

fn variable<'src, E>() -> impl Parser<'src, &'src str, Variable, E>
where
    E: ParserExtra<'src, &'src str>,
    E::Error: LabelError<'src, &'src str, TextExpected<'src, &'src str>>
        + LabelError<'src, &'src str, MaybeRef<'src, char>>,
{
    just('x')
        .ignore_then(text::int(10))
        .padded()
        .map(|n: &str| Variable(n.parse().unwrap()))
}

/*
fn binary_operation<'a, 'b: 'a>() -> impl Parser<'a, &'a str, ExprRef, ExtraType<'a, 'b>> {
    let var = variable().map_with(|n, e| e.state().add(Expr::Variable(n)));
    let base_entity = choice((entity(), var)).padded();
    let base_entity_2 = choice((entity(), var)).padded();
    choice((
        just("AgentOf").to(BinOp::AgentOf),
        just("PatientOf").to(BinOp::PatientOf),
    ))
    .then_ignore(just('('))
    .then(base_entity)
    .then_ignore(just(','))
    .then(base_entity_2)
    .then_ignore(just(')'))
    .map_with(|((binop, actor), event), e| e.state().add(Expr::Binary(binop, actor, event)))
}*/

fn parser<'a, 'b: 'a>() -> impl Parser<'a, &'a str, ExprRef, ExtraType<'a, 'b>> {
    let entity = entity::<ExtraType<'a, 'b>>().padded();

    let true_or_false = bool_literal::<ExtraType<'a, 'b>>()
        .padded()
        .map_with(|b, e| e.state().add(Expr::Constant(b)));

    let sets = sets::<ExtraType<'a, 'b>>()
        .padded()
        .map_with(|x, e| x.to_expr_ref(e.state()));
    /*
    let truth_value = recursive(|expr| {
        let has_property = just("p")
            .ignore_then(text::int::<&str, ExtraType>(10))
            .map(|p| MonOp::Property(p.parse().unwrap()))
            .then_ignore(just('('))
            .then(entity)
            .then_ignore(just(')'))
            .map_with(|(p, a), e| e.state().add(Expr::Unary(p, a)));

        let atom = true_or_false
            .or(binary_operation())
            .or(has_property)
            .or(expr.clone().delimited_by(just('('), just(')')))
            .padded();

        let neg = just("~")
            .repeated()
            .foldr_with(atom, |_, b, e| e.state().add(Expr::Unary(MonOp::Not, b)));

        let logical_op = neg.clone().foldl_with(
            choice((just('&').to(BinOp::And), just('|').to(BinOp::Or)))
                .padded()
                .then(neg.clone())
                .repeated(),
            |lhs, (op, rhs), e| e.state().add(Expr::Binary(op, lhs, rhs)),
        );

        let non_quantified_statement = logical_op.or(neg).padded();

        let quantified = choice((
            just("every").to(Quantifier::Universal),
            just("some").to(Quantifier::Existential),
        ))
        .then_ignore(just('('))
        .then(literal_var)
        .then_ignore(just(','))
        .then(sets.or(entity).or(non_quantified_statement.clone()))
        .then_ignore(just(','))
        .then(non_quantified_statement.clone())
        .then_ignore(just(')'))
        .map_with(|(((q, v), rest), phi), e| e.state().add(Expr::Quantifier(q, v, rest, phi)));
        non_quantified_statement.or(quantified)
    });

    truth_value.then_ignore(end())

    */

    sets.then_ignore(end())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language::{LanguageResult, VariableBuffer};
    use crate::{LabelledScenarios, Scenario, ThetaRoles};
    use std::collections::HashMap;

    #[test]
    fn parse_entity() {
        for n in [1, 6, 3, 4, 5, 100, 40] {
            let str = format!("a{n}");
            assert_eq!(
                entity::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                LabeledEntity::Unlabeled(Entity::Actor(n.into()))
            );
            let str = format!("e{n}");
            assert_eq!(
                entity::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                LabeledEntity::Unlabeled(Entity::Event(n))
            );
        }
        for keyword in ["john", "mary", "phil", "Anna"] {
            let str = format!("a_{keyword}");
            assert_eq!(
                entity::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                LabeledEntity::LabeledActor(keyword)
            );
        }
    }

    #[test]
    fn parse_bool() {
        assert_eq!(
            bool_literal::<extra::Err<Simple<_>>>()
                .parse("True")
                .unwrap(),
            Constant::Tautology
        );
        assert_eq!(
            bool_literal::<extra::Err<Simple<_>>>()
                .parse("False")
                .unwrap(),
            Constant::Contradiction
        );
    }

    #[test]
    fn parse_sets() {
        for n in [1, 6, 3, 4, 5, 100, 1032, 40343] {
            let str = format!("p{n}");
            assert_eq!(
                sets::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                LabeledConstant::Constant(Constant::Property(n))
            );
        }
        assert_eq!(
            sets::<extra::Err<Simple<_>>>().parse("all_e").unwrap(),
            LabeledConstant::Constant(Constant::EveryEvent)
        );
        assert_eq!(
            sets::<extra::Err<Simple<_>>>().parse("all_a").unwrap(),
            LabeledConstant::Constant(Constant::Everyone)
        );
        for keyword in ["john", "mary", "phil", "Anna"] {
            let str = format!("p_{keyword}");
            assert_eq!(
                sets::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                LabeledConstant::LabeledProperty(keyword)
            );
        }
    }

    #[test]
    fn parse_variable() {
        for n in [1, 6, 3, 4, 5, 100, 1032, 40343] {
            let str = format!("x{n}");
            assert_eq!(
                variable::<extra::Err<Simple<_>>>().parse(&str).unwrap(),
                Variable(n)
            );
        }
    }

    fn get_parse(s: &str, simple_scenario: &Scenario) -> LanguageResult {
        let mut labels = LabelledScenarios {
            scenarios: vec![],
            actor_labels: HashMap::default(),
            property_labels: HashMap::default(),
        };
        let mut pool = extra::SimpleState(LabeledExprPool::new(&mut labels));
        let parse = parser().parse_with_state(s, &mut pool).unwrap();
        let mut variables = VariableBuffer(vec![]);
        pool.pool.interp(parse, simple_scenario, &mut variables)
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

        Ok(())
    }
}
