use crate::{
    language::{Constant, Expr, ExprPool, ExprRef, MonOp},
    Actor, Entity, LabelledScenarios, PropertyLabel,
};
use chumsky::extra;
use chumsky::prelude::*;

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

fn parser<'a, 'b: 'a>() -> impl Parser<'a, &'a str, ExprRef, ExtraType<'a, 'b>> {
    let actor_or_event_number = one_of("ae")
        .then(text::int::<&str, ExtraType>(10))
        .map_with(|(c, num), e| {
            let expr_ref: ExprRef = e.state().add(Expr::Entity(match c {
                'a' => Entity::Actor(num.parse().unwrap()),
                'e' => Entity::Event(num.parse().unwrap()),
                _ => panic!("Unreachable because of one_of"),
            }));
            expr_ref
        });

    let actor_or_event_keyword = just("a_")
        .ignore_then(text::ident::<&str, ExtraType>())
        .map_with(|keyword, e| {
            let expr = Expr::Entity(Entity::Actor(e.state().get_actor_label(keyword)));
            e.state().add(expr)
        });

    let actor_or_event = choice((actor_or_event_keyword, actor_or_event_number)).padded();

    let true_or_false = choice((
        text::ascii::keyword::<_, _, ExtraType>("True").to(Constant::Tautology),
        text::ascii::keyword::<_, _, ExtraType>("False").to(Constant::Contradiction),
    ))
    .map_with(|c, e| e.state().add(Expr::Constant(c)))
    .padded();

    let sets = choice((
        just("all_a").to(Constant::Everyone),
        just("all_e").to(Constant::EveryEvent),
        just("p")
            .ignore_then(text::int::<&str, ExtraType>(10))
            .map(|p| Constant::Property(p.parse().unwrap())),
    ))
    .map_with(|c, e| e.state().add(Expr::Constant(c)))
    .padded();

    let literal_var = just('x')
        .ignore_then(text::int::<&str, ExtraType>(10))
        .padded()
        .map(|n| Variable(n.parse().unwrap()));

    let var = literal_var.map_with(|n, e| e.state().add(Expr::Variable(n)));

    let entity = actor_or_event.or(var).padded();

    let truth_value = recursive(|expr| {
        let has_property = just("p")
            .ignore_then(text::int::<&str, ExtraType>(10))
            .map(|p| MonOp::Property(p.parse().unwrap()))
            .then_ignore(just('('))
            .then(entity)
            .then_ignore(just(')'))
            .map_with(|(p, a), e| e.state().add(Expr::Unary(p, a)));

        let bin_op = choice((
            just("AgentOf").to(BinOp::AgentOf),
            just("PatientOf").to(BinOp::PatientOf),
        ))
        .then_ignore(just('('))
        .then(entity)
        .then_ignore(just(','))
        .then(entity)
        .then_ignore(just(')'))
        .map_with(|((binop, actor), event), e| e.state().add(Expr::Binary(binop, actor, event)));

        let atom = true_or_false
            .or(bin_op)
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language::{LanguageResult, VariableBuffer};
    use crate::{LabelledScenarios, Scenario, ThetaRoles};
    use std::collections::HashMap;

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
