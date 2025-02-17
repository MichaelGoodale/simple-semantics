use crate::{
    language::{Constant, Expr, ExprPool, ExprRef, MonOp},
    Entity, PropertyLabel,
};
use chumsky::extra;
use chumsky::prelude::*;

use super::BinOp;

type ExtraType<'a> = extra::Full<Simple<'a, char>, extra::SimpleState<ExprPool>, ()>;

fn parser<'a>() -> impl Parser<'a, &'a str, ExprRef, ExtraType<'a>> {
    let actor_or_event = one_of("ae")
        .then(text::int::<&str, ExtraType>(10))
        .map_with(|(c, num), e| {
            e.state().add(Expr::Entity(match c {
                'a' => Entity::Actor(num.parse().unwrap()),
                'e' => Entity::Event(num.parse().unwrap()),
                _ => panic!("Unreachable because of one_of"),
            }))
        })
        .padded();

    let true_or_false = choice((
        text::ascii::keyword::<_, _, ExtraType>("True").to(Constant::Tautology),
        text::ascii::keyword::<_, _, ExtraType>("False").to(Constant::Contradiction),
    ))
    .map_with(|c, e| e.state().add(Expr::Constant(c)))
    .padded();

    let sets = choice((
        just("everyone").to(Constant::Everyone),
        just("everyevent").to(Constant::EveryEvent),
        just("p")
            .ignore_then(text::int::<&str, ExtraType>(10))
            .map(|p| Constant::Property(p.parse().unwrap())),
    ))
    .map_with(|c, e| e.state().add(Expr::Constant(c)))
    .padded();

    let entity = actor_or_event.padded();

    let truth_value = recursive(|expr| {
        let atom = true_or_false
            .or(expr.delimited_by(just('('), just(')')))
            .padded();

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

        let neg = just("~")
            .repeated()
            .foldr_with(atom, |_, b, e| e.state().add(Expr::Unary(MonOp::Not, b)));

        neg.or(bin_op)
    });

    truth_value.then_ignore(end())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language::{LanguageResult, VariableBuffer};
    use crate::{Scenario, ThetaRoles};
    use std::collections::HashMap;

    #[test]
    fn parse_test() -> anyhow::Result<()> {
        let mut variables = VariableBuffer(vec![]);
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
            properties: HashMap::default(),
        };

        let mut pool = extra::SimpleState(ExprPool::default());
        let parse = parser().parse_with_state("~~~False", &mut pool).unwrap();
        assert_eq!(
            pool.0.interp(parse, &simple_scenario, &mut variables),
            LanguageResult::Bool(true)
        );

        let mut pool = extra::SimpleState(ExprPool::default());
        let parse = parser()
            .parse_with_state("AgentOf(a1,  e1)", &mut pool)
            .unwrap();
        assert_eq!(
            pool.0.interp(parse, &simple_scenario, &mut variables),
            LanguageResult::Bool(true)
        );
        Ok(())
    }
}
