use crate::{
    ops::{Constant, Expr, ExprPool, ExprRef, MonOp},
    Entity, PropertyLabel,
};
use chumsky::extra;
use chumsky::prelude::*;

type ExtraType<'a> = extra::Full<Simple<'a, char>, extra::SimpleState<ExprPool>, ()>;

fn parser<'a>() -> impl Parser<'a, &'a str, ExprRef, ExtraType<'a>> {
    let actor = just("a")
        .ignore_then(text::int::<&str, ExtraType>(10))
        .map_with(|num, e| {
            e.state()
                .add(Expr::Entity(Entity::Actor(num.parse().unwrap())))
        })
        .padded();

    let event = just("e")
        .ignore_then(text::int::<&str, ExtraType>(10))
        .map_with(|num, e| {
            e.state()
                .add(Expr::Entity(Entity::Actor(num.parse().unwrap())))
        })
        .padded();

    let true_or_false = choice((
        text::ascii::keyword::<_, _, ExtraType>("True").to(Constant::Tautology),
        text::ascii::keyword::<_, _, ExtraType>("False").to(Constant::Contradiction),
    ))
    .map_with(|c, e| e.state().add(Expr::Constant(c)))
    .padded();

    let constants = choice((
        text::ascii::keyword::<_, _, ExtraType>("everyone").to(Constant::Everyone),
        text::ascii::keyword::<_, _, ExtraType>("everyevent").to(Constant::EveryEvent),
        text::ascii::keyword::<_, _, ExtraType>("True").to(Constant::Tautology),
        text::ascii::keyword::<_, _, ExtraType>("False").to(Constant::Contradiction),
        just("p")
            .ignore_then(text::int::<&str, ExtraType>(10))
            .map(|p| Constant::Property(p.parse().unwrap())),
    ))
    .map_with(|c, e| e.state().add(Expr::Constant(c)))
    .padded();

    let truth_value = recursive(|expr| {
        let atom = true_or_false
            .or(expr.delimited_by(just('('), just(')')))
            .padded();
        let neg = just("~").repeated().foldr_with(atom, |_, b, e| {
            let pool = e.state();
            pool.add(Expr::Unary(MonOp::Not, b))
        });
        neg
    });

    truth_value.then_ignore(end())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ops::{LanguageResult, VariableBuffer};
    use crate::{Scenario, ThetaRoles};
    use std::collections::HashMap;

    #[test]
    fn parse_test() -> anyhow::Result<()> {
        let mut pool = extra::SimpleState(ExprPool::default());
        let parse = parser().parse_with_state("~~~False", &mut pool).unwrap();
        println!("{parse:?}");
        println!("{:?}", pool.0);
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

        assert_eq!(
            pool.0.interp(parse, &simple_scenario, &mut variables),
            LanguageResult::Bool(false)
        );
        Ok(())
    }
}
