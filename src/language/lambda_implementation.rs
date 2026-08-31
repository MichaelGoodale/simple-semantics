use thiserror::Error;

use super::{ActorOrEvent, BinOp, Expr, MonOp};
use crate::{
    lambda::{
        ExprType, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool, PrimitiveVarType,
        ReductionError, RootedLambdaPool, types::LambdaType,
    },
    language::Constant,
};

impl<'a> LambdaLanguageOfThought for Expr<'a> {
    fn var_type(&self) -> Option<&LambdaType> {
        match self {
            Expr::Quantifier { var_type, .. } | Expr::Unary(MonOp::Iota(var_type)) => {
                match var_type {
                    ActorOrEvent::Actor => Some(LambdaType::a()),
                    ActorOrEvent::Event => Some(LambdaType::e()),
                }
            }
            _ => None,
        }
    }

    fn commutative(&self) -> bool {
        matches!(self, Expr::Binary(BinOp::And | BinOp::Or, ..))
    }

    fn infix(&self) -> bool {
        matches!(self, Expr::Binary(BinOp::And | BinOp::Or, ..))
    }

    fn unary_associative(&self) -> bool {
        matches!(self, Expr::Unary(MonOp::Not))
    }

    fn bind_vars(&self) -> PrimitiveVarType {
        match self {
            Expr::Quantifier { .. } => PrimitiveVarType::BindVarTwoBodies,
            Expr::Unary(MonOp::Iota(_), ..) => PrimitiveVarType::BindVar,
            _ => PrimitiveVarType::NoVar,
        }
    }

    fn typ(&self) -> &LambdaType {
        match self {
            Expr::Quantifier {
                var_type: ActorOrEvent::Actor,
                ..
            } => LambdaType::gq_a(),
            Expr::Quantifier {
                var_type: ActorOrEvent::Event,
                ..
            } => LambdaType::gq_e(),
            Expr::Unary(MonOp::Iota(ActorOrEvent::Actor)) => LambdaType::ata(),
            Expr::Unary(MonOp::Iota(ActorOrEvent::Event)) => LambdaType::ete(),
            Expr::Actor(_) => &LambdaType::A,
            Expr::Event(_) => &LambdaType::E,
            Expr::Binary(bin_op) => match bin_op {
                BinOp::AgentOf | BinOp::PatientOf => LambdaType::aet(),
                BinOp::And | BinOp::Or => LambdaType::ttt(),
            },
            Expr::Unary(MonOp::Not) => LambdaType::tt(),
            Expr::Constant(Constant::Everyone) => LambdaType::at(),
            Expr::Constant(Constant::EveryEvent) => LambdaType::et(),
            Expr::Constant(Constant::Tautology) => &LambdaType::T,
            Expr::Constant(Constant::Contradiction) => &LambdaType::T,
            Expr::Constant(Constant::Property(_, ActorOrEvent::Actor)) => LambdaType::at(),
            Expr::Constant(Constant::Property(_, ActorOrEvent::Event)) => LambdaType::et(),
        }
    }
}

///An error which results from a failed application of [`RootedLambdaPool::conjoin`]
#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum ConjoiningError {
    ///Both arguments have to have the same type
    #[error("Can't conjoin {0} and {1}")]
    MismatchingTypes(LambdaType, LambdaType),

    ///The type must return a truth value
    #[error("Lambda type, {0} doesn't return a truth value")]
    DoesntReturnT(LambdaType),

    ///One of the arguments has an internal problem leading to reduction errors
    #[error("One of the operands causes problems in reduction: {0})")]
    ReductionError(#[from] ReductionError),
}

fn who_raises_who<'a>(
    a: RootedLambdaPool<'a, Expr<'a>>,
    b: RootedLambdaPool<'a, Expr<'a>>,
) -> Result<
    (
        RootedLambdaPool<'a, Expr<'a>>,
        RootedLambdaPool<'a, Expr<'a>>,
    ),
    ConjoiningError,
> {
    let a_type = a.get_type().unwrap();
    let b_type = b.get_type().unwrap();

    let Ok(a_rhs) = a_type.rhs() else {
        return Err(ConjoiningError::DoesntReturnT(a_type));
    };
    let Ok(b_rhs) = b_type.rhs() else {
        return Err(ConjoiningError::DoesntReturnT(b_type));
    };
    if b_rhs != &LambdaType::T && a_rhs != &LambdaType::T {
        return Err(ConjoiningError::DoesntReturnT(a_type));
    }

    if a_rhs != &b_type && b_rhs != &a_type {
        Err(ConjoiningError::MismatchingTypes(a_type, b_type))
    } else if a_rhs == &b_type {
        Ok((a, b))
    } else {
        Ok((b, a))
    }
}

impl<'a> RootedLambdaPool<'a, Expr<'a>> {
    ///Takes two lambda expressions, phi and psi of type <x, t> where x is any type and returns phi
    ///AND psi.
    ///
    ///# Errors
    ///Returns a [`ConjoiningError`] if `self` and `other` are not of the right types such that a
    //conjoining can happen.
    #[allow(clippy::missing_panics_doc)]
    pub fn conjoin(self, other: Self) -> Result<Self, ConjoiningError> {
        let self_type = self.get_type().unwrap();
        let other_type = other.get_type().unwrap();
        if self_type != other_type {
            return Err(ConjoiningError::MismatchingTypes(self_type, other_type));
        }

        let Ok((lhs, rhs)) = self_type.split() else {
            return Err(ConjoiningError::DoesntReturnT(self_type));
        };

        if rhs != &LambdaType::T {
            return Err(ConjoiningError::DoesntReturnT(self_type));
        }
        let lhs = lhs.clone();
        let combinator = RootedLambdaPool {
            pool: LambdaPool(vec![
                LambdaExpr::Lambda(LambdaExprRef(1), self_type.clone()),
                LambdaExpr::Lambda(LambdaExprRef(2), other_type.clone()),
                LambdaExpr::Lambda(LambdaExprRef(3), lhs.clone()),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(4),
                    argument: LambdaExprRef(9),
                },
                LambdaExpr::Application {
                    subformula: LambdaExprRef(5),
                    argument: LambdaExprRef(6),
                },
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And), ExprType::NoVar),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(7),
                    argument: LambdaExprRef(8),
                },
                LambdaExpr::BoundVariable(2, self_type),
                LambdaExpr::BoundVariable(0, lhs.clone()),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(10),
                    argument: LambdaExprRef(11),
                },
                LambdaExpr::BoundVariable(1, other_type),
                LambdaExpr::BoundVariable(0, lhs),
            ]),
            root: LambdaExprRef(0),
        };

        let mut conjoined = combinator.merge(self).unwrap().merge(other).unwrap();
        conjoined.reduce()?;
        Ok(conjoined)
    }

    ///Takes two lambda expressions, phi <x, <y,t>> and psi of type <y, t> where x and y is any type and returns phi
    ///AND psi.
    ///
    ///This is a generalized kind of Event Identification from Kratzer (1996)
    ///
    /// - Kratzer, A. (1996). Severing the External Argument from its Verb. In J. Rooryck & L. Zaring (Eds.), Phrase Structure and the Lexicon (pp. 109–137). Springer Netherlands. <https://doi.org/10.1007/978-94-015-8617-7_5>
    ///
    ///# Errors
    ///Returns a [`ConjoiningError`] if `self` and `other` are not of the right types such that a
    //raised conjoining can happen.
    #[allow(clippy::missing_panics_doc)]
    pub fn raised_conjoin(self, other: Self) -> Result<Self, ConjoiningError> {
        let (a, b) = who_raises_who(self, other)?;
        let a_type = a.get_type().unwrap();
        let b_type = b.get_type().unwrap();

        let Ok(event) = a_type.lhs() else {
            return Err(ConjoiningError::DoesntReturnT(a_type));
        };

        let Ok(e) = b_type.lhs() else {
            return Err(ConjoiningError::DoesntReturnT(b_type));
        };
        let e = e.clone();
        let event = event.clone();

        let combinator = RootedLambdaPool {
            pool: LambdaPool(vec![
                LambdaExpr::Lambda(LambdaExprRef(1), a_type.clone()),
                LambdaExpr::Lambda(LambdaExprRef(2), b_type.clone()),
                LambdaExpr::Lambda(LambdaExprRef(3), event.clone()),
                LambdaExpr::Lambda(LambdaExprRef(4), e.clone()),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(5),
                    argument: LambdaExprRef(12),
                }, //4
                LambdaExpr::Application {
                    subformula: LambdaExprRef(6),
                    argument: LambdaExprRef(7),
                },
                LambdaExpr::LanguageOfThoughtExpr(
                    Expr::Binary(
                        //6
                        BinOp::And,
                    ),
                    ExprType::NoVar,
                ),
                LambdaExpr::Application {
                    //7
                    subformula: LambdaExprRef(8),
                    argument: LambdaExprRef(11),
                },
                LambdaExpr::Application {
                    subformula: LambdaExprRef(9),
                    argument: LambdaExprRef(10),
                },
                LambdaExpr::BoundVariable(3, a_type),
                LambdaExpr::BoundVariable(1, event),
                LambdaExpr::BoundVariable(0, e.clone()),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(13),
                    argument: LambdaExprRef(14),
                },
                LambdaExpr::BoundVariable(2, b_type),
                LambdaExpr::BoundVariable(0, e),
            ]),
            root: LambdaExprRef(0),
        };
        let mut conjoined = combinator.merge(a).unwrap().merge(b).unwrap();
        conjoined.reduce()?;
        Ok(conjoined)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::lambda::{FreeVar, types::LambdaType};
    use crate::{Entity, Scenario, ThetaRoles, lambda::RootedLambdaPool};

    #[test]
    fn type_checking() -> anyhow::Result<()> {
        let john = RootedLambdaPool::<Expr>::parse("a_John")?;
        let likes = RootedLambdaPool::<Expr>::parse(
            "lambda a x ((lambda a y (some_e(e, all_e(e), AgentOf(x, e) & PatientOf(y, e) & pe_likes(e)))))",
        )?;

        let mary = RootedLambdaPool::<Expr>::parse("a_Mary")?;
        let phi = mary.clone().merge(likes.clone()).unwrap();
        let mut phi = phi.merge(john.clone()).unwrap();
        phi.reduce()?;
        assert_eq!(
            "some_e(x, all_e(x), AgentOf(a_Mary, x) & PatientOf(a_John, x) & pe_likes(x))",
            phi.to_string()
        );
        let phi = likes.merge(mary).unwrap();
        let mut phi = john.merge(phi).unwrap();
        phi.reduce()?;
        assert_eq!(
            "some_e(x, all_e(x), AgentOf(a_Mary, x) & PatientOf(a_John, x) & pe_likes(x))",
            phi.to_string()
        );
        Ok(())
    }
    #[test]
    fn fancy_quantification_reduction() -> anyhow::Result<()> {
        let pool = RootedLambdaPool::<Expr>::parse("every_e(x0,pe_0(x0) & pe_1(x0), pe_2(x0))")?;
        let scenario = Scenario::new(
            vec![],
            vec![ThetaRoles::default(); 5],
            [
                ("0", vec![Entity::Event(1), Entity::Event(2)]),
                ("1", vec![Entity::Event(0), Entity::Event(1)]),
                ("2", vec![Entity::Event(1)]),
            ]
            .into_iter()
            .collect(),
        );

        assert!(pool.interp(&scenario).unwrap().try_into()?);

        let pool = RootedLambdaPool::<Expr>::parse("every_e(x0, pe_0(x0) & pe_1(x0), pe_2(x0))")?;

        let scenario = Scenario::new(
            vec![],
            vec![ThetaRoles::default(); 5],
            [
                ("0", vec![Entity::Event(1), Entity::Event(2)]),
                ("1", vec![Entity::Event(0), Entity::Event(1)]),
                ("2", vec![Entity::Event(1)]),
            ]
            .into_iter()
            .collect(),
        );

        dbg!(&pool);
        assert!(pool.interp(&scenario).unwrap().try_into()?);

        let pool = RootedLambdaPool::<Expr>::parse(
            "every_e(x, pe_laughs, every(y, pe_sleeps(x), pa_woman(y)))",
        )?;
        println!("{}", pool);
        Ok(())
    }

    #[test]
    fn conjoining_check() -> anyhow::Result<()> {
        let tall = RootedLambdaPool::<Expr>::parse("lambda a x pa_tall(x)")?;
        let man = RootedLambdaPool::<Expr>::parse("lambda a x pa_man(x)")?;

        let mut tall_man = tall.conjoin(man)?;
        tall_man.reduce()?;
        let weird = RootedLambdaPool::<Expr>::parse("weird#<a,t>")?;
        let man = RootedLambdaPool::<Expr>::parse("lambda a x pa_man(x)")?;
        let weird_man = weird.conjoin(man)?;
        assert_eq!(format!("{tall_man}"), "lambda a x pa_tall(x) & pa_man(x)");
        assert_eq!(
            format!("{weird_man}"),
            "lambda a x weird#<a,t>(x) & pa_man(x)"
        );

        let voice = RootedLambdaPool::<Expr>::parse("lambda a x lambda e y AgentOf(x, y)")?;
        let run = RootedLambdaPool::<Expr>::parse("lambda e x pe_run(x)")?;

        let mut agent_run = voice.raised_conjoin(run)?;
        agent_run.reduce()?;
        assert_eq!(
            format!("{agent_run}"),
            "lambda a x lambda e y AgentOf(x, y) & pe_run(y)"
        );
        let voice = RootedLambdaPool::<Expr>::parse("lambda a x lambda e y AgentOf(x, y)")?;
        let run = RootedLambdaPool::<Expr>::parse("lambda e x pe_run(x)")?;

        let mut agent_run = run.raised_conjoin(voice)?;
        agent_run.reduce()?;
        assert_eq!(
            format!("{agent_run}"),
            "lambda a x lambda e y AgentOf(x, y) & pe_run(y)"
        );
        Ok(())
    }

    #[test]
    fn alpha_check() -> anyhow::Result<()> {
        let everyone =
            RootedLambdaPool::<Expr>::parse("lambda <a,t> P (every(x, all_a(x), P(x)))")?;
        let someone = RootedLambdaPool::<Expr>::parse("lambda <a,t> P (some(x, all_a(x), P(x)))")?;
        let mut likes = RootedLambdaPool::<Expr>::parse(
            "lambda a x (lambda a y (some_e(e, all_e(e), AgentOf(y, e)&pe_likes(e)&PatientOf(x, e))))",
        )?;

        likes.apply_new_free_variable(FreeVar::Anonymous(0))?;
        let mut sentence = likes.merge(someone).unwrap();
        sentence.lambda_abstract_free_variable(FreeVar::Anonymous(0), LambdaType::A, true)?;
        let mut sentence = sentence.merge(everyone).unwrap();
        sentence.reduce()?;

        assert_eq!(
            sentence.to_string(),
            "every(x, all_a(x), some(y, all_a(y), some_e(z, all_e(z), AgentOf(y, z) & pe_likes(z) & PatientOf(x, z))))"
        );
        assert_eq!(
            sentence,
            RootedLambdaPool::<Expr>::parse(
                "every(x, all_a(x), some(y, all_a(y), some_e(z, all_e(z), AgentOf(y, z) & pe_likes(z) & PatientOf(x, z))))"
            )?
        );

        let everyone =
            RootedLambdaPool::<Expr>::parse("lambda <a,t> P (every(x, all_a(x), P(x)))")?;
        let someone = RootedLambdaPool::<Expr>::parse("lambda <a,t> P (some(x, all_a(x), P(x)))")?;
        let mut likes = RootedLambdaPool::<Expr>::parse(
            "lambda a x (lambda a y ( some_e(e, all_e(e), AgentOf(y, e)&pe_likes(e)&PatientOf(x, e)) | some(w, all_a(w), every_e(e, all_e(e), AgentOf(y, e)&pe_likes(e)&PatientOf(x, e)))))",
        )?;

        likes.apply_new_free_variable(FreeVar::Anonymous(0))?;
        let mut sentence = likes.merge(someone).unwrap();
        sentence.lambda_abstract_free_variable(FreeVar::Anonymous(0), LambdaType::A, true)?;
        let mut sentence = sentence.merge(everyone).unwrap();
        sentence.reduce()?;
        assert_eq!(
            sentence,
            RootedLambdaPool::<Expr>::parse(
                "every(x, all_a(x), some(y, all_a(y), some_e(z, all_e(z), AgentOf(y, z) & pe_likes(z) & PatientOf(x, z)) | some(z, all_a(z), every_e(a, all_e(a), AgentOf(y, a) & pe_likes(a) & PatientOf(x, a)))))"
            )?
        );
        Ok(())
    }
}
