use thiserror::Error;

use super::{ActorOrEvent, BinOp, Expr, MonOp};
use crate::{
    Entity, Scenario,
    lambda::{
        EvaluationError, ExprType, InterpretableLOT, LambdaExpr, LambdaExprRef,
        LambdaLanguageOfThought, LambdaPool, Literal, PrimitiveVarType, ReductionError,
        RootedLambdaPool, Value, types::LambdaType,
    },
    language::{Constant, Quantifier},
};

impl<'src> Constant<'src> {
    ///Gets the literal value of a constant.
    ///
    ///# Errors
    ///[`EvaluationError::UndefinedExpression`] if a property doesn't exist in the scenario.
    pub fn eval(&self, scenario: &Scenario<'src>) -> Result<Literal<'src>, EvaluationError> {
        Ok(match self {
            Constant::Everyone => Literal::ActorSet(scenario.actors.clone()),
            Constant::EveryEvent => Literal::EventSet(scenario.events().collect()),
            Constant::Tautology => Literal::Bool(true),
            Constant::Contradiction => Literal::Bool(false),
            Constant::Property(p, a_or_e) => {
                let x = scenario
                    .properties
                    .get(p)
                    .ok_or(EvaluationError::UndefinedExpression)?;
                match a_or_e {
                    ActorOrEvent::Actor => Literal::ActorSet(
                        x.iter()
                            .filter_map(|x| {
                                if let Entity::Actor(x) = x {
                                    Some(*x)
                                } else {
                                    None
                                }
                            })
                            .collect(),
                    ),
                    ActorOrEvent::Event => Literal::EventSet(
                        x.iter()
                            .filter_map(|x| {
                                if let Entity::Event(x) = x {
                                    Some(*x)
                                } else {
                                    None
                                }
                            })
                            .collect(),
                    ),
                }
            }
        })
    }
}

impl MonOp {
    ///Gets the value of a unary operator.
    ///
    ///# Errors
    ///
    ///- [`EvaluationError::UndefinedExpression`] if an iota has more than one possible value in the scenario
    ///- [`EvaluationError::Stuck`] if the argument cannot be converted to a [`Literal`]
    ///
    ///# Panics
    /// Will panic if the value types are not correct.
    pub fn eval<'src>(
        &self,
        argument: Value<'src, '_, Expr<'src>>,
        scenario: &Scenario<'src>,
    ) -> Result<Literal<'src>, EvaluationError> {
        let argument = argument.into_base_value_with_scenario(scenario)?.unwrap();
        Ok(match self {
            MonOp::Not => Literal::Bool(!argument.as_bool().unwrap()),
            MonOp::Iota(a_o_e) => match a_o_e {
                ActorOrEvent::Actor => {
                    let mut x = argument.into_actor_set().unwrap();
                    if x.len() != 1 {
                        return Err(EvaluationError::UndefinedExpression);
                    }
                    Literal::Actor(x.pop().unwrap())
                }
                ActorOrEvent::Event => {
                    let mut x = argument.into_event_set().unwrap();
                    if x.len() != 1 {
                        return Err(EvaluationError::UndefinedExpression);
                    }
                    Literal::Event(x.pop().unwrap())
                }
            },
        })
    }
}

impl BinOp {
    ///Gets the value of a binary operator.
    ///
    ///# Errors
    ///
    ///- [`EvaluationError::UndefinedExpression`] if a property doesn't exist in the scenario.
    ///- [`EvaluationError::Stuck`] if the arguments cannot be converted to a [`Literal`]  and the value can't be determined.
    ///
    ///# Panics
    /// Will panic if the value types are not correct.
    pub fn eval<'src, 'pool>(
        &self,
        x: Value<'src, 'pool, Expr<'src>>,
        y: Value<'src, 'pool, Expr<'src>>,
        scenario: &Scenario<'src>,
    ) -> Result<bool, EvaluationError> {
        match self {
            BinOp::AgentOf | BinOp::PatientOf => {
                let a = x
                    .into_base_value_with_scenario(scenario)?
                    .unwrap()
                    .as_actor()
                    .unwrap();
                let e = y
                    .into_base_value_with_scenario(scenario)?
                    .unwrap()
                    .as_event()
                    .unwrap();
                let e = scenario
                    .thematic_relations
                    .get(usize::from(e))
                    .ok_or(EvaluationError::UndefinedExpression)?;
                Ok(match self {
                    BinOp::AgentOf => e.agent.is_some_and(|x| x == a),
                    BinOp::PatientOf => e.patient.is_some_and(|x| x == a),
                    _ => panic!("impossible bc of prior check!"),
                })
            }
            BinOp::And | BinOp::Or => {
                let is_and = matches!(self, BinOp::And);

                match (
                    x.into_base_value_with_scenario(scenario)
                        .map(|x| x.unwrap().as_bool().unwrap()),
                    y.into_base_value_with_scenario(scenario)
                        .map(|x| x.unwrap().as_bool().unwrap()),
                ) {
                    (Ok(x), Ok(y)) => Ok(if is_and { x && y } else { x || y }),
                    (Ok(x), Err(_)) | (Err(_), Ok(x)) => match (is_and, x) {
                        //Don't need to evaluate other operand to get result.
                        (true, false) => Ok(false),
                        (false, true) => Ok(true),

                        //Need more information to know result
                        (true, true) | (false, false) => Err(EvaluationError::Stuck),
                    },
                    (Err(_), Err(_)) => Err(EvaluationError::Stuck),
                }
            }
        }
    }

    ///Evaluation if there is only a single argument!
    ///
    ///# Errors
    ///- [`EvaluationError::Stuck`] if the argument cannot be converted to a [`Literal`]
    ///# Panics
    /// Will panic if the value types are not correct.
    pub fn partial_eval<'src>(
        &self,
        argument: Value<'src, '_, Expr<'src>>,
        scenario: &Scenario<'src>,
    ) -> Result<Literal<'src>, EvaluationError> {
        let arg = argument.into_base_value_with_scenario(scenario)?.unwrap();
        Ok(match self {
            BinOp::AgentOf | BinOp::PatientOf => {
                let a = arg.as_actor().unwrap();
                let events = scenario
                    .thematic_relations
                    .iter()
                    .enumerate()
                    .filter_map(|(i, e)| match self {
                        BinOp::AgentOf => e.agent.and_then(|x| {
                            if x == a {
                                Some(u8::try_from(i).unwrap())
                            } else {
                                None
                            }
                        }),
                        BinOp::PatientOf => e.patient.and_then(|x| {
                            if x == a {
                                Some(u8::try_from(i).unwrap())
                            } else {
                                None
                            }
                        }),
                        _ => panic!("impossible bc of prior check!"),
                    })
                    .collect();
                Literal::EventSet(events)
            }
            BinOp::And => Literal::TruthTable {
                on_false: false,
                on_true: arg.as_bool().unwrap(),
            },
            BinOp::Or => Literal::TruthTable {
                on_false: arg.as_bool().unwrap(),
                on_true: true,
            },
        })
    }
}

impl Quantifier {
    ///Evaluate a quantifier
    ///# Errors
    ///- [`EvaluationError::Stuck`] if the arguments cannot be converted to a [`Literal`]
    ///
    ///# Panics
    /// Will panic if the value types are not correct.
    pub fn eval<'src, 'pool>(
        &self,
        var_type: ActorOrEvent,
        restrictor: Value<'src, 'pool, Expr<'src>>,
        predicate: Value<'src, 'pool, Expr<'src>>,
        scenario: &Scenario<'src>,
    ) -> Result<bool, EvaluationError> {
        let restrictor = restrictor.into_base_value_with_scenario(scenario)?.unwrap();
        let predicate = predicate.into_base_value_with_scenario(scenario)?.unwrap();
        let v = match var_type {
            ActorOrEvent::Actor => {
                let predicate = predicate.into_actor_set().unwrap();
                let restrictor = restrictor.into_actor_set().unwrap();
                match self {
                    Quantifier::Universal => restrictor.iter().all(|x| predicate.contains(x)),
                    Quantifier::Existential => restrictor.iter().any(|x| predicate.contains(x)),
                }
            }
            ActorOrEvent::Event => {
                let predicate = predicate.into_event_set().unwrap();
                let restrictor = restrictor.into_event_set().unwrap();
                match self {
                    Quantifier::Universal => restrictor.iter().all(|x| predicate.contains(x)),
                    Quantifier::Existential => restrictor.iter().any(|x| predicate.contains(x)),
                }
            }
        };
        Ok(v)
    }
}

impl<'src> InterpretableLOT<'src> for Expr<'src> {
    fn eval<'pool>(
        &self,
        mut arguments: Vec<Value<'src, 'pool, Expr<'src>>>,
        scenario: &Scenario<'src>,
    ) -> Result<Value<'src, 'pool, Expr<'src>>, EvaluationError> {
        Ok(Value::Base(match self {
            Expr::Quantifier {
                quantifier,
                var_type,
            } => match arguments.len() {
                0 | 1 => return Err(EvaluationError::Unfinished),
                2 => {
                    let [restrictor, predicate] = arguments.try_into().unwrap();
                    Literal::Bool(quantifier.eval(*var_type, restrictor, predicate, scenario)?)
                }
                n => panic!("Quantifier expression has {n} applicands!"),
            },
            Expr::Binary(op) => match arguments.len() {
                0 => return Err(EvaluationError::Unfinished),
                1 => op.partial_eval(arguments.pop().unwrap(), scenario)?,
                2 => {
                    let [x, y] = arguments.try_into().unwrap();
                    Literal::Bool(op.eval(x, y, scenario)?)
                }
                n => panic!("Binary expression has {n} applicands!"),
            },

            Expr::Unary(x) => match arguments.len() {
                0 => return Err(EvaluationError::Unfinished),
                1 => x.eval(arguments.pop().unwrap(), scenario)?,
                n => panic!("Unary expression has {n} applicands!"),
            },
            Expr::Constant(c) => c.eval(scenario)?,
            Expr::Actor(a) => Literal::Actor(a),
            Expr::Event(e) => Literal::Event(*e),
        }))
    }
}

impl LambdaLanguageOfThought for Expr<'_> {
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

    fn associative(&self) -> bool {
        matches!(self, Expr::Binary(BinOp::And | BinOp::Or, ..))
    }

    fn infix(&self) -> bool {
        matches!(self, Expr::Binary(BinOp::And | BinOp::Or, ..))
    }

    fn unary_associative(&self) -> bool {
        matches!(self, Expr::Unary(MonOp::Not))
    }

    fn involutory(&self) -> bool {
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
            Expr::Constant(Constant::Everyone | Constant::Property(_, ActorOrEvent::Actor)) => {
                LambdaType::at()
            }
            Expr::Constant(Constant::EveryEvent | Constant::Property(_, ActorOrEvent::Event)) => {
                LambdaType::et()
            }
            Expr::Constant(Constant::Tautology | Constant::Contradiction) => &LambdaType::T,
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
            "every_e(x, pe_laughs(x), every(y, pe_sleeps(x), pa_woman(y)))",
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
