use crate::{Actor, Entity, Event, PropertyLabel, Scenario};

#[derive(Debug, Clone, Copy)]
enum BinOp {
    AgentOf,
    PatientOf,
    And,
    Or,
}

#[derive(Debug, Clone, Copy)]
enum MonOp {
    Not,
}

#[derive(Debug, Clone, Copy)]
enum Constant {
    Everyone,
    EveryEvent,
    Tautology,
    Contradiction,
}

#[derive(Debug, Clone, Copy)]
struct Variable(u32);

#[derive(Debug, Clone, Copy)]
enum Quantifier {
    Universal,
    Existential,
}

#[derive(Debug, Clone, Copy)]
enum Expr {
    Quantifier(Quantifier, Variable, ExprRef, ExprRef),
    Variable(Variable),
    Entity(Entity),
    PropertyLabel(PropertyLabel),
    Binary(BinOp, ExprRef, ExprRef),
    Unary(MonOp, ExprRef),
    Constant(Constant),
}

#[derive(Debug, Clone, Copy)]
struct ExprRef(u32);

#[derive(Debug, Clone)]
struct ExprPool(Vec<Expr>);

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct VariableBuffer(Vec<Option<Entity>>);

impl VariableBuffer {
    fn set(&mut self, v: Variable, x: Entity) {
        let i = v.0 as usize;
        if self.0.len() <= i {
            self.0.resize(i + 1, None);
        }
        self.0[i] = Some(x);
    }

    fn get(&self, v: Variable) -> Option<Entity> {
        match self.0.get(v.0 as usize) {
            Some(x) => *x,
            None => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum LanguageResult {
    PresuppositionError,
    Bool(bool),
    Entity(Entity),
    EntitySet(Vec<Entity>),
    PropertyLabel(PropertyLabel),
}
impl TryFrom<LanguageResult> for Event {
    type Error = ();

    fn try_from(value: LanguageResult) -> Result<Self, Self::Error> {
        match value {
            LanguageResult::Entity(Entity::Event(x)) => Ok(x),
            _ => Err(()),
        }
    }
}

impl TryFrom<LanguageResult> for Actor {
    type Error = ();

    fn try_from(value: LanguageResult) -> Result<Self, Self::Error> {
        match value {
            LanguageResult::Entity(Entity::Actor(x)) => Ok(x),
            _ => Err(()),
        }
    }
}
impl TryFrom<LanguageResult> for bool {
    type Error = ();

    fn try_from(value: LanguageResult) -> Result<Self, Self::Error> {
        match value {
            LanguageResult::Bool(vec) => Ok(vec),
            _ => Err(()),
        }
    }
}

impl TryFrom<LanguageResult> for Vec<Entity> {
    type Error = ();

    fn try_from(value: LanguageResult) -> Result<Self, Self::Error> {
        match value {
            LanguageResult::EntitySet(vec) => Ok(vec),
            _ => Err(()),
        }
    }
}

impl ExprPool {
    fn get(&self, expr: ExprRef) -> &Expr {
        &self.0[expr.0 as usize]
    }

    fn add(&mut self, expr: Expr) -> ExprRef {
        let idx = self.0.len();
        self.0.push(expr);
        ExprRef(idx.try_into().expect("Too many exprs in the pool"))
    }

    fn interp(
        &self,
        expr: ExprRef,
        scenario: &Scenario,
        variables: &mut VariableBuffer,
    ) -> LanguageResult {
        match self.get(expr) {
            Expr::Quantifier(q, var, restrictor, subformula) => {
                let domain: Vec<Entity> = self
                    .interp(*restrictor, scenario, variables)
                    .try_into()
                    .unwrap();
                let mut variables = variables.clone();

                let mut result = match q {
                    Quantifier::Universal => true,
                    Quantifier::Existential => false,
                };
                for e in domain {
                    variables.set(*var, e);
                    let subformula_value: bool = self
                        .interp(*subformula, scenario, &mut variables)
                        .try_into()
                        .unwrap();
                    result = match q {
                        Quantifier::Universal => subformula_value && result,
                        Quantifier::Existential => subformula_value || result,
                    };
                }
                LanguageResult::Bool(result)
            }
            Expr::Variable(i) => LanguageResult::Entity(variables.get(*i).unwrap()),
            Expr::Entity(a) => LanguageResult::Entity(*a),
            Expr::PropertyLabel(p) => LanguageResult::PropertyLabel(*p),
            Expr::Binary(bin_op, lhs, rhs) => {
                let lhs = self.interp(*lhs, scenario, variables);
                let rhs = self.interp(*rhs, scenario, variables);
                match bin_op {
                    BinOp::PatientOf | BinOp::AgentOf => {
                        let a: Actor = lhs.try_into().unwrap();
                        let e: Event = rhs.try_into().unwrap();
                        match bin_op {
                            BinOp::AgentOf => match scenario.thematic_relations[e as usize].agent {
                                Some(x) => LanguageResult::Bool(x == a),
                                None => LanguageResult::PresuppositionError,
                            },
                            BinOp::PatientOf => {
                                match scenario.thematic_relations[e as usize].patient {
                                    Some(x) => LanguageResult::Bool(x == a),
                                    None => LanguageResult::PresuppositionError,
                                }
                            }
                            _ => panic!("impossible because of previous check"),
                        }
                    }
                    BinOp::Or | BinOp::And => {
                        let phi: bool = lhs.try_into().unwrap();
                        let psi: bool = rhs.try_into().unwrap();
                        LanguageResult::Bool(match bin_op {
                            BinOp::And => phi && psi,
                            BinOp::Or => phi || psi,
                            _ => panic!("impossible because of previous check"),
                        })
                    }
                }
            }
            Expr::Constant(constant) => match constant {
                Constant::Everyone => LanguageResult::EntitySet(
                    scenario.actors.iter().map(|x| Entity::Actor(*x)).collect(),
                ),
                Constant::EveryEvent => LanguageResult::EntitySet(
                    (0..scenario.thematic_relations.len())
                        .map(|x| Entity::Event(x.try_into().unwrap()))
                        .collect(),
                ),
                Constant::Tautology => LanguageResult::Bool(true),
                Constant::Contradiction => LanguageResult::Bool(false),
            },
            Expr::Unary(mon_op, arg) => {
                let arg = self.interp(*arg, scenario, variables);
                match mon_op {
                    MonOp::Not => LanguageResult::Bool(!TryInto::<bool>::try_into(arg).unwrap()),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ThetaRoles;

    #[test]
    fn agent_of_and_patient_of() {
        let mut variables = VariableBuffer(vec![]);
        let simple_scenario = Scenario {
            actors: vec![0, 1],
            thematic_relations: vec![ThetaRoles {
                agent: Some(0),
                patient: None,
            }],
            properties: vec![],
        };

        let simple_expr = ExprPool(vec![
            Expr::Entity(Entity::Actor(0)),
            Expr::Entity(Entity::Event(0)),
            Expr::Binary(BinOp::AgentOf, ExprRef(0), ExprRef(1)),
        ]);

        assert_eq!(
            simple_expr.interp(ExprRef(2), &simple_scenario, &mut variables),
            LanguageResult::Bool(true)
        );

        let simple_expr = ExprPool(vec![
            Expr::Entity(Entity::Actor(0)),
            Expr::Entity(Entity::Event(0)),
            Expr::Binary(BinOp::PatientOf, ExprRef(0), ExprRef(1)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(2), &simple_scenario, &mut variables),
            LanguageResult::PresuppositionError
        );
    }

    #[test]
    fn quantification() {
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
            properties: vec![],
        };

        //For all actors there exists an event such that they are its agent.
        let simple_expr = ExprPool(vec![
            Expr::Quantifier(Quantifier::Universal, Variable(0), ExprRef(1), ExprRef(2)),
            Expr::Constant(Constant::Everyone),
            Expr::Quantifier(Quantifier::Existential, Variable(1), ExprRef(3), ExprRef(4)),
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::AgentOf, ExprRef(5), ExprRef(6)),
            Expr::Variable(Variable(0)),
            Expr::Variable(Variable(1)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables),
            LanguageResult::Bool(true)
        );

        //For all actors there exists an event such that they are its patient.
        let simple_expr = ExprPool(vec![
            Expr::Quantifier(Quantifier::Universal, Variable(0), ExprRef(1), ExprRef(2)),
            Expr::Constant(Constant::Everyone),
            Expr::Quantifier(Quantifier::Existential, Variable(1), ExprRef(3), ExprRef(4)),
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::PatientOf, ExprRef(5), ExprRef(6)),
            Expr::Variable(Variable(0)),
            Expr::Variable(Variable(1)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables),
            LanguageResult::Bool(false)
        );
    }

    #[test]
    fn logic() {
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
            properties: vec![],
        };

        assert_eq!(
            ExprPool(vec![Expr::Constant(Constant::Contradiction)]).interp(
                ExprRef(0),
                &simple_scenario,
                &mut variables
            ),
            LanguageResult::Bool(false)
        );

        assert_eq!(
            ExprPool(vec![Expr::Constant(Constant::Tautology)]).interp(
                ExprRef(0),
                &simple_scenario,
                &mut variables
            ),
            LanguageResult::Bool(true)
        );

        //\neg \bot
        let simple_expr = ExprPool(vec![
            Expr::Unary(MonOp::Not, ExprRef(1)),
            Expr::Constant(Constant::Contradiction),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables),
            LanguageResult::Bool(true)
        );

        //\neg \top
        let simple_expr = ExprPool(vec![
            Expr::Unary(MonOp::Not, ExprRef(1)),
            Expr::Constant(Constant::Tautology),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables),
            LanguageResult::Bool(false)
        );

        //(\neg \bot) \lor (\bot)
        let simple_expr = ExprPool(vec![
            Expr::Binary(BinOp::Or, ExprRef(1), ExprRef(3)),
            Expr::Unary(MonOp::Not, ExprRef(2)),
            Expr::Constant(Constant::Contradiction),
            Expr::Constant(Constant::Contradiction),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables),
            LanguageResult::Bool(true)
        );

        //(\neg \bot) \and (\bot)
        let simple_expr = ExprPool(vec![
            Expr::Binary(BinOp::And, ExprRef(1), ExprRef(3)),
            Expr::Unary(MonOp::Not, ExprRef(2)),
            Expr::Constant(Constant::Contradiction),
            Expr::Constant(Constant::Contradiction),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables),
            LanguageResult::Bool(false)
        );

        //For all actors there exists an event such that they are its patient and TOP.
        let simple_expr = ExprPool(vec![
            Expr::Quantifier(Quantifier::Universal, Variable(0), ExprRef(1), ExprRef(2)),
            Expr::Constant(Constant::Everyone),
            Expr::Quantifier(Quantifier::Existential, Variable(1), ExprRef(3), ExprRef(4)),
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::And, ExprRef(5), ExprRef(8)),
            Expr::Binary(BinOp::PatientOf, ExprRef(6), ExprRef(7)),
            Expr::Variable(Variable(0)),
            Expr::Variable(Variable(1)),
            Expr::Constant(Constant::Tautology),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables),
            LanguageResult::Bool(false)
        );
    }
}
