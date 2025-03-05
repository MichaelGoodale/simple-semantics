use crate::{Actor, Entity, Event, PropertyLabel, Scenario};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum BinOp {
    AgentOf,
    PatientOf,
    And,
    Or,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum MonOp {
    Not,
    Property(PropertyLabel),
    Tautology,
    Contradiction,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Constant {
    Everyone,
    EveryEvent,
    Tautology,
    Contradiction,
    Property(PropertyLabel),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
struct Variable(u32);

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum Quantifier {
    Universal,
    Existential,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum Expr {
    Quantifier {
        quantifier: Quantifier,
        var: Variable,
        restrictor: ExprRef,
        subformula: ExprRef,
    },
    BoundVariable(Variable),
    Entity(Entity),
    Binary(BinOp, ExprRef, ExprRef),
    Unary(MonOp, ExprRef),
    Constant(Constant),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
struct ExprRef(u32);

#[derive(Debug, Clone, Default, Eq, PartialEq)]
struct ExprPool(Vec<Expr>);

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LanguageExpression {
    pool: ExprPool,
    start: ExprRef,
}

impl LanguageExpression {
    pub fn run(&self, scenario: &Scenario) -> LanguageResult {
        let mut variables = VariableBuffer::default();
        self.pool.interp(self.start, scenario, &mut variables)
    }
}

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
pub enum LanguageResult {
    PresuppositionError,
    Bool(bool),
    Entity(Entity),
    EntitySet(Vec<Entity>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum LanguageResultType {
    Bool,
    Entity,
    EntitySet,
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

impl TryFrom<LanguageResult> for Entity {
    type Error = ();

    fn try_from(value: LanguageResult) -> Result<Self, Self::Error> {
        match value {
            LanguageResult::Entity(x) => Ok(x),
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
    pub fn new() -> ExprPool {
        ExprPool(vec![])
    }

    fn checked_get(&self, expr: ExprRef) -> Option<&Expr> {
        self.0.get(expr.0 as usize)
    }

    fn get(&self, expr: ExprRef) -> &Expr {
        &self.0[expr.0 as usize]
    }

    fn get_mut(&mut self, expr: ExprRef) -> &mut Expr {
        &mut self.0[expr.0 as usize]
    }

    pub fn add(&mut self, expr: Expr) -> ExprRef {
        let idx = self.0.len();
        self.0.push(expr);
        ExprRef(idx.try_into().expect("Too many exprs in the pool"))
    }

    fn get_type(&self, expr: ExprRef) -> LanguageResultType {
        match self.get(expr) {
            Expr::Quantifier { .. } => LanguageResultType::Bool,
            Expr::BoundVariable(_) => LanguageResultType::Entity,
            Expr::Entity(_) => LanguageResultType::Entity,
            Expr::Binary(..) => LanguageResultType::Bool,
            Expr::Unary(..) => LanguageResultType::Bool,
            Expr::Constant(constant) => match constant {
                Constant::Everyone | Constant::EveryEvent | Constant::Property(_) => {
                    LanguageResultType::EntitySet
                }
                Constant::Tautology | Constant::Contradiction => LanguageResultType::Bool,
            },
        }
    }

    pub fn interp(
        &self,
        expr: ExprRef,
        scenario: &Scenario,
        variables: &mut VariableBuffer,
    ) -> LanguageResult {
        match self.get(expr) {
            Expr::Quantifier {
                quantifier,
                var,
                restrictor,
                subformula,
            } => {
                let mut variables = variables.clone();
                let domain: Vec<Entity> = match self.get_type(*restrictor) {
                    LanguageResultType::Bool => {
                        //TODO: Check if the quantification is over actors or events somehow!
                        let mut domain = vec![];
                        for e in scenario.actors.iter() {
                            variables.set(*var, Entity::Actor(*e));
                            let truth_value_for_e: bool = self
                                .interp(*restrictor, scenario, &mut variables)
                                .try_into()
                                .unwrap();
                            if truth_value_for_e {
                                domain.push(Entity::Actor(*e))
                            }
                        }
                        domain
                    }
                    LanguageResultType::Entity => {
                        let e: Entity = self
                            .interp(*restrictor, scenario, &mut variables)
                            .try_into()
                            .unwrap();
                        vec![e]
                    }
                    LanguageResultType::EntitySet => self
                        .interp(*restrictor, scenario, &mut variables)
                        .try_into()
                        .unwrap(),
                };

                let mut result = match quantifier {
                    Quantifier::Universal => true,
                    Quantifier::Existential => false,
                };
                for e in domain {
                    variables.set(*var, e);
                    let subformula_value: bool = self
                        .interp(*subformula, scenario, &mut variables)
                        .try_into()
                        .unwrap();
                    result = match quantifier {
                        Quantifier::Universal => subformula_value && result,
                        Quantifier::Existential => subformula_value || result,
                    };
                }
                LanguageResult::Bool(result)
            }
            Expr::BoundVariable(i) => LanguageResult::Entity(variables.get(*i).unwrap()),
            Expr::Entity(a) => LanguageResult::Entity(*a),
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
                Constant::Property(p) => match scenario.properties.get(p) {
                    Some(property_members) => LanguageResult::EntitySet(property_members.clone()),
                    None => LanguageResult::EntitySet(vec![]),
                },
            },
            Expr::Unary(mon_op, arg) => {
                let arg = self.interp(*arg, scenario, variables);
                match mon_op {
                    MonOp::Not => LanguageResult::Bool(!TryInto::<bool>::try_into(arg).unwrap()),
                    MonOp::Contradiction => LanguageResult::Bool(false),
                    MonOp::Tautology => LanguageResult::Bool(true),
                    MonOp::Property(e) => {
                        let arg: Entity = arg.try_into().unwrap();
                        match scenario.properties.get(e) {
                            Some(property_members) => {
                                LanguageResult::Bool(property_members.contains(&arg))
                            }
                            None => LanguageResult::Bool(false),
                        }
                    }
                }
            }
        }
    }
}

mod parser;
pub use parser::parse_executable;

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ahash::RandomState;

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
            properties: HashMap::default(),
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
            properties: HashMap::default(),
        };

        //For all actors there exists an event such that they are its agent.
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var: Variable(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Everyone),
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var: Variable(1),
                restrictor: ExprRef(3),
                subformula: ExprRef(4),
            },
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::AgentOf, ExprRef(5), ExprRef(6)),
            Expr::BoundVariable(Variable(0)),
            Expr::BoundVariable(Variable(1)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables),
            LanguageResult::Bool(true)
        );

        //For all actors there exists an event such that they are its patient.
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var: Variable(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Everyone),
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var: Variable(1),
                restrictor: ExprRef(3),
                subformula: ExprRef(4),
            },
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::PatientOf, ExprRef(5), ExprRef(6)),
            Expr::BoundVariable(Variable(0)),
            Expr::BoundVariable(Variable(1)),
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
            properties: HashMap::default(),
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
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var: Variable(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Everyone),
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var: Variable(1),
                restrictor: ExprRef(3),
                subformula: ExprRef(4),
            },
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::And, ExprRef(5), ExprRef(8)),
            Expr::Binary(BinOp::PatientOf, ExprRef(6), ExprRef(7)),
            Expr::BoundVariable(Variable(0)),
            Expr::BoundVariable(Variable(1)),
            Expr::Constant(Constant::Tautology),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables),
            LanguageResult::Bool(false)
        );
    }

    #[test]
    fn properties() {
        let mut variables = VariableBuffer(vec![]);
        let mut properties: HashMap<_, _, RandomState> = HashMap::default();
        properties.insert(1, vec![Entity::Actor(0), Entity::Actor(1)]);
        properties.insert(534, vec![Entity::Actor(1)]);
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

        // everyone is of property type one.
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var: Variable(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Everyone),
            Expr::Unary(MonOp::Property(1), ExprRef(3)),
            Expr::BoundVariable(Variable(0)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables),
            LanguageResult::Bool(true)
        );
        // someone is of property type 534.
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var: Variable(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Everyone),
            Expr::Unary(MonOp::Property(534), ExprRef(3)),
            Expr::BoundVariable(Variable(0)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables),
            LanguageResult::Bool(true)
        );
    }

    #[test]
    fn complicated_restrictors() {
        let mut variables = VariableBuffer(vec![]);
        let mut properties: HashMap<_, _, RandomState> = HashMap::default();
        properties.insert(534, vec![Entity::Actor(1)]);
        properties.insert(235, vec![Entity::Event(0)]);
        properties.insert(2, vec![Entity::Actor(0)]);
        let simple_scenario = Scenario {
            actors: vec![0, 1],
            thematic_relations: vec![ThetaRoles {
                agent: Some(1),
                patient: Some(0),
            }],
            properties,
        };

        // all property type 534 objects are agents of a 235-event
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var: Variable(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Property(534)),
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var: Variable(1),
                restrictor: ExprRef(3),
                subformula: ExprRef(4),
            },
            Expr::Constant(Constant::Property(235)),
            Expr::Binary(BinOp::AgentOf, ExprRef(5), ExprRef(6)),
            Expr::BoundVariable(Variable(0)),
            Expr::BoundVariable(Variable(1)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables),
            LanguageResult::Bool(true)
        );
        // all property type 2 objects are agents of a 235-event (which is false)
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var: Variable(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(2),
            },
            Expr::Constant(Constant::Property(2)),
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var: Variable(1),
                restrictor: ExprRef(3),
                subformula: ExprRef(4),
            },
            Expr::Constant(Constant::Property(235)),
            Expr::Binary(BinOp::AgentOf, ExprRef(5), ExprRef(6)),
            Expr::BoundVariable(Variable(0)),
            Expr::BoundVariable(Variable(1)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables),
            LanguageResult::Bool(false)
        );

        let mut properties: HashMap<_, _, RandomState> = HashMap::default();
        properties.insert(3, vec![Entity::Actor(1), Entity::Actor(2)]);
        properties.insert(2, vec![Entity::Actor(1), Entity::Actor(3)]);
        properties.insert(4, vec![Entity::Event(0)]);
        let simple_scenario = Scenario {
            actors: vec![0, 1, 2, 3, 4],
            thematic_relations: vec![ThetaRoles {
                agent: Some(1),
                patient: Some(0),
            }],
            properties,
        };
        //All property type 2 and property type 3 actors are an agent of an event
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var: Variable(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(6),
            },
            Expr::Binary(BinOp::And, ExprRef(2), ExprRef(4)),
            Expr::Unary(MonOp::Property(2), ExprRef(3)),
            Expr::BoundVariable(Variable(0)),
            Expr::Unary(MonOp::Property(3), ExprRef(5)),
            Expr::BoundVariable(Variable(0)), //5
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var: Variable(1),
                restrictor: ExprRef(7),
                subformula: ExprRef(8),
            },
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::AgentOf, ExprRef(9), ExprRef(10)),
            Expr::BoundVariable(Variable(0)),
            Expr::BoundVariable(Variable(1)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables),
            LanguageResult::Bool(true)
        );
        //All property type 2 and property type 3 actors are patients of an event
        let simple_expr = ExprPool(vec![
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var: Variable(0),
                restrictor: ExprRef(1),
                subformula: ExprRef(6),
            },
            Expr::Binary(BinOp::And, ExprRef(2), ExprRef(4)),
            Expr::Unary(MonOp::Property(2), ExprRef(3)),
            Expr::BoundVariable(Variable(0)),
            Expr::Unary(MonOp::Property(3), ExprRef(5)),
            Expr::BoundVariable(Variable(0)), //5
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var: Variable(1),
                restrictor: ExprRef(7),
                subformula: ExprRef(8),
            },
            Expr::Constant(Constant::EveryEvent),
            Expr::Binary(BinOp::PatientOf, ExprRef(9), ExprRef(10)),
            Expr::BoundVariable(Variable(0)),
            Expr::BoundVariable(Variable(1)),
        ]);
        assert_eq!(
            simple_expr.interp(ExprRef(0), &simple_scenario, &mut variables),
            LanguageResult::Bool(false)
        );
    }
}
