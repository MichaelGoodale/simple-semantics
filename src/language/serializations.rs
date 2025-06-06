use serde::Serialize;

use crate::{
    LabelledScenarios,
    lambda::{LambdaExpr, LambdaExprRef, RootedLambdaPool, types::LambdaType},
    language::{BinOp, Expr, Variable},
};

use crate::language::lambda_implementation::VarContext;

impl Serialize for LambdaType {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.to_string().as_str())
    }
}

impl RootedLambdaPool<Expr<'_>> {
    pub(super) fn tokens<'a, 'b: 'a>(
        &'a self,
        expr: LambdaExprRef,
        c: VarContext,
        v: &mut Vec<Token<'a>>,
        labels: Option<&'b LabelledScenarios>,
    ) {
        match self.get(expr) {
            LambdaExpr::Lambda(child, lambda_type) => {
                let (c, var) = c.inc_depth();
                v.push(Token::Lambda {
                    t: lambda_type,
                    var: TokenVar::Lambda(var),
                });
                v.push(Token::OpenDelim);
                self.tokens(*child, c, v, labels);
                v.push(Token::CloseDelim);
            }
            LambdaExpr::BoundVariable(bvar, _) => {
                v.push(Token::Var(TokenVar::Lambda(c.lambda_var(*bvar))))
            }
            LambdaExpr::FreeVariable(fvar, t) => {
                v.push(Token::Var(TokenVar::Free {
                    label: fvar.to_string(),
                    t,
                }));
            }

            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                v.push(Token::OpenDelim);
                self.tokens(*subformula, c.clone(), v, labels);
                v.push(Token::CloseDelim);
                v.push(Token::OpenDelim);
                self.tokens(*argument, c.clone(), v, labels);
                v.push(Token::CloseDelim);
            }
            LambdaExpr::LanguageOfThoughtExpr(x) => match x {
                Expr::Quantifier {
                    quantifier,
                    var,
                    restrictor,
                    subformula,
                } => {
                    let (c, var_string) = c.add_qvar(*var);

                    v.push(Token::Quantifier {
                        q: quantifier.to_string(),
                        t: match var {
                            Variable::Actor(_) => LambdaType::a(),
                            Variable::Event(_) => LambdaType::e(),
                        },
                        var: TokenVar::Quantifier(var_string),
                    });
                    v.push(Token::OpenDelim);
                    self.tokens(LambdaExprRef(restrictor.0), c.clone(), v, labels);
                    v.push(Token::CloseDelim);
                    v.push(Token::OpenDelim);
                    self.tokens(LambdaExprRef(subformula.0), c, v, labels);
                    v.push(Token::CloseDelim);
                }
                Expr::Variable(variable) => {
                    v.push(Token::Var(TokenVar::Quantifier(c.q_var(*variable))))
                }
                Expr::Actor(a) => v.push(Token::Actor(a.to_string())),
                Expr::Event(e) => v.push(Token::Event(e.to_string())),
                Expr::Binary(bin_op, x, y) => match bin_op {
                    BinOp::AgentOf | BinOp::PatientOf => {
                        v.push(Token::Func(bin_op.to_string()));
                        v.push(Token::OpenDelim);
                        self.tokens(LambdaExprRef(x.0), c.clone(), v, labels);
                        self.tokens(LambdaExprRef(y.0), c, v, labels);
                        v.push(Token::CloseDelim);
                    }

                    BinOp::And | BinOp::Or => {
                        v.push(Token::OpenDelim);
                        self.tokens(LambdaExprRef(x.0), c.clone(), v, labels);
                        v.push(Token::Func(bin_op.to_string()));
                        self.tokens(LambdaExprRef(y.0), c, v, labels);
                        v.push(Token::CloseDelim);
                    }
                },
                Expr::Unary(mon_op, arg) => {
                    v.push(Token::Func(mon_op.to_string()));
                    v.push(Token::OpenDelim);
                    self.tokens(LambdaExprRef(arg.0), c, v, labels);
                    v.push(Token::CloseDelim);
                }
                Expr::Constant(constant) => {
                    v.push(Token::Const(constant.to_string()));
                }
            },
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(super) enum TokenVar<'a> {
    Lambda(String),
    Quantifier(String),
    Free { label: String, t: &'a LambdaType },
}

#[derive(Debug, Clone, Serialize)]
pub(super) enum Token<'a> {
    Lambda {
        t: &'a LambdaType,
        var: TokenVar<'a>,
    },
    Var(TokenVar<'a>),
    BinOp(String),
    Actor(String),
    Event(String),
    Func(String),
    Const(String),
    Quantifier {
        q: String,
        var: TokenVar<'a>,
        t: &'a LambdaType,
    },
    OpenDelim,
    CloseDelim,
}

impl Serialize for RootedLambdaPool<Expr<'_>> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut v: Vec<Token> = vec![];
        self.tokens(self.root, VarContext::default(), &mut v, None);
        v.serialize(serializer)
    }
}

#[cfg(test)]
mod test {

    use crate::{Entity, LabelledScenarios, Scenario, ThetaRoles, lambda::RootedLambdaPool};

    use ahash::HashMap;

    #[test]
    fn serializing() -> anyhow::Result<()> {
        let mut properties = HashMap::default();

        properties.insert(1, vec![Entity::Actor(1)]);
        properties.insert(4, vec![Entity::Actor(0), Entity::Actor(1)]);

        let simple_scenario = Scenario {
            question: None,
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
            sentences: vec![],
            lemmas: vec![],
        };

        for (statement, json) in [
            (
                "~(AgentOf(a_John,e0))",
                "[{\"Func\":\"~\"},\"OpenDelim\",{\"Func\":\"AgentOf\"},\"OpenDelim\",{\"Actor\":\"John\"},{\"Event\":\"0\"},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "(pa_Red(a_John) & ~(pa_Red(a_Mary)))",
                "[\"OpenDelim\",{\"Func\":\"Red\"},\"OpenDelim\",{\"Actor\":\"John\"},\"CloseDelim\",{\"Func\":\"&\"},{\"Func\":\"~\"},\"OpenDelim\",{\"Func\":\"Red\"},\"OpenDelim\",{\"Actor\":\"Mary\"},\"CloseDelim\",\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "every(x,all_a,pa_Blue(x))",
                "[{\"Quantifier\":{\"q\":\"every\",\"var\":{\"Quantifier\":\"x\"},\"t\":\"a\"}},\"OpenDelim\",{\"Const\":\"all_a\"},\"CloseDelim\",\"OpenDelim\",{\"Func\":\"Blue\"},\"OpenDelim\",{\"Var\":{\"Quantifier\":\"x\"}},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "every(x,pa_Blue,pa_Blue(x))",
                "[{\"Quantifier\":{\"q\":\"every\",\"var\":{\"Quantifier\":\"x\"},\"t\":\"a\"}},\"OpenDelim\",{\"Const\":\"Blue\"},\"CloseDelim\",\"OpenDelim\",{\"Func\":\"Blue\"},\"OpenDelim\",{\"Var\":{\"Quantifier\":\"x\"}},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "every(x,pa5,pa10(a59))",
                "[{\"Quantifier\":{\"q\":\"every\",\"var\":{\"Quantifier\":\"x\"},\"t\":\"a\"}},\"OpenDelim\",{\"Const\":\"pa5\"},\"CloseDelim\",\"OpenDelim\",{\"Func\":\"pa10\"},\"OpenDelim\",{\"Actor\":\"59\"},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "every_e(x,all_e,PatientOf(a_Mary,x))",
                "[{\"Quantifier\":{\"q\":\"every\",\"var\":{\"Quantifier\":\"x\"},\"t\":\"e\"}},\"OpenDelim\",{\"Const\":\"all_e\"},\"CloseDelim\",\"OpenDelim\",{\"Func\":\"PatientOf\"},\"OpenDelim\",{\"Actor\":\"Mary\"},{\"Var\":{\"Quantifier\":\"x\"}},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "(cool#<a,t>)(a_John)",
                "[\"OpenDelim\",{\"Var\":{\"Free\":{\"label\":\"cool\",\"t\":\"<a,t>\"}}},\"CloseDelim\",\"OpenDelim\",{\"Actor\":\"John\"},\"CloseDelim\"]",
            ),
            (
                "(bad#<a,t>)(man#a)",
                "[\"OpenDelim\",{\"Var\":{\"Free\":{\"label\":\"bad\",\"t\":\"<a,t>\"}}},\"CloseDelim\",\"OpenDelim\",{\"Var\":{\"Free\":{\"label\":\"man\",\"t\":\"a\"}}},\"CloseDelim\"]",
            ),
        ] {
            let expression = RootedLambdaPool::parse(statement, &mut labels)?;
            assert_eq!(
                json,
                serde_json::to_string(&expression.serialize_with_labels(&labels))?
            );
        }

        Ok(())
    }
}
