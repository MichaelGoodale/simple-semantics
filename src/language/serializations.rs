use serde::Serialize;

use crate::{
    lambda::{FreeVar, LambdaExpr, LambdaExprRef, RootedLambdaPool, types::LambdaType},
    language::{BinOp, Expr, MonOp, Variable, lambda_implementation::AssociativityData},
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

impl RootedLambdaPool<'_, Expr<'_>> {
    pub(super) fn tokens<'a, 'b: 'a>(
        &'a self,
        expr: LambdaExprRef,
        c: VarContext,
        v: &mut Vec<Token<'a>>,
    ) -> AssociativityData {
        match self.get(expr) {
            LambdaExpr::Lambda(child, lambda_type) => {
                let (c, var) = c.inc_depth();
                v.push(Token::Lambda {
                    t: lambda_type,
                    var: TokenVar::Lambda(var),
                });

                let mut new_v = vec![];
                let child_asso = self.tokens(*child, c, &mut new_v);
                match child_asso {
                    AssociativityData::IsBinom => {
                        v.push(Token::OpenDelim);
                        v.extend(new_v);
                        v.push(Token::CloseDelim);
                    }
                    AssociativityData::IsMonop => v.extend(new_v),
                }

                AssociativityData::IsBinom
            }
            LambdaExpr::BoundVariable(bvar, _) => {
                v.push(Token::Var(TokenVar::Lambda(c.lambda_var(*bvar))));
                AssociativityData::IsMonop
            }
            LambdaExpr::FreeVariable(fvar, t) => {
                v.push(Token::Var(TokenVar::Free {
                    label: fvar.to_string(),
                    t,
                    anon: match fvar {
                        FreeVar::Named(_) => false,
                        FreeVar::Anonymous(_) => true,
                    },
                }));
                AssociativityData::IsMonop
            }

            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                let mut new_v = vec![];

                match self.tokens(*subformula, c.clone(), &mut new_v) {
                    AssociativityData::IsBinom => {
                        v.push(Token::OpenDelim);
                        v.extend(new_v);
                        v.push(Token::CloseDelim);
                    }
                    AssociativityData::IsMonop => v.extend(new_v),
                }

                v.push(Token::OpenDelim);
                self.tokens(*argument, c.clone(), v);
                v.push(Token::CloseDelim);
                AssociativityData::IsBinom
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
                    self.tokens(LambdaExprRef(restrictor.0), c.clone(), v);
                    v.push(Token::ArgSep);
                    self.tokens(LambdaExprRef(subformula.0), c, v);
                    v.push(Token::CloseDelim);
                    AssociativityData::IsMonop
                }
                Expr::Variable(variable) => {
                    v.push(Token::Var(TokenVar::Quantifier(c.q_var(*variable))));
                    AssociativityData::IsMonop
                }
                Expr::Actor(a) => {
                    v.push(Token::Actor(a.to_string()));
                    AssociativityData::IsMonop
                }
                Expr::Event(e) => {
                    v.push(Token::Event(e.to_string()));
                    AssociativityData::IsMonop
                }
                Expr::Binary(bin_op, x, y) => match bin_op {
                    BinOp::AgentOf | BinOp::PatientOf => {
                        v.push(Token::Func(bin_op.to_string()));
                        v.push(Token::OpenDelim);
                        self.tokens(LambdaExprRef(x.0), c.clone(), v);
                        v.push(Token::ArgSep);
                        self.tokens(LambdaExprRef(y.0), c, v);
                        v.push(Token::CloseDelim);
                        AssociativityData::IsMonop
                    }

                    BinOp::And | BinOp::Or => {
                        self.tokens(LambdaExprRef(x.0), c.clone(), v);
                        v.push(Token::Func(bin_op.to_string()));
                        self.tokens(LambdaExprRef(y.0), c, v);
                        AssociativityData::IsBinom
                    }
                },
                Expr::Unary(mon_op, arg) => {
                    let s = match mon_op {
                        super::MonOp::Property(s, _) => s.to_string(),
                        super::MonOp::Tautology
                        | super::MonOp::Not
                        | super::MonOp::Contradiction => mon_op.to_string(),
                    };
                    v.push(Token::Func(s));

                    let mut new_v = vec![];
                    let child_asso = self.tokens(LambdaExprRef(arg.0), c, &mut new_v);
                    match (mon_op, child_asso) {
                        (MonOp::Not, AssociativityData::IsMonop) => {
                            v.extend(new_v);
                        }
                        _ => {
                            v.push(Token::OpenDelim);
                            v.extend(new_v);
                            v.push(Token::CloseDelim);
                        }
                    }
                    AssociativityData::IsMonop
                }
                Expr::Constant(constant) => {
                    let s = match constant {
                        super::Constant::Everyone
                        | super::Constant::EveryEvent
                        | super::Constant::Tautology
                        | super::Constant::Contradiction => constant.to_string(),
                        super::Constant::Property(s, _) => s.to_string(),
                    };
                    v.push(Token::Const(s));
                    AssociativityData::IsMonop
                }
            },
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(super) enum TokenVar<'a> {
    Lambda(String),
    Quantifier(String),
    Free {
        label: String,
        t: &'a LambdaType,
        anon: bool,
    },
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
    ArgSep,
    CloseDelim,
}

impl Serialize for RootedLambdaPool<'_, Expr<'_>> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut v: Vec<Token> = vec![];
        self.tokens(self.root, VarContext::default(), &mut v);
        v.serialize(serializer)
    }
}

#[cfg(test)]
mod test {

    use crate::lambda::RootedLambdaPool;

    #[test]
    fn serializing() -> anyhow::Result<()> {
        for (statement, json) in [
            (
                "~(AgentOf(a_John,e_0))",
                "[{\"Func\":\"~\"},{\"Func\":\"AgentOf\"},\"OpenDelim\",{\"Actor\":\"John\"},\"ArgSep\",{\"Event\":\"0\"},\"CloseDelim\"]",
            ),
            (
                "(pa_Red(a_John) & ~(pa_Red(a_Mary)))",
                "[{\"Func\":\"Red\"},\"OpenDelim\",{\"Actor\":\"John\"},\"CloseDelim\",{\"Func\":\"&\"},{\"Func\":\"~\"},{\"Func\":\"Red\"},\"OpenDelim\",{\"Actor\":\"Mary\"},\"CloseDelim\"]",
            ),
            (
                "every(x,all_a,pa_Blue(x))",
                "[{\"Quantifier\":{\"q\":\"every\",\"var\":{\"Quantifier\":\"x\"},\"t\":\"a\"}},\"OpenDelim\",{\"Const\":\"all_a\"},\"ArgSep\",{\"Func\":\"Blue\"},\"OpenDelim\",{\"Var\":{\"Quantifier\":\"x\"}},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "every(x,pa_Blue,pa_Blue(x))",
                "[{\"Quantifier\":{\"q\":\"every\",\"var\":{\"Quantifier\":\"x\"},\"t\":\"a\"}},\"OpenDelim\",{\"Const\":\"Blue\"},\"ArgSep\",{\"Func\":\"Blue\"},\"OpenDelim\",{\"Var\":{\"Quantifier\":\"x\"}},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "every(x,pa_5,pa_10(a_59))",
                "[{\"Quantifier\":{\"q\":\"every\",\"var\":{\"Quantifier\":\"x\"},\"t\":\"a\"}},\"OpenDelim\",{\"Const\":\"5\"},\"ArgSep\",{\"Func\":\"10\"},\"OpenDelim\",{\"Actor\":\"59\"},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "every_e(x,all_e,PatientOf(a_Mary,x))",
                "[{\"Quantifier\":{\"q\":\"every\",\"var\":{\"Quantifier\":\"x\"},\"t\":\"e\"}},\"OpenDelim\",{\"Const\":\"all_e\"},\"ArgSep\",{\"Func\":\"PatientOf\"},\"OpenDelim\",{\"Actor\":\"Mary\"},\"ArgSep\",{\"Var\":{\"Quantifier\":\"x\"}},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "(cool#<a,t>)(a_John)",
                "[{\"Var\":{\"Free\":{\"label\":\"cool\",\"t\":\"<a,t>\",\"anon\":false}}},\"OpenDelim\",{\"Actor\":\"John\"},\"CloseDelim\"]",
            ),
            (
                "(bad#<a,t>)(man#a)",
                "[{\"Var\":{\"Free\":{\"label\":\"bad\",\"t\":\"<a,t>\",\"anon\":false}}},\"OpenDelim\",{\"Var\":{\"Free\":{\"label\":\"man\",\"t\":\"a\",\"anon\":false}}},\"CloseDelim\"]",
            ),
        ] {
            let expression = RootedLambdaPool::parse(statement)?;
            assert_eq!(json, serde_json::to_string(&expression)?);
        }

        Ok(())
    }
}
