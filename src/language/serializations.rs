use serde::{Deserialize, Deserializer, Serialize};

use crate::{
    lambda::{FreeVar, LambdaExpr, LambdaExprRef, RootedLambdaPool, types::LambdaType},
    language::{
        ActorOrEvent, BinOp, Expr, MonOp,
        lambda_implementation::{AssociativityData, add_parenthesis_for_bin_op},
    },
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

impl<'de> Deserialize<'de> for LambdaType {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        LambdaType::from_string(&s).map_err(serde::de::Error::custom)
    }
}
impl<'src> Serialize for RootedLambdaPool<'src, Expr<'src>> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.to_string().as_str())
    }
}
impl<'de, 'a> Deserialize<'de> for RootedLambdaPool<'a, Expr<'a>>
where
    'de: 'a,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = <&'de str>::deserialize(deserializer)?;
        RootedLambdaPool::parse(s).map_err(serde::de::Error::custom)
    }
}

impl RootedLambdaPool<'_, Expr<'_>> {
    pub(super) fn tokens<'a, 'b: 'a>(
        &'a self,
        expr: LambdaExprRef,
        c: VarContext,
        v: &mut Vec<Token<'a>>,
        parent_is_app: bool,
    ) -> AssociativityData {
        match self.get(expr) {
            LambdaExpr::Lambda(child, lambda_type) => {
                let (c, var) = c.inc_depth(lambda_type);
                v.push(Token::Lambda {
                    t: lambda_type,
                    var: TokenVar::Bound(var),
                });

                self.tokens(*child, c, v, false);
                AssociativityData::Lambda
            }
            LambdaExpr::BoundVariable(bvar, lambda_type) => {
                v.push(Token::Var(TokenVar::Bound(
                    c.lambda_var(*bvar, lambda_type),
                )));
                AssociativityData::Monop
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
                AssociativityData::Monop
            }

            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                let mut new_v = vec![];

                match self.tokens(*subformula, c.clone(), &mut new_v, true) {
                    AssociativityData::Binom(_) | AssociativityData::Lambda => {
                        v.push(Token::OpenDelim);
                        v.extend(new_v);
                        v.push(Token::CloseDelim);
                        v.push(Token::OpenDelim);
                    }
                    AssociativityData::Monop => {
                        v.extend(new_v);
                        v.push(Token::OpenDelim);
                    }
                    AssociativityData::App => {
                        v.extend(new_v);
                    }
                }
                self.tokens(*argument, c.clone(), v, false);

                if parent_is_app {
                    v.push(Token::ArgSep);
                } else {
                    v.push(Token::CloseDelim);
                }
                AssociativityData::App
            }
            LambdaExpr::LanguageOfThoughtExpr(x) => match x {
                Expr::Quantifier {
                    quantifier,
                    var_type,
                    restrictor,
                    subformula,
                } => {
                    let (c, var_string) = c.inc_depth_q(*var_type);

                    v.push(Token::Quantifier {
                        q: quantifier.to_string(),
                        t: match var_type {
                            ActorOrEvent::Actor => LambdaType::a(),
                            ActorOrEvent::Event => LambdaType::e(),
                        },
                        var: TokenVar::Bound(var_string),
                    });
                    v.push(Token::OpenDelim);
                    self.tokens(LambdaExprRef(restrictor.0), c.clone(), v, false);
                    v.push(Token::ArgSep);
                    self.tokens(LambdaExprRef(subformula.0), c, v, false);
                    v.push(Token::CloseDelim);
                    AssociativityData::Monop
                }
                Expr::Unary(MonOp::Iota(var_type), subformula) => {
                    let (c, var_string) = c.inc_depth_q(*var_type);

                    v.push(Token::Iota {
                        t: match var_type {
                            ActorOrEvent::Actor => LambdaType::a(),
                            ActorOrEvent::Event => LambdaType::e(),
                        },
                        var: TokenVar::Bound(var_string),
                    });
                    v.push(Token::OpenDelim);
                    self.tokens(LambdaExprRef(subformula.0), c, v, false);
                    v.push(Token::CloseDelim);
                    AssociativityData::Monop
                }
                Expr::Variable(variable) => {
                    v.push(Token::Var(TokenVar::Bound(c.lambda_var(
                        variable.id() as usize,
                        variable.as_lambda_type(),
                    ))));
                    AssociativityData::Monop
                }
                Expr::Actor(a) => {
                    v.push(Token::Actor(a.to_string()));
                    AssociativityData::Monop
                }
                Expr::Event(e) => {
                    v.push(Token::Event(e.to_string()));
                    AssociativityData::Monop
                }
                Expr::Binary(bin_op, x, y) => match bin_op {
                    BinOp::AgentOf | BinOp::PatientOf => {
                        v.push(Token::Func(bin_op.to_string()));
                        v.push(Token::OpenDelim);
                        self.tokens(LambdaExprRef(x.0), c.clone(), v, false);
                        v.push(Token::ArgSep);
                        self.tokens(LambdaExprRef(y.0), c, v, false);
                        v.push(Token::CloseDelim);
                        AssociativityData::Monop
                    }

                    BinOp::And | BinOp::Or => {
                        let mut x_v = vec![];
                        let x_a = self.tokens(LambdaExprRef(x.0), c.clone(), &mut x_v, false);
                        let mut y_v = vec![];
                        let y_a = self.tokens(LambdaExprRef(y.0), c.clone(), &mut y_v, false);

                        if add_parenthesis_for_bin_op(*bin_op, x_a) {
                            v.push(Token::OpenDelim);
                            v.extend(x_v);
                            v.push(Token::CloseDelim);
                        } else {
                            v.extend(x_v);
                        }
                        v.push(Token::Func(bin_op.to_string()));
                        if add_parenthesis_for_bin_op(*bin_op, y_a) {
                            v.push(Token::OpenDelim);
                            v.extend(y_v);
                            v.push(Token::CloseDelim);
                        } else {
                            v.extend(y_v);
                        }
                        AssociativityData::Binom(*bin_op)
                    }
                },
                Expr::Unary(mon_op, arg) => {
                    let s = match mon_op {
                        super::MonOp::Property(s, _) => s.to_string(),
                        super::MonOp::Iota(_) | super::MonOp::Not => mon_op.to_string(),
                    };
                    v.push(Token::Func(s));

                    let mut new_v = vec![];
                    let child_asso = self.tokens(LambdaExprRef(arg.0), c, &mut new_v, false);

                    if mon_op == &MonOp::Not {
                        match child_asso {
                            AssociativityData::Binom(BinOp::And | BinOp::Or) => {
                                v.push(Token::OpenDelim);
                                v.extend(new_v);
                                v.push(Token::CloseDelim);
                            }
                            AssociativityData::Binom(_)
                            | AssociativityData::Lambda
                            | AssociativityData::App
                            | AssociativityData::Monop => {
                                v.extend(new_v);
                            }
                        }
                    } else {
                        v.push(Token::OpenDelim);
                        v.extend(new_v);
                        v.push(Token::CloseDelim);
                    }

                    AssociativityData::Monop
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
                    AssociativityData::Monop
                }
            },
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(super) enum TokenVar<'a> {
    Bound(String),
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
    Actor(String),
    Event(String),
    Func(String),
    Const(String),
    Iota {
        t: &'a LambdaType,
        var: TokenVar<'a>,
    },
    Quantifier {
        q: String,
        var: TokenVar<'a>,
        t: &'a LambdaType,
    },
    OpenDelim,
    ArgSep,
    CloseDelim,
}

///A special kind of RootedLambdaPool that should be used to display in fancy math modes, e.g. with
///Typst or (potentially) LaTeX.
pub struct MathModeExpression<'a>(Vec<Token<'a>>);

impl<'src> RootedLambdaPool<'src, Expr<'src>> {
    ///Get a [`MathModeExpression`] to be serialized for documents.
    pub fn for_document<'a>(&'a self) -> MathModeExpression<'a> {
        let mut v: Vec<Token> = vec![];
        self.tokens(self.root, VarContext::default(), &mut v, false);
        MathModeExpression(v)
    }
}

impl Serialize for MathModeExpression<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.serialize(serializer)
    }
}

#[cfg(test)]
mod test {

    use crate::lambda::{RootedLambdaPool, types::LambdaType};

    #[test]
    fn type_serializing() -> anyhow::Result<()> {
        for s in ["a", "<a,t>", "<<e,<e,<<a,t>,t>>>, t>"] {
            let t = LambdaType::from_string(s)?;
            let t_str = serde_json::to_string(&t)?;
            let t_json: LambdaType = serde_json::from_str(t_str.as_str())?;
            assert_eq!(t, t_json);
        }

        Ok(())
    }

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
                "[{\"Quantifier\":{\"q\":\"every\",\"var\":{\"Bound\":\"x\"},\"t\":\"a\"}},\"OpenDelim\",{\"Const\":\"all_a\"},\"ArgSep\",{\"Func\":\"Blue\"},\"OpenDelim\",{\"Var\":{\"Bound\":\"x\"}},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "every(x,pa_Blue,pa_Blue(x))",
                "[{\"Quantifier\":{\"q\":\"every\",\"var\":{\"Bound\":\"x\"},\"t\":\"a\"}},\"OpenDelim\",{\"Const\":\"Blue\"},\"ArgSep\",{\"Func\":\"Blue\"},\"OpenDelim\",{\"Var\":{\"Bound\":\"x\"}},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "every(x,pa_5,pa_10(a_59))",
                "[{\"Quantifier\":{\"q\":\"every\",\"var\":{\"Bound\":\"x\"},\"t\":\"a\"}},\"OpenDelim\",{\"Const\":\"5\"},\"ArgSep\",{\"Func\":\"10\"},\"OpenDelim\",{\"Actor\":\"59\"},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "every_e(x,all_e,PatientOf(a_Mary,x))",
                "[{\"Quantifier\":{\"q\":\"every\",\"var\":{\"Bound\":\"x\"},\"t\":\"e\"}},\"OpenDelim\",{\"Const\":\"all_e\"},\"ArgSep\",{\"Func\":\"PatientOf\"},\"OpenDelim\",{\"Actor\":\"Mary\"},\"ArgSep\",{\"Var\":{\"Bound\":\"x\"}},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "(cool#<a,t>)(a_John)",
                "[{\"Var\":{\"Free\":{\"label\":\"cool\",\"t\":\"<a,t>\",\"anon\":false}}},\"OpenDelim\",{\"Actor\":\"John\"},\"CloseDelim\"]",
            ),
            (
                "(bad#<a,t>)(man#a)",
                "[{\"Var\":{\"Free\":{\"label\":\"bad\",\"t\":\"<a,t>\",\"anon\":false}}},\"OpenDelim\",{\"Var\":{\"Free\":{\"label\":\"man\",\"t\":\"a\",\"anon\":false}}},\"CloseDelim\"]",
            ),
            (
                "((loves#<a,<a,t>>)(a_mary))(a_john)",
                "[{\"Var\":{\"Free\":{\"label\":\"loves\",\"t\":\"<a,<a,t>>\",\"anon\":false}}},\"OpenDelim\",{\"Actor\":\"mary\"},\"ArgSep\",{\"Actor\":\"john\"},\"CloseDelim\"]",
            ),
            (
                "True | (True & False)",
                "[{\"Const\":\"True\"},{\"Func\":\"|\"},\"OpenDelim\",{\"Const\":\"True\"},{\"Func\":\"&\"},{\"Const\":\"False\"},\"CloseDelim\"]",
            ),
            (
                "(True | True) & False",
                "[\"OpenDelim\",{\"Const\":\"True\"},{\"Func\":\"|\"},{\"Const\":\"True\"},\"CloseDelim\",{\"Func\":\"&\"},{\"Const\":\"False\"}]",
            ),
            (
                "lambda a x (lambda a y (likes#<a,<a,t>>(x))(y))",
                "[{\"Lambda\":{\"t\":\"a\",\"var\":{\"Bound\":\"x\"}}},{\"Lambda\":{\"t\":\"a\",\"var\":{\"Bound\":\"y\"}}},{\"Var\":{\"Free\":{\"label\":\"likes\",\"t\":\"<a,<a,t>>\",\"anon\":false}}},\"OpenDelim\",{\"Var\":{\"Bound\":\"x\"}},\"ArgSep\",{\"Var\":{\"Bound\":\"y\"}},\"CloseDelim\"]",
            ),
            (
                "lambda <a,t> P iota(x, P(x))",
                "[{\"Lambda\":{\"t\":\"<a,t>\",\"var\":{\"Bound\":\"P\"}}},{\"Iota\":{\"t\":\"a\",\"var\":{\"Bound\":\"x\"}}},\"OpenDelim\",{\"Var\":{\"Bound\":\"P\"}},\"OpenDelim\",{\"Var\":{\"Bound\":\"x\"}},\"CloseDelim\",\"CloseDelim\"]",
            ),
        ] {
            let expression = RootedLambdaPool::parse(statement)?;
            assert_eq!(json, serde_json::to_string(&expression.for_document())?);
        }

        Ok(())
    }
}
