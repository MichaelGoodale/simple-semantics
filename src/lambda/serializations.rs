use std::borrow::Cow;
use std::fmt::{Debug, Display};

use serde::{Deserialize, Serialize};

use crate::lambda::ExprType;
use crate::lambda::parser::{ExprToken, ParseLot, Token};
use crate::lambda::types::LambdaType;
use crate::lambda::{
    LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, RootedLambdaPool,
    printing::AssociativityData,
};

use crate::lambda::printing::{InfixPosition, VarContext};

impl<'src, T: Display + LambdaLanguageOfThought + ParseLot<'src> + PartialEq> Serialize
    for RootedLambdaPool<'src, T>
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.to_string().as_str())
    }
}
impl<'de, 'a, T> Deserialize<'de> for RootedLambdaPool<'a, T>
where
    'de: 'a,
    T: ParseLot<'a> + LambdaLanguageOfThought + Clone + PartialEq + Debug,
    T::Token: Display + Clone + PartialEq + Debug,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = <&'de str>::deserialize(deserializer)?;
        RootedLambdaPool::parse(s).map_err(serde::de::Error::custom)
    }
}

enum BindingToken<'src, T: ParseLot<'src>> {
    Token(Token<'src, T>),
    BindingToken {
        expr: T::Token,
        var_name: String,
        var_type: LambdaType,
    },
}

impl<'src, T: LambdaLanguageOfThought + ParseLot<'src> + PartialEq> RootedLambdaPool<'src, T> {
    fn tokens<'a>(
        &'a self,
        expr: LambdaExprRef,
        c: VarContext,
        v: &mut Vec<BindingToken<'src, T>>,
        parent_is_app: bool,
    ) -> AssociativityData<'a, T> {
        match self.get(expr) {
            LambdaExpr::Lambda(child, lambda_type) => {
                let (c, var) = c.inc_depth(lambda_type);
                v.push(BindingToken::Token(Token::Lambda(
                    lambda_type.clone(),
                    Cow::Owned(var),
                )));

                self.tokens(*child, c, v, false);
                AssociativityData::Lambda
            }
            LambdaExpr::BoundVariable(bvar, _) => {
                v.push(BindingToken::Token(Token::Variable(Cow::Owned(
                    c.lambda_var(*bvar),
                ))));
                AssociativityData::Var
            }
            LambdaExpr::FreeVariable(fvar, t) => {
                v.push(BindingToken::Token(Token::FreeVariable(*fvar, t.clone())));
                AssociativityData::Var
            }

            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                let mut f_v = vec![];
                let mut arg_v = vec![];

                let f_asso = self.tokens(*subformula, c.clone(), &mut f_v, true);
                let arg_asso = self.tokens(*argument, c.clone(), &mut arg_v, false);

                if let AssociativityData::Infix(t1, _) = arg_asso
                    && let AssociativityData::Infix(t2, _) = f_asso
                    && t1 != t2
                {
                    arg_v.insert(0, BindingToken::Token(Token::OpenDelim));
                    arg_v.push(BindingToken::Token(Token::CloseDelim));
                }

                match f_asso {
                    AssociativityData::Infix(x, InfixPosition::Op) if parent_is_app => {
                        v.extend(arg_v);
                        v.extend(f_v);
                        return AssociativityData::Infix(x, InfixPosition::DoneLeftOnly);
                    }
                    AssociativityData::Infix(x, InfixPosition::DoneLeftOnly) => {
                        v.extend(f_v);
                        v.extend(arg_v);
                        return AssociativityData::Infix(x, InfixPosition::Done);
                    }
                    AssociativityData::Prefix => {
                        match arg_asso {
                            AssociativityData::App
                            | AssociativityData::Var
                            | AssociativityData::Prefix => {
                                v.extend(f_v);
                                v.extend(arg_v);
                            }
                            AssociativityData::Lambda | AssociativityData::Infix(..) => {
                                v.extend(f_v);
                                v.push(BindingToken::Token(Token::OpenDelim));
                                v.extend(arg_v);
                                v.push(BindingToken::Token(Token::CloseDelim));
                            }
                        };

                        return AssociativityData::Var;
                    }
                    AssociativityData::Lambda
                    | AssociativityData::Infix(_, InfixPosition::Done) => {
                        v.push(BindingToken::Token(Token::OpenDelim));
                        v.extend(f_v);
                        v.extend([Token::CloseDelim, Token::OpenDelim].map(BindingToken::Token));
                        v.extend(arg_v);
                    }
                    AssociativityData::Var | AssociativityData::Infix(_, InfixPosition::Op) => {
                        v.extend(f_v);
                        v.push(BindingToken::Token(Token::OpenDelim));
                        v.extend(arg_v);
                    }
                    AssociativityData::App => {
                        v.extend(f_v);
                        v.extend(arg_v);
                    }
                }

                v.push(BindingToken::Token(if parent_is_app {
                    Token::ArgSep
                } else {
                    Token::CloseDelim
                }));
                AssociativityData::App
            }
            LambdaExpr::LanguageOfThoughtExpr(x, super::ExprType::NoVar) => {
                v.push(BindingToken::Token(Token::LanguageOfThought(
                    x.into_token(),
                )));
                if x.commutative() & x.infix() {
                    AssociativityData::Infix(x, InfixPosition::Op)
                } else if x.unary_associative() {
                    AssociativityData::Prefix
                } else {
                    AssociativityData::Var
                }
            }
            LambdaExpr::LanguageOfThoughtExpr(x, ExprType::BindVar(body)) => {
                let (c, var_string) = c.inc_depth(x.var_type().expect(
                    "Implementation error, if you bind a var, the expression must bind vars!",
                ));

                v.push(BindingToken::BindingToken {
                    expr: x.into_token(),
                    var_name: var_string,
                    var_type: x.var_type().unwrap().clone(),
                });
                v.push(BindingToken::Token(Token::OpenDelim));
                self.tokens(*body, c, v, false);
                v.push(BindingToken::Token(Token::CloseDelim));
                AssociativityData::Var
            }
            LambdaExpr::LanguageOfThoughtExpr(x, ExprType::BindVarTwoBodies(l, r)) => {
                let (c, var_string) = c.inc_depth(x.var_type().expect(
                    "Implementation error, if you bind a var, the expression must bind vars!",
                ));
                v.push(BindingToken::BindingToken {
                    expr: x.into_token(),
                    var_name: var_string,
                    var_type: x.var_type().unwrap().clone(),
                });

                v.push(BindingToken::Token(Token::OpenDelim));
                self.tokens(*l, c.clone(), v, false);
                v.push(BindingToken::Token(Token::ArgSep));
                self.tokens(*r, c, v, false);
                v.push(BindingToken::Token(Token::CloseDelim));
                AssociativityData::Var
            }
        }
    }
}

impl<'src, T> serde::Serialize for BindingToken<'src, T>
where
    T: ParseLot<'src>,
    T::Token: serde::Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeStructVariant;

        match self {
            Self::Token(token) => token.serialize(serializer),
            Self::BindingToken {
                expr,
                var_name,
                var_type,
            } => {
                let mut state =
                    serializer.serialize_struct_variant("BindingToken", 0, "BindingToken", 3)?;

                state.serialize_field("expr", expr)?;
                state.serialize_field("var_name", var_name)?;
                state.serialize_field("var_type", var_type)?;

                state.end()
            }
        }
    }
}

impl<'src, T> serde::Serialize for Token<'src, T>
where
    T: ParseLot<'src>,
    T::Token: serde::Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            Self::OpenDelim => serializer.serialize_unit_variant("Token", 0, "OpenDelim"),
            Self::ArgSep => serializer.serialize_unit_variant("Token", 1, "ArgSep"),
            Self::CloseDelim => serializer.serialize_unit_variant("Token", 2, "CloseDelim"),

            Self::Lambda(ty, var) => {
                serializer.serialize_newtype_variant("Token", 3, "Lambda", &(var, ty))
            }

            Self::Variable(var) => {
                serializer.serialize_newtype_variant("Token", 4, "Variable", var)
            }

            Self::FreeVariable(var, ty) => {
                serializer.serialize_newtype_variant("Token", 5, "FreeVariable", &(var, ty))
            }

            Self::LanguageOfThought(token) => token.serialize(serializer),
        }
    }
}

impl Serialize for ExprToken<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            ExprToken::Constant(crate::language::Constant::Property(p, _)) => {
                serializer.serialize_newtype_variant("Expr", 1, "Func", p)
            }
            ExprToken::Constant(constant) => {
                serializer.serialize_newtype_variant("Expr", 0, "Const", &constant.to_string())
            }
            ExprToken::BinOp(f) => {
                serializer.serialize_newtype_variant("Expr", 1, "Func", &f.to_string())
            }
            ExprToken::MonOp(f) => {
                serializer.serialize_newtype_variant("Expr", 1, "Func", &f.to_string())
            }
            ExprToken::Actor(a) => serializer.serialize_newtype_variant("Expr", 2, "Actor", &a),
            ExprToken::Event(e) => serializer.serialize_newtype_variant("Expr", 3, "Event", e),
            ExprToken::Iota(actor_or_event) => {
                serializer.serialize_newtype_variant("Expr", 3, "Iota", &actor_or_event.to_string())
            }

            ExprToken::Quantifier(quantifier, _) => serializer.serialize_newtype_variant(
                "Expr",
                4,
                "Quantifier",
                &quantifier.to_string(),
            ),
        }
    }
}

///A special kind of `RootedLambdaPool` that should be used to display in fancy math modes, e.g. with
///Typst or (potentially) LaTeX.
pub struct MathModeExpression<'src, T: ParseLot<'src>>(Vec<BindingToken<'src, T>>);

impl<'src, T: ParseLot<'src> + LambdaLanguageOfThought + 'src + PartialEq> RootedLambdaPool<'src, T>
where
    T::Token: Serialize,
{
    ///Get a [`MathModeExpression`] to be serialized for documents.
    #[must_use]
    pub fn for_document(&self) -> MathModeExpression<'src, T> {
        let mut v: Vec<BindingToken<'src, T>> = vec![];
        self.tokens(self.root, VarContext::default(), &mut v, false);
        MathModeExpression(v)
    }
}

impl<'src, T: ParseLot<'src>> Serialize for MathModeExpression<'src, T>
where
    T::Token: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.serialize(serializer)
    }
}

#[cfg(test)]
mod test {

    use crate::{
        lambda::{RootedLambdaPool, types::LambdaType},
        language::Expr,
    };

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
                "[{\"Func\":\"~\"},{\"Func\":\"AgentOf\"},\"OpenDelim\",{\"Actor\":\"John\"},\"ArgSep\",{\"Event\":0},\"CloseDelim\"]",
            ),
            (
                "(pa_Red(a_John) & ~(pa_Red(a_Mary)))",
                "[{\"Func\":\"Red\"},\"OpenDelim\",{\"Actor\":\"John\"},\"CloseDelim\",{\"Func\":\"&\"},{\"Func\":\"~\"},{\"Func\":\"Red\"},\"OpenDelim\",{\"Actor\":\"Mary\"},\"CloseDelim\"]",
            ),
            (
                "every(x,all_a(x),pa_Blue(x))",
                "[{\"BindingToken\":{\"expr\":{\"Quantifier\":\"every\"},\"var_name\":\"x\",\"var_type\":\"a\"}},\"OpenDelim\",{\"Const\":\"all_a\"},\"OpenDelim\",{\"Variable\":\"x\"},\"CloseDelim\",\"ArgSep\",{\"Func\":\"Blue\"},\"OpenDelim\",{\"Variable\":\"x\"},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "every(x,pa_Blue(x),pa_Blue(x))",
                "[{\"BindingToken\":{\"expr\":{\"Quantifier\":\"every\"},\"var_name\":\"x\",\"var_type\":\"a\"}},\"OpenDelim\",{\"Func\":\"Blue\"},\"OpenDelim\",{\"Variable\":\"x\"},\"CloseDelim\",\"ArgSep\",{\"Func\":\"Blue\"},\"OpenDelim\",{\"Variable\":\"x\"},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "every(x,pa_5(x),pa_10(a_59))",
                "[{\"BindingToken\":{\"expr\":{\"Quantifier\":\"every\"},\"var_name\":\"x\",\"var_type\":\"a\"}},\"OpenDelim\",{\"Func\":\"5\"},\"OpenDelim\",{\"Variable\":\"x\"},\"CloseDelim\",\"ArgSep\",{\"Func\":\"10\"},\"OpenDelim\",{\"Actor\":\"59\"},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "every_e(x,all_e(x),PatientOf(a_Mary,x))",
                "[{\"BindingToken\":{\"expr\":{\"Quantifier\":\"every\"},\"var_name\":\"x\",\"var_type\":\"e\"}},\"OpenDelim\",{\"Const\":\"all_e\"},\"OpenDelim\",{\"Variable\":\"x\"},\"CloseDelim\",\"ArgSep\",{\"Func\":\"PatientOf\"},\"OpenDelim\",{\"Actor\":\"Mary\"},\"ArgSep\",{\"Variable\":\"x\"},\"CloseDelim\",\"CloseDelim\"]",
            ),
            (
                "(cool#<a,t>)(a_John)",
                "[{\"FreeVariable\":[{\"Named\":\"cool\"},\"<a,t>\"]},\"OpenDelim\",{\"Actor\":\"John\"},\"CloseDelim\"]",
            ),
            (
                "(bad#<a,t>)(man#a)",
                "[{\"FreeVariable\":[{\"Named\":\"bad\"},\"<a,t>\"]},\"OpenDelim\",{\"FreeVariable\":[{\"Named\":\"man\"},\"a\"]},\"CloseDelim\"]",
            ),
            (
                "((loves#<a,<a,t>>)(a_mary))(a_john)",
                "[{\"FreeVariable\":[{\"Named\":\"loves\"},\"<a,<a,t>>\"]},\"OpenDelim\",{\"Actor\":\"mary\"},\"ArgSep\",{\"Actor\":\"john\"},\"CloseDelim\"]",
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
                "[{\"Lambda\":[\"x\",\"a\"]},{\"Lambda\":[\"y\",\"a\"]},{\"FreeVariable\":[{\"Named\":\"likes\"},\"<a,<a,t>>\"]},\"OpenDelim\",{\"Variable\":\"x\"},\"ArgSep\",{\"Variable\":\"y\"},\"CloseDelim\"]",
            ),
            (
                "lambda <a,t> P iota(x, P(x))",
                "[{\"Lambda\":[\"P\",\"<a,t>\"]},{\"BindingToken\":{\"expr\":{\"Func\":\"iota\"},\"var_name\":\"x\",\"var_type\":\"a\"}},\"OpenDelim\",{\"Variable\":\"P\"},\"OpenDelim\",{\"Variable\":\"x\"},\"CloseDelim\",\"CloseDelim\"]",
            ),
        ] {
            let expression = RootedLambdaPool::<Expr>::parse(statement)?;
            assert_eq!(json, serde_json::to_string(&expression.for_document())?);
        }

        Ok(())
    }
}
