use std::fmt::{Debug, Display};

use itertools::Itertools;
use serde::{Deserialize, Serialize};

use crate::lambda::parser::ParseLot;
use crate::lambda::types::LambdaType;
use crate::lambda::{ExprType, FreeVar};
use crate::lambda::{LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, RootedLambdaPool};

use crate::lambda::printing::VarContext;

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

#[derive(Clone)]
enum BaseExpr<T> {
    Variable(String, Option<LambdaType>),
    AnonymousVariable(usize, LambdaType),
    Expr(T),
}

impl<T: LambdaLanguageOfThought> BaseExpr<T> {
    fn infix(&self) -> bool {
        if let BaseExpr::Expr(x) = self {
            x.infix()
        } else {
            false
        }
    }
}

impl<T: Serialize> Serialize for BaseExpr<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            BaseExpr::Variable(name, _) => {
                serializer.serialize_newtype_variant("BaseExpr", 0, "Variable", name)
            }

            BaseExpr::AnonymousVariable(index, _) => {
                serializer.serialize_newtype_variant("BaseExpr", 1, "AnonymousVariable", index)
            }

            BaseExpr::Expr(expr) => {
                serializer.serialize_newtype_variant("BaseExpr", 2, "Expr", expr)
            }
        }
    }
}

impl<T: Display> Display for BaseExpr<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BaseExpr::Variable(x, None) => write!(f, "{x}"),
            BaseExpr::Variable(x, Some(t)) => write!(f, "{x}#{t}"),
            BaseExpr::AnonymousVariable(x, t) => write!(f, "{x}#{t}"),
            BaseExpr::Expr(x) => write!(f, "{x}"),
        }
    }
}

impl<T: Display + LambdaLanguageOfThought> Display for PrintingAST<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PrintingAST::Application {
                head: Some(head),
                children,
            } if head.infix() => write!(
                f,
                "{}",
                children
                    .iter()
                    .map(|x| if x.needs_parens() {
                        format!("({x})")
                    } else {
                        x.to_string()
                    })
                    .join(format!(" {head} ").as_str())
            ),
            PrintingAST::Application {
                head: Some(head),
                children,
            } => write!(
                f,
                "{head}({})",
                children.iter().map(|x| x.to_string()).join(", ")
            ),
            PrintingAST::Application {
                head: None,
                children,
            } => {
                write!(
                    f,
                    "({})({})",
                    children.first().unwrap(),
                    children[1..].iter().map(|x| x.to_string()).join(", ")
                )
            }
            PrintingAST::Lambda { var, typ, body } => write!(f, "lambda {typ} {var} {body}"),
            PrintingAST::Binder {
                expr,
                var_name,
                children,
                ..
            } => write!(
                f,
                "{expr}({var_name}, {})",
                children.iter().map(|x| x.to_string()).join(", ")
            ),
            PrintingAST::Expr(x) => write!(f, "{x}"),
        }
    }
}

#[derive(Serialize)]
enum PrintingAST<T> {
    Application {
        head: Option<BaseExpr<T>>,
        #[serde(skip_serializing_if = "Vec::is_empty")]
        children: Vec<PrintingAST<T>>,
    },
    Lambda {
        var: String,
        typ: LambdaType,
        body: Box<PrintingAST<T>>,
    },
    Binder {
        expr: T,
        var_name: String,
        var_type: LambdaType,
        #[serde(skip_serializing_if = "Vec::is_empty")]
        children: Vec<PrintingAST<T>>,
    },
    #[serde(untagged)]
    Expr(BaseExpr<T>),
}
impl<T> PrintingAST<T>
where
    T: LambdaLanguageOfThought,
{
    fn needs_parens(&self) -> bool {
        match self {
            PrintingAST::Application {
                head: Some(head),
                children,
            } if head.infix() && children.len() >= 2 => true,
            PrintingAST::Application { .. } => false,
            PrintingAST::Lambda { .. } => true,
            PrintingAST::Binder { .. } => false,
            PrintingAST::Expr(_) => false,
        }
    }
}
impl<T> PrintingAST<T>
where
    T: Clone,
{
    fn token(&self) -> Option<BaseExpr<T>> {
        match self {
            PrintingAST::Application { head, .. } => head.clone(),
            PrintingAST::Expr(head) => Some(head.clone()),
            PrintingAST::Binder { expr, .. } => Some(BaseExpr::Expr(expr.clone())),
            PrintingAST::Lambda { .. } => None,
        }
    }

    fn children(self) -> Vec<PrintingAST<T>> {
        match self {
            PrintingAST::Application { children, .. } | PrintingAST::Binder { children, .. } => {
                children
            }
            PrintingAST::Lambda { body, .. } => vec![*body],
            PrintingAST::Expr(_) => vec![],
        }
    }

    fn steal_children(self, other: Self) -> Self {
        match self {
            PrintingAST::Application { head, mut children } => {
                children.extend(other.children());
                PrintingAST::Application { head, children }
            }
            PrintingAST::Expr(head) => PrintingAST::Application {
                head: Some(head),
                children: other.children(),
            },
            PrintingAST::Binder {
                expr,
                var_name,
                var_type,
                mut children,
            } => {
                children.extend(other.children());
                PrintingAST::Binder {
                    expr,
                    var_name,
                    var_type,
                    children,
                }
            }
            PrintingAST::Lambda { .. } => panic!("No way to add new children to a lambda"),
        }
    }

    fn add_child(self, child: Self) -> Self {
        match self {
            PrintingAST::Application { head, mut children } => {
                children.push(child);
                PrintingAST::Application { head, children }
            }
            PrintingAST::Binder {
                expr,
                var_name,
                var_type,
                mut children,
            } => {
                children.push(child);
                PrintingAST::Binder {
                    expr,
                    var_name,
                    var_type,
                    children,
                }
            }
            PrintingAST::Expr(head) => PrintingAST::Application {
                head: Some(head),
                children: vec![child],
            },
            l @ PrintingAST::Lambda { .. } => PrintingAST::Application {
                head: None,
                children: vec![l, child],
            },
        }
    }
}

impl<'src, T> RootedLambdaPool<'src, T>
where
    T: Clone + LambdaLanguageOfThought + PartialEq,
{
    fn tokens(&self, expr: LambdaExprRef, c: VarContext) -> PrintingAST<T> {
        match self.get(expr) {
            LambdaExpr::Lambda(child, lambda_type) => {
                let (c, var) = c.inc_depth(lambda_type);
                PrintingAST::Lambda {
                    var,
                    typ: lambda_type.clone(),
                    body: Box::new(self.tokens(*child, c)),
                }
            }
            LambdaExpr::BoundVariable(bvar, _) => {
                PrintingAST::Expr(BaseExpr::Variable(c.lambda_var(*bvar), None))
            }

            LambdaExpr::FreeVariable(FreeVar::Named(s), t) => {
                PrintingAST::Expr(BaseExpr::Variable(s.to_string(), Some(t.clone())))
            }
            LambdaExpr::FreeVariable(FreeVar::Anonymous(n), t) => {
                PrintingAST::Expr(BaseExpr::AnonymousVariable(*n, t.clone()))
            }

            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                let f = self.tokens(*subformula, c.clone());
                let arg = self.tokens(*argument, c.clone());
                match (f.token(), arg.token()) {
                    (Some(BaseExpr::Expr(x)), Some(BaseExpr::Expr(y))) => {
                        if x.commutative() && x.associative() && x == y {
                            f.steal_children(arg)
                        } else {
                            f.add_child(arg)
                        }
                    }
                    (_, _) => f.add_child(arg),
                }
            }
            LambdaExpr::LanguageOfThoughtExpr(x, super::ExprType::NoVar) => {
                PrintingAST::Expr(BaseExpr::Expr(x.clone()))
            }
            LambdaExpr::LanguageOfThoughtExpr(x, ExprType::BindVar(body)) => {
                let (c, var_string) = c.inc_depth(x.var_type().expect(
                    "Implementation error, if you bind a var, the expression must bind vars!",
                ));

                PrintingAST::Binder {
                    expr: x.clone(),
                    var_name: var_string,
                    var_type: x.var_type().unwrap().clone(),
                    children: vec![self.tokens(*body, c)],
                }
            }
            LambdaExpr::LanguageOfThoughtExpr(x, ExprType::BindVarTwoBodies(l, r)) => {
                let (c, var_string) = c.inc_depth(x.var_type().expect(
                    "Implementation error, if you bind a var, the expression must bind vars!",
                ));
                PrintingAST::Binder {
                    expr: x.clone(),
                    var_name: var_string,
                    var_type: x.var_type().unwrap().clone(),
                    children: vec![self.tokens(*l, c.clone()), self.tokens(*r, c)],
                }
            }
        }
    }
}

///A special kind of `RootedLambdaPool` that should be used to display in fancy math modes, e.g. with
///Typst or (potentially) LaTeX.
pub struct MathModeExpression<T>(PrintingAST<T>);

impl<'src, T: ParseLot<'src> + LambdaLanguageOfThought + 'src + PartialEq> RootedLambdaPool<'src, T>
where
    T: ParseLot<'src> + Clone + LambdaLanguageOfThought + PartialEq,
    T::Token: Clone,
{
    ///Get a [`MathModeExpression`] to be serialized for documents.
    #[must_use]
    pub fn for_document(&self) -> MathModeExpression<T> {
        MathModeExpression(self.tokens(self.root, VarContext::default()))
    }
}

impl<T> Serialize for MathModeExpression<T>
where
    T: Serialize,
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
                "~(AgentOf(a_John, e_0))",
                "{\"Application\":{\"head\":{\"Expr\":\"Not\"},\"children\":[{\"Application\":{\"head\":{\"Expr\":\"AgentOf\"},\"children\":[{\"Expr\":{\"Actor\":\"John\"}},{\"Expr\":{\"Event\":0}}]}}]}}",
            ),
            (
                "pa_Red(a_John) & ~(pa_Red(a_Mary))",
                "{\"Application\":{\"head\":{\"Expr\":\"And\"},\"children\":[{\"Application\":{\"head\":{\"Expr\":{\"Property\":[\"Red\",\"Actor\"]}},\"children\":[{\"Expr\":{\"Actor\":\"John\"}}]}},{\"Application\":{\"head\":{\"Expr\":\"Not\"},\"children\":[{\"Application\":{\"head\":{\"Expr\":{\"Property\":[\"Red\",\"Actor\"]}},\"children\":[{\"Expr\":{\"Actor\":\"Mary\"}}]}}]}}]}}",
            ),
            (
                "every(x, all_a(x), pa_Blue(x))",
                "{\"Binder\":{\"expr\":{\"Quantifier\":{\"quantifier\":\"Universal\",\"var_type\":\"Actor\"}},\"var_name\":\"x\",\"var_type\":\"a\",\"children\":[{\"Application\":{\"head\":{\"Expr\":\"Everyone\"},\"children\":[{\"Variable\":\"x\"}]}},{\"Application\":{\"head\":{\"Expr\":{\"Property\":[\"Blue\",\"Actor\"]}},\"children\":[{\"Variable\":\"x\"}]}}]}}",
            ),
            (
                "every(x, pa_Blue(x), pa_Blue(x))",
                "{\"Binder\":{\"expr\":{\"Quantifier\":{\"quantifier\":\"Universal\",\"var_type\":\"Actor\"}},\"var_name\":\"x\",\"var_type\":\"a\",\"children\":[{\"Application\":{\"head\":{\"Expr\":{\"Property\":[\"Blue\",\"Actor\"]}},\"children\":[{\"Variable\":\"x\"}]}},{\"Application\":{\"head\":{\"Expr\":{\"Property\":[\"Blue\",\"Actor\"]}},\"children\":[{\"Variable\":\"x\"}]}}]}}",
            ),
            (
                "every(x, pa_5(x), pa_10(a_59))",
                "{\"Binder\":{\"expr\":{\"Quantifier\":{\"quantifier\":\"Universal\",\"var_type\":\"Actor\"}},\"var_name\":\"x\",\"var_type\":\"a\",\"children\":[{\"Application\":{\"head\":{\"Expr\":{\"Property\":[\"5\",\"Actor\"]}},\"children\":[{\"Variable\":\"x\"}]}},{\"Application\":{\"head\":{\"Expr\":{\"Property\":[\"10\",\"Actor\"]}},\"children\":[{\"Expr\":{\"Actor\":\"59\"}}]}}]}}",
            ),
            (
                "every_e(x, all_e(x), PatientOf(a_Mary, x))",
                "{\"Binder\":{\"expr\":{\"Quantifier\":{\"quantifier\":\"Universal\",\"var_type\":\"Event\"}},\"var_name\":\"x\",\"var_type\":\"e\",\"children\":[{\"Application\":{\"head\":{\"Expr\":\"EveryEvent\"},\"children\":[{\"Variable\":\"x\"}]}},{\"Application\":{\"head\":{\"Expr\":\"PatientOf\"},\"children\":[{\"Expr\":{\"Actor\":\"Mary\"}},{\"Variable\":\"x\"}]}}]}}",
            ),
            (
                "cool#<a,t>(a_John)",
                "{\"Application\":{\"head\":{\"Variable\":\"cool\"},\"children\":[{\"Expr\":{\"Actor\":\"John\"}}]}}",
            ),
            (
                "bad#<a,t>(man#a)",
                "{\"Application\":{\"head\":{\"Variable\":\"bad\"},\"children\":[{\"Variable\":\"man\"}]}}",
            ),
            (
                "loves#<a,<a,t>>(a_mary, a_john)",
                "{\"Application\":{\"head\":{\"Variable\":\"loves\"},\"children\":[{\"Expr\":{\"Actor\":\"mary\"}},{\"Expr\":{\"Actor\":\"john\"}}]}}",
            ),
            (
                "True | (True & False)",
                "{\"Application\":{\"head\":{\"Expr\":\"Or\"},\"children\":[{\"Expr\":\"Tautology\"},{\"Application\":{\"head\":{\"Expr\":\"And\"},\"children\":[{\"Expr\":\"Tautology\"},{\"Expr\":\"Contradiction\"}]}}]}}",
            ),
            (
                "(True | True) & False",
                "{\"Application\":{\"head\":{\"Expr\":\"And\"},\"children\":[{\"Application\":{\"head\":{\"Expr\":\"Or\"},\"children\":[{\"Expr\":\"Tautology\"},{\"Expr\":\"Tautology\"}]}},{\"Expr\":\"Contradiction\"}]}}",
            ),
            (
                "lambda a x lambda a y likes#<a,<a,t>>(x, y)",
                "{\"Lambda\":{\"var\":\"x\",\"typ\":\"a\",\"body\":{\"Lambda\":{\"var\":\"y\",\"typ\":\"a\",\"body\":{\"Application\":{\"head\":{\"Variable\":\"likes\"},\"children\":[{\"Variable\":\"x\"},{\"Variable\":\"y\"}]}}}}}}",
            ),
            (
                "lambda <a,t> P iota(x, P(x))",
                "{\"Lambda\":{\"var\":\"P\",\"typ\":\"<a,t>\",\"body\":{\"Binder\":{\"expr\":{\"Iota\":\"Actor\"},\"var_name\":\"x\",\"var_type\":\"a\",\"children\":[{\"Application\":{\"head\":{\"Variable\":\"P\"},\"children\":[{\"Variable\":\"x\"}]}}]}}}}",
            ),
        ] {
            let expression = RootedLambdaPool::<Expr>::parse(statement)?;
            let doc = expression.for_document();
            assert_eq!(doc.0.to_string(), statement);
            assert_eq!(json, serde_json::to_string(&doc)?);
        }

        Ok(())
    }
}
