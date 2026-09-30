use std::fmt::{Debug, Display};

use itertools::{Either, Itertools};
use serde::{Deserialize, Serialize};

use crate::lambda::interpretation::Neutral;
use crate::lambda::parser::ParseLot;
use crate::lambda::types::LambdaType;
use crate::lambda::{ExprType, FreeVar, Literal, Value};
use crate::lambda::{LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, RootedLambdaPool};

use crate::lambda::printing::VarContext;

impl<'src, T: Display + LambdaLanguageOfThought + ParseLot<'src> + PartialEq + Clone + Debug>
    Serialize for RootedLambdaPool<'src, T>
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(super) enum BaseExpr<'src, T> {
    Variable(String, LambdaType),
    FreeVariable(String, LambdaType),
    AnonymousVariable(usize, LambdaType),
    Literal(Literal<'src>),
    Expr(T),
}

impl<T: LambdaLanguageOfThought> BaseExpr<'_, T> {
    fn infix(&self) -> bool {
        if let BaseExpr::Expr(x) = self {
            x.infix()
        } else {
            false
        }
    }

    fn unary_associative(&self) -> bool {
        if let BaseExpr::Expr(x) = self {
            x.unary_associative()
        } else {
            false
        }
    }
}

impl<T: Display> Display for BaseExpr<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BaseExpr::Variable(x, _) => write!(f, "{x}"),
            BaseExpr::FreeVariable(x, t) => write!(f, "{x}#{t}"),
            BaseExpr::AnonymousVariable(x, t) => write!(f, "{x}#{t}"),
            BaseExpr::Expr(x) => write!(f, "{x}"),
            BaseExpr::Literal(x) => write!(f, "{x}"),
        }
    }
}

impl<T: Display + LambdaLanguageOfThought + Debug> Display for PrintingAST<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PrintingAST::Application {
                head: ApplicationHead::Infix(head, needs_parens),
                children,
            } => {
                if children.len() < 2 {
                    write!(
                        f,
                        "{head}({})",
                        children.iter().map(|x| x.to_string()).join("")
                    )
                } else {
                    write!(
                        f,
                        "{}",
                        children
                            .iter()
                            .zip(needs_parens)
                            .map(|(x, needs_parens)| if *needs_parens {
                                format!("({x})")
                            } else {
                                x.to_string()
                            })
                            .join(format!(" {head} ").as_str())
                    )
                }
            }
            PrintingAST::Application {
                head: ApplicationHead::Prefix(head, needs_parens),
                children,
                ..
            } => {
                write!(
                    f,
                    "{}{}",
                    head,
                    if *needs_parens {
                        format!("({})", children[0])
                    } else {
                        children[0].to_string()
                    }
                )
            }

            PrintingAST::Application {
                head: ApplicationHead::Normal(head),
                children,
                ..
            } => write!(
                f,
                "{head}({})",
                children
                    .iter()
                    .map(std::string::ToString::to_string)
                    .join(", ")
            ),
            PrintingAST::Application {
                head: ApplicationHead::ComplexFunc(head),
                children,
                ..
            } => {
                write!(
                    f,
                    "({head})({})",
                    children
                        .iter()
                        .map(std::string::ToString::to_string)
                        .join(", ")
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
                children
                    .iter()
                    .map(std::string::ToString::to_string)
                    .join(", ")
            ),
            PrintingAST::Expr(x) => write!(f, "{x}"),
        }
    }
}

#[derive(Serialize, Clone, Debug)]
pub(super) enum ApplicationHead<'src, T> {
    Infix(BaseExpr<'src, T>, Vec<bool>),
    Prefix(BaseExpr<'src, T>, bool),
    Normal(BaseExpr<'src, T>),
    ComplexFunc(Box<PrintingAST<'src, T>>),
}

#[derive(Serialize, Clone, Debug)]
pub(super) enum PrintingAST<'src, T> {
    Application {
        head: ApplicationHead<'src, T>,
        #[serde(skip_serializing_if = "Vec::is_empty")]
        children: Vec<PrintingAST<'src, T>>,
    },
    Lambda {
        var: String,
        typ: LambdaType,
        body: Box<PrintingAST<'src, T>>,
    },
    Binder {
        expr: T,
        var_name: String,
        var_type: LambdaType,
        #[serde(skip_serializing_if = "Vec::is_empty")]
        children: Vec<PrintingAST<'src, T>>,
    },
    #[serde(untagged)]
    Expr(BaseExpr<'src, T>),
}
impl<T> PrintingAST<'_, T>
where
    T: LambdaLanguageOfThought,
{
    fn needs_parens(&self) -> bool {
        match self {
            PrintingAST::Application {
                head: ApplicationHead::Infix(head, _),
                children,
                ..
            } if children.len() >= 2 => true,
            PrintingAST::Lambda { .. } => true,
            PrintingAST::Application { .. } | PrintingAST::Binder { .. } | PrintingAST::Expr(_) => {
                false
            }
        }
    }
}
impl<'src, T: PartialEq + Debug + LambdaLanguageOfThought> PrintingAST<'src, T> {
    fn apply(self, other: Self, under_app: bool) -> Self {
        match (self, other) {
            (
                PrintingAST::Application {
                    head: ApplicationHead::Infix(x, x_parens),
                    children: x_children,
                },
                PrintingAST::Application {
                    head: ApplicationHead::Infix(y, y_parens),
                    children: y_children,
                },
            ) if x == y => PrintingAST::Application {
                head: ApplicationHead::Infix(x, x_parens.into_iter().chain(y_parens).collect()),
                children: x_children.into_iter().chain(y_children).collect(),
            },
            (
                PrintingAST::Application {
                    head: ApplicationHead::Infix(x, mut parens),
                    mut children,
                },
                y,
            ) => {
                parens.push(y.needs_parens() && y.head().is_none_or(|y| y != &x));
                children.push(y);
                PrintingAST::Application {
                    head: ApplicationHead::Infix(x, parens),
                    children,
                }
            }

            (PrintingAST::Expr(expr), r)
                if matches!(
                    &r,
                    PrintingAST::Application {
                        head: ApplicationHead::Infix(x, ..),
                        ..
                    } if &expr == x
                ) && under_app =>
            {
                //This is when we're applying a And to and And, (or Or to Or), so we can just flatten
                //it, but only if we know another And is coming!
                r
            }

            (
                x @ (PrintingAST::Application {
                    head: ApplicationHead::Prefix(..),
                    ..
                }
                | PrintingAST::Lambda { .. }),
                y,
            ) => PrintingAST::Application {
                head: ApplicationHead::ComplexFunc(Box::new(x)),
                children: vec![y],
            },
            (
                PrintingAST::Application {
                    head: head @ (ApplicationHead::Normal(_) | ApplicationHead::ComplexFunc(_)),
                    mut children,
                },
                y,
            ) => {
                children.push(y);
                PrintingAST::Application { head, children }
            }

            (PrintingAST::Expr(expr), y) => PrintingAST::Application {
                head: if expr.infix() && under_app {
                    let parens = vec![y.needs_parens() && y.head().is_none_or(|x| x != &expr)];
                    ApplicationHead::Infix(expr, parens)
                } else if expr.unary_associative() {
                    ApplicationHead::Prefix(expr, y.needs_parens())
                } else {
                    ApplicationHead::Normal(expr)
                },
                children: vec![y],
            },
            (x, y) => todo!("A:\t{x:#?}\nB:\t{y:#?}"),
        }
    }

    fn head(&self) -> Option<&BaseExpr<'src, T>> {
        match self {
            PrintingAST::Application {
                head:
                    ApplicationHead::Prefix(head, _)
                    | ApplicationHead::Infix(head, _)
                    | ApplicationHead::Normal(head),
                ..
            } => Some(head),
            _ => None,
        }
    }
}

impl<'src, T> RootedLambdaPool<'src, T>
where
    T: LambdaLanguageOfThought + PartialEq + Clone + Debug,
{
    pub(super) fn tokens(&self, expr: LambdaExprRef, c: VarContext) -> PrintingAST<'src, T> {
        self.tokens_inner(expr, c, false)
    }
    fn tokens_inner(
        &self,
        expr: LambdaExprRef,
        c: VarContext,
        under_app: bool,
    ) -> PrintingAST<'src, T> {
        match self.get(expr) {
            LambdaExpr::Lambda(child, lambda_type) => {
                let (c, var) = c.inc_depth(lambda_type);
                PrintingAST::Lambda {
                    var,
                    typ: lambda_type.clone(),
                    body: Box::new(self.tokens_inner(*child, c, false)),
                }
            }
            LambdaExpr::BoundVariable(bvar, t) => {
                PrintingAST::Expr(BaseExpr::Variable(c.lambda_var(*bvar), t.clone()))
            }

            LambdaExpr::FreeVariable(FreeVar::Named(s), t) => {
                PrintingAST::Expr(BaseExpr::FreeVariable(s.to_string(), t.clone()))
            }
            LambdaExpr::FreeVariable(FreeVar::Anonymous(n), t) => {
                PrintingAST::Expr(BaseExpr::AnonymousVariable(*n, t.clone()))
            }

            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                let f = self.tokens_inner(*subformula, c.clone(), true);
                let arg = self.tokens_inner(*argument, c.clone(), true);
                f.apply(arg, under_app)
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
                    children: vec![self.tokens_inner(*body, c, false)],
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
                    children: vec![
                        self.tokens_inner(*l, c.clone(), false),
                        self.tokens_inner(*r, c, false),
                    ],
                }
            }
        }
    }
}

impl<'src, T> Value<'src, '_, T>
where
    T: LambdaLanguageOfThought + PartialEq + Clone + Debug,
{
    pub(super) fn tokens(&self, c: VarContext) -> PrintingAST<'src, T> {
        match self {
            Value::Base(literal) => PrintingAST::Expr(BaseExpr::Literal(literal.clone())),
            Value::Function(body, lambda_type, _) => {
                let (c, var) = c.inc_depth(lambda_type);
                PrintingAST::Lambda {
                    var,
                    typ: (*lambda_type).clone(),
                    body: Box::new(body.tokens(c)),
                }
            }
            Value::Neutral(x) => x.tokens(c),
            Value::Primitive { expr, args } => {
                let children = if expr.commutative() && expr.associative() {
                    args.iter()
                        .flat_map(|x| match x {
                            Value::Primitive {
                                expr: child_expr,
                                args,
                            }
                            | Value::Neutral(Neutral::Primitive {
                                expr: child_expr,
                                args,
                            }) if child_expr == expr => Either::Right(args.iter()),
                            v => Either::Left(std::iter::once(v)),
                        })
                        .map(|x| x.tokens(c.clone()))
                        .collect::<Vec<_>>()
                } else {
                    args.iter().map(|x| x.tokens(c.clone())).collect()
                };

                PrintingAST::Application {
                    head: if expr.infix() && children.len() >= 2 {
                        ApplicationHead::Infix(
                            BaseExpr::Expr(expr.clone()),
                            children.iter().map(|x| x.needs_parens()).collect(),
                        )
                    } else if expr.unary_associative() && !children.is_empty() {
                        ApplicationHead::Prefix(
                            BaseExpr::Expr(expr.clone()),
                            children.iter().any(|x| x.needs_parens()),
                        )
                    } else {
                        ApplicationHead::Normal(BaseExpr::Expr(expr.clone()))
                    },
                    children,
                }
            }
        }
    }
}

impl<'src, T> Neutral<'src, '_, T>
where
    T: LambdaLanguageOfThought + PartialEq + Clone + Debug,
{
    pub(super) fn tokens(&self, c: VarContext) -> PrintingAST<'src, T> {
        let (f, arg) = match self {
            Neutral::FreeVar(FreeVar::Anonymous(x), lambda_type) => {
                return PrintingAST::Expr(BaseExpr::AnonymousVariable(*x, (*lambda_type).clone()));
            }
            Neutral::FreeVar(FreeVar::Named(x), lambda_type) => {
                return PrintingAST::Expr(BaseExpr::Variable(
                    x.to_string(),
                    (*lambda_type).clone(),
                ));
            }
            Neutral::BoundVar(d, t) => {
                return PrintingAST::Expr(BaseExpr::Variable(
                    c.lambda_var_by_level(*d),
                    (*t).clone(),
                ));
            }
            Neutral::Primitive { expr, args } => {
                let children = if expr.commutative() && expr.associative() {
                    args.iter()
                        .flat_map(|x| match x {
                            Value::Primitive {
                                expr: child_expr,
                                args,
                            }
                            | Value::Neutral(Neutral::Primitive {
                                expr: child_expr,
                                args,
                            }) if child_expr == expr => Either::Right(args.iter()),
                            v => Either::Left(std::iter::once(v)),
                        })
                        .map(|x| x.tokens(c.clone()))
                        .collect::<Vec<_>>()
                } else {
                    args.iter().map(|x| x.tokens(c.clone())).collect()
                };
                return PrintingAST::Application {
                    head: if expr.infix() && children.len() >= 2 {
                        ApplicationHead::Infix(
                            BaseExpr::Expr(expr.clone()),
                            children.iter().map(|x| x.needs_parens()).collect(),
                        )
                    } else if expr.unary_associative() && !children.is_empty() {
                        ApplicationHead::Prefix(
                            BaseExpr::Expr(expr.clone()),
                            children.iter().any(|x| x.needs_parens()),
                        )
                    } else {
                        ApplicationHead::Normal(BaseExpr::Expr(expr.clone()))
                    },
                    children,
                };
            }
            Neutral::AppBoth(head, arg) => (head.tokens(c.clone()), arg.tokens(c)),
            Neutral::AppHead(head, arg) => (head.tokens(c.clone()), arg.tokens(c)),
            Neutral::AppArg(head, arg) => (head.tokens(c.clone()), arg.tokens(c)),
        };
        f.apply(arg, false)
    }
}

///A way of exporting [`RootedLambdaPool`], [`Value`], or [`Neutral`] that can be used to display in fancy math modes, e.g. with
///Typst or (potentially) LaTeX. It's a nicer way of serializing them for fancy printing.
pub struct MathModeExpression<'src, T>(PrintingAST<'src, T>);

impl<'src, T: ParseLot<'src> + LambdaLanguageOfThought + 'src + PartialEq> RootedLambdaPool<'src, T>
where
    T: ParseLot<'src> + Clone + LambdaLanguageOfThought + PartialEq + Debug,
    T::Token: Clone,
{
    ///Get a [`MathModeExpression`] to be serialized for documents.
    #[must_use]
    pub fn for_document(&self) -> MathModeExpression<'src, T> {
        MathModeExpression(self.tokens(self.root, VarContext::default()))
    }
}

impl<'src, 'pool, T: ParseLot<'src> + LambdaLanguageOfThought + 'src + PartialEq>
    Value<'src, 'pool, T>
where
    T: ParseLot<'src> + Clone + LambdaLanguageOfThought + PartialEq + Debug,
    T::Token: Clone,
{
    ///Get a [`MathModeExpression`] to be serialized for documents.
    #[must_use]
    pub fn for_document(&self) -> MathModeExpression<'src, T> {
        MathModeExpression(self.tokens(VarContext::default()))
    }
}

impl<'src, 'pool, T: ParseLot<'src> + LambdaLanguageOfThought + 'src + PartialEq>
    Neutral<'src, 'pool, T>
where
    T: ParseLot<'src> + Clone + LambdaLanguageOfThought + PartialEq + Debug,
    T::Token: Clone,
{
    ///Get a [`MathModeExpression`] to be serialized for documents.
    #[must_use]
    pub fn for_document(&self) -> MathModeExpression<'src, T> {
        MathModeExpression(self.tokens(VarContext::default()))
    }
}

impl<T> Serialize for MathModeExpression<'_, T>
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
            ("~", "{\"Expr\":\"Not\"}"),
            (
                "&(x#t)",
                "{\"Application\":{\"head\":{\"Normal\":{\"Expr\":\"And\"}},\"children\":[{\"FreeVariable\":[\"x\",\"t\"]}]}}",
            ),
            (
                "lambda t phi &(phi & phi)",
                "{\"Lambda\":{\"var\":\"phi\",\"typ\":\"t\",\"body\":{\"Application\":{\"head\":{\"Normal\":{\"Expr\":\"And\"}},\"children\":[{\"Application\":{\"head\":{\"Infix\":[{\"Expr\":\"And\"},[false,false]]},\"children\":[{\"Variable\":[\"phi\",\"t\"]},{\"Variable\":[\"phi\",\"t\"]}]}}]}}}}",
            ),
            (
                "True & True & True",
                "{\"Application\":{\"head\":{\"Infix\":[{\"Expr\":\"And\"},[false,false,false]]},\"children\":[{\"Expr\":\"Tautology\"},{\"Expr\":\"Tautology\"},{\"Expr\":\"Tautology\"}]}}",
            ),
            (
                "AgentOf(a_John, e_0) & PatientOf(a_Mary, e_1) & likes#<a,<a,t>>(a_Mary, a_John)",
                "{\"Application\":{\"head\":{\"Infix\":[{\"Expr\":\"And\"},[false,false,false]]},\"children\":[{\"Application\":{\"head\":{\"Normal\":{\"Expr\":\"AgentOf\"}},\"children\":[{\"Expr\":{\"Actor\":\"John\"}},{\"Expr\":{\"Event\":0}}]}},{\"Application\":{\"head\":{\"Normal\":{\"Expr\":\"PatientOf\"}},\"children\":[{\"Expr\":{\"Actor\":\"Mary\"}},{\"Expr\":{\"Event\":1}}]}},{\"Application\":{\"head\":{\"Normal\":{\"FreeVariable\":[\"likes\",\"<a,<a,t>>\"]}},\"children\":[{\"Expr\":{\"Actor\":\"Mary\"}},{\"Expr\":{\"Actor\":\"John\"}}]}}]}}",
            ),
            (
                "~AgentOf(a_John, e_0)",
                "{\"Application\":{\"head\":{\"Prefix\":[{\"Expr\":\"Not\"},false]},\"children\":[{\"Application\":{\"head\":{\"Normal\":{\"Expr\":\"AgentOf\"}},\"children\":[{\"Expr\":{\"Actor\":\"John\"}},{\"Expr\":{\"Event\":0}}]}}]}}",
            ),
            (
                "pa_Red(a_John) & ~pa_Red(a_Mary)",
                "{\"Application\":{\"head\":{\"Infix\":[{\"Expr\":\"And\"},[false,false]]},\"children\":[{\"Application\":{\"head\":{\"Normal\":{\"Expr\":{\"Property\":[\"Red\",\"Actor\"]}}},\"children\":[{\"Expr\":{\"Actor\":\"John\"}}]}},{\"Application\":{\"head\":{\"Prefix\":[{\"Expr\":\"Not\"},false]},\"children\":[{\"Application\":{\"head\":{\"Normal\":{\"Expr\":{\"Property\":[\"Red\",\"Actor\"]}}},\"children\":[{\"Expr\":{\"Actor\":\"Mary\"}}]}}]}}]}}",
            ),
            (
                "every(x, all_a(x), pa_Blue(x))",
                "{\"Binder\":{\"expr\":{\"Quantifier\":{\"quantifier\":\"Universal\",\"var_type\":\"Actor\"}},\"var_name\":\"x\",\"var_type\":\"a\",\"children\":[{\"Application\":{\"head\":{\"Normal\":{\"Expr\":\"Everyone\"}},\"children\":[{\"Variable\":[\"x\",\"a\"]}]}},{\"Application\":{\"head\":{\"Normal\":{\"Expr\":{\"Property\":[\"Blue\",\"Actor\"]}}},\"children\":[{\"Variable\":[\"x\",\"a\"]}]}}]}}",
            ),
            (
                "every(x, pa_Blue(x), pa_Blue(x))",
                "{\"Binder\":{\"expr\":{\"Quantifier\":{\"quantifier\":\"Universal\",\"var_type\":\"Actor\"}},\"var_name\":\"x\",\"var_type\":\"a\",\"children\":[{\"Application\":{\"head\":{\"Normal\":{\"Expr\":{\"Property\":[\"Blue\",\"Actor\"]}}},\"children\":[{\"Variable\":[\"x\",\"a\"]}]}},{\"Application\":{\"head\":{\"Normal\":{\"Expr\":{\"Property\":[\"Blue\",\"Actor\"]}}},\"children\":[{\"Variable\":[\"x\",\"a\"]}]}}]}}",
            ),
            (
                "every(x, pa_5(x), pa_10(a_59))",
                "{\"Binder\":{\"expr\":{\"Quantifier\":{\"quantifier\":\"Universal\",\"var_type\":\"Actor\"}},\"var_name\":\"x\",\"var_type\":\"a\",\"children\":[{\"Application\":{\"head\":{\"Normal\":{\"Expr\":{\"Property\":[\"5\",\"Actor\"]}}},\"children\":[{\"Variable\":[\"x\",\"a\"]}]}},{\"Application\":{\"head\":{\"Normal\":{\"Expr\":{\"Property\":[\"10\",\"Actor\"]}}},\"children\":[{\"Expr\":{\"Actor\":\"59\"}}]}}]}}",
            ),
            (
                "every_e(x, all_e(x), PatientOf(a_Mary, x))",
                "{\"Binder\":{\"expr\":{\"Quantifier\":{\"quantifier\":\"Universal\",\"var_type\":\"Event\"}},\"var_name\":\"x\",\"var_type\":\"e\",\"children\":[{\"Application\":{\"head\":{\"Normal\":{\"Expr\":\"EveryEvent\"}},\"children\":[{\"Variable\":[\"x\",\"e\"]}]}},{\"Application\":{\"head\":{\"Normal\":{\"Expr\":\"PatientOf\"}},\"children\":[{\"Expr\":{\"Actor\":\"Mary\"}},{\"Variable\":[\"x\",\"e\"]}]}}]}}",
            ),
            (
                "cool#<a,t>(a_John)",
                "{\"Application\":{\"head\":{\"Normal\":{\"FreeVariable\":[\"cool\",\"<a,t>\"]}},\"children\":[{\"Expr\":{\"Actor\":\"John\"}}]}}",
            ),
            (
                "bad#<a,t>(man#a)",
                "{\"Application\":{\"head\":{\"Normal\":{\"FreeVariable\":[\"bad\",\"<a,t>\"]}},\"children\":[{\"FreeVariable\":[\"man\",\"a\"]}]}}",
            ),
            (
                "loves#<a,<a,t>>(a_mary, a_john)",
                "{\"Application\":{\"head\":{\"Normal\":{\"FreeVariable\":[\"loves\",\"<a,<a,t>>\"]}},\"children\":[{\"Expr\":{\"Actor\":\"mary\"}},{\"Expr\":{\"Actor\":\"john\"}}]}}",
            ),
            (
                "True | (True & False)",
                "{\"Application\":{\"head\":{\"Infix\":[{\"Expr\":\"Or\"},[false,true]]},\"children\":[{\"Expr\":\"Tautology\"},{\"Application\":{\"head\":{\"Infix\":[{\"Expr\":\"And\"},[false,false]]},\"children\":[{\"Expr\":\"Tautology\"},{\"Expr\":\"Contradiction\"}]}}]}}",
            ),
            (
                "(True | True) & False",
                "{\"Application\":{\"head\":{\"Infix\":[{\"Expr\":\"And\"},[true,false]]},\"children\":[{\"Application\":{\"head\":{\"Infix\":[{\"Expr\":\"Or\"},[false,false]]},\"children\":[{\"Expr\":\"Tautology\"},{\"Expr\":\"Tautology\"}]}},{\"Expr\":\"Contradiction\"}]}}",
            ),
            (
                "lambda a x lambda a y likes#<a,<a,t>>(x, y)",
                "{\"Lambda\":{\"var\":\"x\",\"typ\":\"a\",\"body\":{\"Lambda\":{\"var\":\"y\",\"typ\":\"a\",\"body\":{\"Application\":{\"head\":{\"Normal\":{\"FreeVariable\":[\"likes\",\"<a,<a,t>>\"]}},\"children\":[{\"Variable\":[\"x\",\"a\"]},{\"Variable\":[\"y\",\"a\"]}]}}}}}}",
            ),
            (
                "lambda <a,t> P iota(x, P(x))",
                "{\"Lambda\":{\"var\":\"P\",\"typ\":\"<a,t>\",\"body\":{\"Binder\":{\"expr\":{\"Iota\":\"Actor\"},\"var_name\":\"x\",\"var_type\":\"a\",\"children\":[{\"Application\":{\"head\":{\"Normal\":{\"Variable\":[\"P\",\"<a,t>\"]}},\"children\":[{\"Variable\":[\"x\",\"a\"]}]}}]}}}}",
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
