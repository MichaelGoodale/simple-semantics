use std::fmt::{Debug, Display};

use ahash::HashMap;
use serde::{Deserialize, Serialize};

use crate::{
    lambda::{
        ExprType, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, RootedLambdaPool,
        parser::ParseLot, types::LambdaType,
    },
    language::ActorOrEvent,
};

static VARIABLENAMES: [&str; 26] = [
    "x", "y", "z", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p",
    "q", "r", "s", "t", "u", "v", "w",
];

static TRUTHS: [&str; 2] = ["phi", "psi"];

static PREDICATENAMES: [&str; 3] = ["P", "Q", "R"];

static OTHERFUNCTIONS: [&str; 4] = ["M", "N", "G", "K"];

pub fn to_var(x: usize, t: Option<&LambdaType>) -> String {
    let var_names = match t {
        Some(t) if t == LambdaType::t() => TRUTHS.as_slice(),
        Some(t) if t.is_one_place_function() => PREDICATENAMES.as_slice(),
        Some(t) if t.is_function() => OTHERFUNCTIONS.as_slice(),
        _ => VARIABLENAMES.as_slice(),
    };

    if x < var_names.len() {
        var_names[x].to_string()
    } else {
        format!("{}{}", var_names[x % var_names.len()], x / var_names.len())
    }
}

impl<'src, T: Display + LambdaLanguageOfThought + ParseLot<'src>> Serialize
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

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub(super) struct VarContext {
    vars: HashMap<usize, usize>,
    predicates: HashMap<usize, usize>,
    other_functions: HashMap<usize, usize>,
    truths: HashMap<usize, usize>,
    depth: usize,
}

impl VarContext {
    fn get_map(&self, t: Option<&LambdaType>) -> &HashMap<usize, usize> {
        match t {
            Some(t) if t == LambdaType::t() => &self.truths,
            Some(t) if t.is_one_place_function() => &self.predicates,
            Some(t) if t.is_function() => &self.other_functions,
            _ => &self.vars,
        }
    }
    fn get_map_mut(&mut self, t: Option<&LambdaType>) -> &mut HashMap<usize, usize> {
        match t {
            Some(t) if t == LambdaType::t() => &mut self.truths,
            Some(t) if t.is_one_place_function() => &mut self.predicates,
            Some(t) if t.is_function() => &mut self.other_functions,
            _ => &mut self.vars,
        }
    }

    pub(super) fn inc_depth_q(self, t: ActorOrEvent) -> (Self, String) {
        let t: LambdaType = t.into();
        self.inc_depth(&t)
    }

    pub(super) fn inc_depth(mut self, t: &LambdaType) -> (Self, String) {
        let d = self.depth;
        let map = self.get_map_mut(Some(t));
        let n_var = map.len();
        map.insert(d, n_var);
        self.depth += 1;
        (self, to_var(n_var, Some(t)))
    }

    pub(super) fn lambda_var(&self, bvar: usize, t: &LambdaType) -> String {
        to_var(
            *self.get_map(Some(t)).get(&(self.depth - bvar - 1)).unwrap(),
            Some(t),
        )
    }
}

impl<'a, T: LambdaLanguageOfThought + Display> std::fmt::Display for RootedLambdaPool<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (string, _) = self.string(self.root(), VarContext::default(), false);
        write!(f, "{string}")
    }
}

enum AssociativityData<'a, T> {
    Lambda,
    Var,
    App,
    Associative(&'a T),
}

pub(super) fn add_parenthesis_for_bin_op<'a, T: LambdaLanguageOfThought + PartialEq>(
    x: &'a T,
    data: AssociativityData<'a, T>,
) -> bool {
    match data {
        AssociativityData::Associative(b) if b == x => true,
        AssociativityData::Lambda => true,
        _ => false,
    }
}

impl<'src, T: LambdaLanguageOfThought + Display> RootedLambdaPool<'src, T> {
    #[allow(clippy::too_many_lines)]
    fn string<'a>(
        &'a self,
        expr: LambdaExprRef,
        c: VarContext,
        parent_is_app: bool,
    ) -> (String, AssociativityData<'a, T>) {
        match self.get(expr) {
            LambdaExpr::Lambda(child, lambda_type) => {
                let (c, var) = c.inc_depth(lambda_type);
                (
                    format!(
                        "lambda {} {} {}",
                        lambda_type,
                        var,
                        self.string(*child, c, false).0
                    ),
                    AssociativityData::Lambda,
                )
            }
            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                let (sub, associative) = self.string(*subformula, c.clone(), true);
                let (arg, _) = self.string(*argument, c, false); // false
                // since apps only collapse if they're a left chain

                let mut s = match associative {
                    AssociativityData::Lambda | AssociativityData::Associative(_) => {
                        format!("({sub})({arg}")
                    }
                    AssociativityData::Var => format!("{sub}({arg}"),
                    AssociativityData::App => format!("{sub}{arg}"),
                };

                if parent_is_app {
                    s.push_str(", ");
                } else {
                    s.push(')');
                }

                (s, AssociativityData::App)
            }
            LambdaExpr::BoundVariable(bvar, lambda_type) => {
                (c.lambda_var(*bvar, lambda_type), AssociativityData::Var)
            }
            LambdaExpr::FreeVariable(fvar, t) => (format!("{fvar}#{t}"), AssociativityData::Var),
            LambdaExpr::LanguageOfThoughtExpr(x, ExprType::NoVar) => (
                format!("{x}"),
                if x.commutative() & x.infix() {
                    AssociativityData::Associative(x)
                } else {
                    AssociativityData::Var
                },
            ),
            LambdaExpr::LanguageOfThoughtExpr(
                x,
                ExprType::BindVar(_) | ExprType::BindVarTwoBodies(..),
            ) => {
                todo!()
            } /*match x {
              Expr::Variable(variable) => (
                  c.lambda_var(variable.id() as usize, variable.as_lambda_type()),
                  AssociativityData::Monop,
              ),
              Expr::Quantifier {
                  quantifier,
                  var_type,
                  restrictor,
                  subformula,
              } => {
                  let (c, var_string) = c.inc_depth_q(*var_type);
                  let (restrictor, _) =
                      self.string(LambdaExprRef(restrictor.0), c.clone(), false);
                  let (subformula, _) = self.string(LambdaExprRef(subformula.0), c, false);
                  (
                      format!(
                          "{}{}({}, {restrictor}, {subformula})",
                          quantifier,
                          match var_type {
                              ActorOrEvent::Actor => "",
                              ActorOrEvent::Event => "_e",
                          },
                          var_string,
                      ),
                      AssociativityData::Monop,
                  )
              }
              Expr::Unary(MonOp::Iota(var_type), arg) => {
                  let (c, var_string) = c.inc_depth_q(*var_type);
                  let (arg, _) = self.string(LambdaExprRef(arg.0), c, false);
                  (
                      format!(
                          "iota{}({}, {arg})",
                          match var_type {
                              ActorOrEvent::Actor => "",
                              ActorOrEvent::Event => "_e",
                          },
                          var_string,
                      ),
                      AssociativityData::Monop,
                  )
              }
              Expr::Actor(a) => (format!("a_{a}"), AssociativityData::Monop),
              Expr::Event(e) => (format!("e_{e}"), AssociativityData::Monop),
              Expr::Binary(bin_op, x, y) => {
                  todo!()
              }
                    {
                        let (x, x_a) = self.string(LambdaExprRef(x.0), c.clone(), false);
                        let (y, y_a) = self.string(LambdaExprRef(y.0), c, false);
                        match bin_op {
                            BinOp::AgentOf | BinOp::PatientOf => {
                                (format!("{bin_op}({x}, {y})"), AssociativityData::Monop)
                            }

                            BinOp::And | BinOp::Or => (
                                {
                                    let mut s = String::default();
                                    if add_parenthesis_for_bin_op(*bin_op, x_a) {
                                        write!(s, "({x})").unwrap();
                                    } else {
                                        s.push_str(&x);
                                    }
                                    write!(s, " {bin_op} ").unwrap();
                                    if add_parenthesis_for_bin_op(*bin_op, y_a) {
                                        write!(s, "({y})").unwrap();
                                    } else {
                                        s.push_str(&y);
                                    }
                                    s
                                },
                                AssociativityData::Binom(*bin_op),
                            ),
                        }
                    }
                    Expr::Unary(mon_op, arg) => {
                        let (arg, arg_binom) = self.string(LambdaExprRef(arg.0), c, false);
                        (
                            match mon_op {
                                MonOp::Not => match arg_binom {
                                    AssociativityData::Binom(BinOp::And | BinOp::Or) => {
                                        format!("{mon_op}({arg})")
                                    }
                                    AssociativityData::Binom(_)
                                    | AssociativityData::Lambda
                                    | AssociativityData::App
                                    | AssociativityData::Monop => {
                                        format!("{mon_op}{arg}")
                                    }
                                },
                                _ => format!("{mon_op}({arg})"),
                            },
                            AssociativityData::Monop,
                        )
                    }
                    Expr::Constant(constant) => (format!("{constant}"), AssociativityData::Monop),
                },*/
        }
    }
}

#[cfg(test)]
mod test {
    use crate::language::Expr;

    use super::*;

    #[test]
    fn var_name_assigner() {
        assert_eq!(to_var(0, None), "x");
        assert_eq!(to_var(1, None), "y");
        assert_eq!(to_var(2, None), "z");
        assert_eq!(to_var(26, None), "x1");
        assert_eq!(to_var(27, None), "y1");
        assert_eq!(to_var(28, None), "z1");
        assert_eq!(to_var(26 * 300, None), "x300");
    }

    #[test]
    fn printing() -> anyhow::Result<()> {
        let pool = RootedLambdaPool::<Expr>::parse(
            "some_e(x0, all_e, AgentOf(a_1, x0) & PatientOf(a_0, x0) & pe_0(x0))",
        )?;
        assert_eq!(
            pool.to_string(),
            "some_e(x, all_e, AgentOf(a_1, x) & PatientOf(a_0, x) & pe_0(x))"
        );
        let likes = RootedLambdaPool::<Expr>::parse(
            "lambda e x lambda e y (some(e, all_a, AgentOf(e, x) & PatientOf(e, y) & pe_likes(y)))",
        )?;

        let s =
            "lambda e x lambda e y some(z, all_a, AgentOf(z, x) & PatientOf(z, y) & pe_likes(y))";
        assert_eq!(likes.to_string(), s,);
        let likes2 = RootedLambdaPool::<Expr>::parse(s)?;
        assert_eq!(likes, likes2);

        Ok(())
    }
}
