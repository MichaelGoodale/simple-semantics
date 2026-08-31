use std::fmt::{Debug, Display};

use ahash::HashMap;
use serde::{Deserialize, Serialize};

use crate::lambda::{
    ExprType, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, RootedLambdaPool,
    parser::ParseLot, types::LambdaType,
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

impl<'a, T: LambdaLanguageOfThought + Display + PartialEq> std::fmt::Display
    for RootedLambdaPool<'a, T>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (string, _) = self.string(self.root(), VarContext::default(), false);
        write!(f, "{string}")
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum InfixPosition {
    Op,
    DoneLeftOnly,
    Done,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum AssociativityData<'a, T> {
    Lambda,
    Var,
    App,
    Infix(&'a T, InfixPosition),
    Prefix,
}

impl<'src, T: LambdaLanguageOfThought + Display + PartialEq> RootedLambdaPool<'src, T> {
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
                let (mut arg, arg_asso) = self.string(*argument, c, false); // false
                // since apps only collapse if they're a left chain

                if let AssociativityData::Infix(t1, _) = arg_asso
                    && let AssociativityData::Infix(t2, _) = associative
                    && t1 != t2
                {
                    arg = format!("({arg})");
                }

                let mut s = match associative {
                    AssociativityData::Infix(x, InfixPosition::Op) if parent_is_app => {
                        return (
                            format!("{arg} {sub}"),
                            AssociativityData::Infix(x, InfixPosition::DoneLeftOnly),
                        );
                    }
                    AssociativityData::Infix(x, InfixPosition::DoneLeftOnly) => {
                        return (
                            format!("{sub} {arg}"),
                            AssociativityData::Infix(x, InfixPosition::Done),
                        );
                    }
                    AssociativityData::Lambda => {
                        format!("({sub})({arg}")
                    }
                    AssociativityData::Prefix => {
                        return match arg_asso {
                            AssociativityData::App
                            | AssociativityData::Var
                            | AssociativityData::Prefix => {
                                (format!("{sub}{arg}"), AssociativityData::Var)
                            }
                            AssociativityData::Lambda | AssociativityData::Infix(..) => {
                                (format!("{sub}({arg})"), AssociativityData::Var)
                            }
                        };
                    }
                    AssociativityData::Var => format!("{sub}({arg}"),
                    AssociativityData::App => format!("{sub}{arg}"),
                    _ => todo!(),
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
                    AssociativityData::Infix(x, InfixPosition::Op)
                } else if x.unary_associative() {
                    AssociativityData::Prefix
                } else {
                    AssociativityData::Var
                },
            ),
            LambdaExpr::LanguageOfThoughtExpr(x, ExprType::BindVar(body)) => {
                let (c, var_string) = c.inc_depth(x.var_type().expect(
                    "Implementation error, if you bind a var, the expression must bind vars!",
                ));
                let (body, _) = self.string(LambdaExprRef(body.0), c.clone(), false);
                (format!("{x}({var_string}, {body})"), AssociativityData::Var)
            }
            LambdaExpr::LanguageOfThoughtExpr(x, ExprType::BindVarTwoBodies(l, r)) => {
                let (c, var_string) = c.inc_depth(x.var_type().expect(
                    "Implementation error, if you bind a var, the expression must bind vars!",
                ));
                let (l, _) = self.string(LambdaExprRef(l.0), c.clone(), false);
                let (r, _) = self.string(LambdaExprRef(r.0), c, false);
                (
                    format!("{x}({var_string}, {l}, {r})"),
                    AssociativityData::Var,
                )
            }
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
    fn printing_parsing_idempotent() -> anyhow::Result<()> {
        for phi in [
            "True & False & True & False",
            "(True & False) | True",
            "False | (True & False & True)",
            "some_e(x, all_e(x), AgentOf(a_1, x) & PatientOf(a_0, x) & pe_0(x))",
            "lambda e x lambda e y some(z, all_a(z), AgentOf(z, x) & PatientOf(z, y) & pe_likes(y))",
            "~True",
            "~~True",
            "~~~True",
            "~AgentOf(a_John, e_0)",
            "pa_Red(a_John) & ~pa_Red(a_Mary)",
            "every(x, all_a(x), pa_Blue(x))",
            "every(x, pa_Blue(x), pa_Blue(x))",
            "every(x, pa_5(x), pa_10(a_59))",
            "every_e(x, all_e(x), PatientOf(a_Mary, x))",
            "cool#<a,t>(a_John)",
            "bad#<a,t>(man#a)",
            "woah#<<e,t>,t>(lambda e x pe_wow(x))",
            "lambda <a,t> P lambda a x P(x)",
            "lambda <a,t> P P(a_man) & ~P(a_woman)",
            "loves#<a,<a,t>>(a_john, a_mary)",
            "gives#<a,<a,<a,t>>>(a_john, a_mary, a_present)",
            "lambda e x lambda a y loves#<e,<a,t>>(x, y)",
            "True",
            "False",
            "~False",
            "~~~~False",
            "(True & True) | False",
            "True | (False & True)",
            "(True & False) | (False & True)",
            "~(True & ~False)",
            "True & (False | (True & (False | True)))",
            "pa_Red(a_John)",
            "~pa_Red(a_John)",
            "~~pa_Red(a_John)",
            "pa_Red(a_John) & pa_Blue(a_John)",
            "(pa_Red(a_John) & pa_Blue(a_John)) | pa_Green(a_John)",
            "every(x, all_a(x), pa_Blue(x))",
            "some(x, all_a(x), ~pa_Blue(x))",
            "every(x, all_a(x), pa_Blue(x) & ~pa_Red(x))",
            "some(x, all_a(x), pa_Blue(x) | pa_Red(x))",
            "every(x, all_a(x), some_e(y, all_e(y), AgentOf(x, y)))",
            "some(x, all_a(x), every_e(y, all_e(y), ~PatientOf(x, y)))",
            "lambda e x pe_run(x)",
            "lambda e x ~pe_run(x)",
            "lambda e x pe_run(x) & pe_walk(x)",
            "lambda a x lambda e y AgentOf(x, y)",
            "lambda e x lambda a y loves#<e,<a,t>>(x, y)",
            "lambda <a,t> P P(a_John)",
            "lambda <a,t> P ~P(a_John)",
            "lambda <a,t> P P(a_John) & P(a_Mary)",
            "lambda <a,t> P P(a_John) & ~P(a_Mary)",
            "lambda <a,<a,t>> M lambda a x lambda a y M(x, y)",
            "cool#<a,t>(a_John)",
            "bad#<a,t>(man#a)",
            "loves#<a,<a,t>>(a_john, a_mary)",
            "gives#<a,<a,<a,t>>>(a_john, a_mary, a_present)",
            "woah#<<e,t>,t>(lambda e x pe_wow(x))",
            "f#<a,t>(a_x)",
            "f#<a,t>(a_x) & g#<a,t>(a_y)",
            "f#<a,<a,t>>(a_x, a_y)",
            "f#<a,<a,<a,t>>>(a_x, a_y, a_z)",
            "some_e(x, all_e(x), AgentOf(a_1, x) & PatientOf(a_0, x) & pe_0(x))",
            "every_e(x, all_e(x), PatientOf(a_Mary, x))",
            "some_e(x, all_e(x), ~PatientOf(a_Mary, x))",
            "every_e(x, all_e(x), some(y, all_a(y), AgentOf(y, x)))",
            "lambda e x some(y, all_a(y), AgentOf(y, x))",
            "lambda e x lambda e y some(z, all_a(z), AgentOf(z, x) & PatientOf(z, y) & pe_likes(y))",
        ] {
            let pool = RootedLambdaPool::<Expr>::parse(phi)?;
            let s = pool.to_string();
            assert_eq!(pool.to_string(), phi, "{s} instead of {phi}")
        }

        Ok(())
    }
    #[test]
    fn parse_print_normalized() -> anyhow::Result<()> {
        for (phi, phi_normalized) in [
            (
                "(True & False) & True & False",
                "True & False & True & False",
            ),
            ("True & False | True", "(True & False) | True"),
            ("(True)", "True"),
            ("(((True)))", "True"),
            ("(((lambda e x pe_run(x))))", "lambda e x pe_run(x)"),
            ("lambda e x (pe_run(x))", "lambda e x pe_run(x)"),
            (
                "((True & False) | (False & True))",
                "(True & False) | (False & True)",
            ),
            (
                "lambda <a,<a,t>> R lambda a x lambda a y R(x, y)",
                "lambda <a,<a,t>> M lambda a x lambda a y M(x, y)",
            ),
            (
                "lambda e x (pe_run(x) & ~pe_walk(x))",
                "lambda e x pe_run(x) & ~pe_walk(x)",
            ),
            (
                "every(x, all_a(x), (pa_Blue(x)))",
                "every(x, all_a(x), pa_Blue(x))",
            ),
            (
                "some(x, all_a(x), ((pa_Blue(x) & pa_Red(x))))",
                "some(x, all_a(x), pa_Blue(x) & pa_Red(x))",
            ),
        ] {
            let pool = RootedLambdaPool::<Expr>::parse(phi)?;
            let s = pool.to_string();
            assert_eq!(
                pool.to_string(),
                phi_normalized,
                "{s} instead of {phi_normalized}"
            )
        }

        Ok(())
    }
}
