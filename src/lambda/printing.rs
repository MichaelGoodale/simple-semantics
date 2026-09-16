use std::fmt::{Debug, Display};

use super::interpretation::Value;
use ahash::HashMap;

use crate::lambda::{LambdaLanguageOfThought, RootedLambdaPool, types::LambdaType};

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

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub(super) struct VarContext<'a> {
    vars: HashMap<usize, usize>,
    predicates: HashMap<usize, usize>,
    other_functions: HashMap<usize, usize>,
    truths: HashMap<usize, usize>,
    lambdas: Vec<&'a LambdaType>,
}

impl<'a> VarContext<'a> {
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

    pub(super) fn inc_depth(mut self, t: &'a LambdaType) -> (Self, String) {
        let d = self.depth();
        let map = self.get_map_mut(Some(t));
        let n_var = map.len();
        map.insert(d, n_var);
        self.lambdas.push(t);
        (self, to_var(n_var, Some(t)))
    }

    pub(super) fn lambda_var_by_level(&self, bvar: usize) -> String {
        let t = self.lambdas[bvar];
        to_var(*self.get_map(Some(t)).get(&(bvar)).unwrap(), Some(t))
    }

    pub(super) fn lambda_var(&self, bvar: usize) -> String {
        let t = self.lambdas[self.depth() - bvar - 1];
        to_var(
            *self
                .get_map(Some(t))
                .get(&(self.depth() - bvar - 1))
                .unwrap(),
            Some(t),
        )
    }

    fn depth(&self) -> usize {
        self.lambdas.len()
    }
}

impl<T: LambdaLanguageOfThought + Display + Clone + PartialEq> std::fmt::Display
    for RootedLambdaPool<'_, T>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let x = self.tokens(self.root, VarContext::default());
        write!(f, "{x}")
    }
}

impl<T: LambdaLanguageOfThought + Display + PartialEq + Clone> Display for Value<'_, '_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.tokens(VarContext::default()))
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
