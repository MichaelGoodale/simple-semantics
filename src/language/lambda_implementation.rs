use ahash::HashMap;
use chumsky::prelude::*;
use std::iter::empty;
use thiserror::Error;

use super::{
    ActorOrEvent, BinOp, Constant, Expr, ExprPool, ExprRef, LambdaParseError, LanguageExpression,
    MonOp, Variable, lot_parser,
};
use crate::lambda::{
    LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool, ReductionError,
    RootedLambdaPool, types::LambdaType,
};
use chumsky::{error::Rich, extra};

impl From<ExprRef> for LambdaExprRef {
    fn from(value: ExprRef) -> Self {
        LambdaExprRef(value.0)
    }
}

impl From<LambdaExprRef> for ExprRef {
    fn from(value: LambdaExprRef) -> Self {
        ExprRef(value.0)
    }
}

#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum LambdaConversionError {
    #[error("There are still lambda terms in this pool")]
    StillHasLambdaTerms,
    #[error("Reducing lambda exprs in quantifiers is leading to a bug ({0})")]
    ReductionError(#[from] ReductionError),
}

impl<'a> LambdaLanguageOfThought for Expr<'a> {
    type Pool = LanguageExpression<'a>;
    type ConversionError = LambdaConversionError;

    fn get_children(&self) -> impl Iterator<Item = LambdaExprRef> {
        match self {
            Expr::Quantifier {
                restrictor,
                subformula,
                ..
            } => vec![restrictor, subformula],
            Expr::Binary(_, x, y) => vec![x, y],
            Expr::Unary(_, x) => vec![x],
            Expr::Constant(_) | Expr::Actor(_) | Expr::Event(_) | Expr::Variable(_) => vec![],
        }
        .into_iter()
        .map(|x| LambdaExprRef(x.0))
    }

    fn change_children(&mut self, new_children: &[LambdaExprRef]) {
        match self {
            Expr::Quantifier {
                restrictor,
                subformula,
                ..
            } => {
                *restrictor = ExprRef(new_children[0].0);
                *subformula = ExprRef(new_children[1].0);
            }
            Expr::Binary(_, x, y) => {
                *x = ExprRef(new_children[0].0);
                *y = ExprRef(new_children[1].0);
            }
            Expr::Unary(_, x) => {
                *x = ExprRef(new_children[0].0);
            }
            Expr::Variable(_) | Expr::Actor(_) | Expr::Event(_) | Expr::Constant(_) => (),
        }
    }

    fn remap_refs(&mut self, remap: &[usize]) {
        match self {
            Expr::Quantifier {
                restrictor,
                subformula,
                ..
            } => {
                *restrictor = ExprRef(remap[restrictor.0 as usize] as u32);
                *subformula = ExprRef(remap[subformula.0 as usize] as u32);
            }
            Expr::Binary(_, x, y) => {
                *x = ExprRef(remap[x.0 as usize] as u32);
                *y = ExprRef(remap[y.0 as usize] as u32);
            }
            Expr::Unary(_, x) => {
                *x = ExprRef(remap[x.0 as usize] as u32);
            }
            Expr::Variable(_) | Expr::Actor(_) | Expr::Event(_) | Expr::Constant(_) => (),
        }
    }

    fn get_type(&self) -> &LambdaType {
        match self {
            Expr::Quantifier { .. } => LambdaType::t(),
            Expr::Variable(Variable::Event(_)) => LambdaType::e(),
            Expr::Variable(Variable::Actor(_)) => LambdaType::a(),
            Expr::Actor(_) => LambdaType::a(),
            Expr::Event(_) => LambdaType::e(),
            Expr::Binary(bin, ..) => match bin {
                BinOp::AgentOf | BinOp::PatientOf | BinOp::And | BinOp::Or => LambdaType::t(),
            },
            Expr::Unary(mon_op, _) => match mon_op {
                MonOp::Property(_, _) | MonOp::Tautology | MonOp::Contradiction | MonOp::Not => {
                    LambdaType::t()
                }
            },
            Expr::Constant(constant) => match constant {
                Constant::Everyone | Constant::Property(_, ActorOrEvent::Actor) => LambdaType::at(),
                Constant::EveryEvent | Constant::Property(_, ActorOrEvent::Event) => {
                    LambdaType::et()
                }
                Constant::Contradiction | Constant::Tautology => LambdaType::t(),
            },
        }
    }

    fn to_pool(
        mut pool: LambdaPool<Self>,
        mut root: LambdaExprRef,
    ) -> Result<Self::Pool, Self::ConversionError> {
        //Quantifiers can have lambda terms embedded in them, this extracts them!
        //e.g. some(x, lambda a y (pa_0(y) | pa_1(y)), pa_3(x)) -> some(x, pa_0(x) | pa_1(x), pa_3(x))
        let quantifier_restrictions = pool
            .0
            .iter()
            .enumerate()
            .filter_map(|(i, x)| {
                if let LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                    var, restrictor, ..
                }) = x
                {
                    let restr_expr = pool.get(LambdaExprRef(restrictor.0));
                    let should_bind = match var {
                        Variable::Actor(_) => {
                            matches!(restr_expr, LambdaExpr::Lambda(_, t) if t == LambdaType::a())
                        }
                        Variable::Event(_) => {
                            matches!(restr_expr, LambdaExpr::Lambda(_, t) if t == LambdaType::e())
                        }
                    };

                    if should_bind {
                        Some((LambdaExprRef(i as u32), LambdaExprRef(restrictor.0), *var))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        if !quantifier_restrictions.is_empty() {
            //Go over and add app of bound variable to each lambda expr for each quantifier
            for (quantifer, restrictor, var) in quantifier_restrictions {
                let var = pool.add(LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(var)));
                let new_restrictor = pool.add(LambdaExpr::Application {
                    subformula: restrictor,
                    argument: var,
                });
                let LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier { restrictor, .. }) =
                    pool.get_mut(quantifer)
                else {
                    panic!("quantifier *must* be filtered to only quantifiers right before this.")
                };

                *restrictor = ExprRef(new_restrictor.0);
            }
            root = pool.reduce(root)?;
        }

        let processed_pool = pool
            .0
            .into_iter()
            .map(|x| match x {
                LambdaExpr::LanguageOfThoughtExpr(x) => Ok(x),
                _ => Err(LambdaConversionError::StillHasLambdaTerms),
            })
            .collect::<Result<Vec<_>, LambdaConversionError>>()?;

        Ok(LanguageExpression {
            pool: ExprPool(processed_pool),
            start: ExprRef(root.0),
        })
    }

    fn alpha_reduce(a: &mut LambdaPool<Self>, b: &mut LambdaPool<Self>) {
        let mut max_var = None;
        for x in a.iter_mut() {
            match x {
                LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier { var: v, .. })
                | LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(v)) => {
                    if let Some(max_var) = max_var.as_mut() {
                        let v = v.id();
                        if v > *max_var {
                            *max_var = v;
                        }
                    } else {
                        max_var = Some(v.id());
                    }
                }
                _ => (),
            }
        }

        if let Some(max_var) = max_var {
            for x in b.iter_mut() {
                match x {
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier { var: v, .. })
                    | LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(v)) => {
                        *v = match v {
                            Variable::Actor(a) => Variable::Actor(max_var + *a + 1),
                            Variable::Event(e) => Variable::Event(max_var + *e + 1),
                        }
                    }
                    _ => (),
                }
            }
        }
    }

    fn get_arguments<'b>(&'b self) -> Box<dyn Iterator<Item = LambdaType> + 'b> {
        match self {
            Expr::Quantifier {
                var: Variable::Actor(_),
                ..
            } => Box::new([LambdaType::at().clone(), LambdaType::t().clone()].into_iter()),
            Expr::Quantifier {
                var: Variable::Event(_),
                ..
            } => Box::new([LambdaType::et().clone(), LambdaType::t().clone()].into_iter()),
            Expr::Binary(b, _, _) => Box::new(b.get_argument_type().into_iter().cloned()),
            Expr::Unary(mon_op, _) => Box::new([mon_op.get_argument_type().clone()].into_iter()),
            Expr::Variable(Variable::Event(_))
            | Expr::Variable(Variable::Actor(_))
            | Expr::Actor(_)
            | Expr::Event(_)
            | Expr::Constant(_) => Box::new(empty()),
        }
    }
}

impl<'a> std::fmt::Display for RootedLambdaPool<'a, Expr<'a>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (string, _) = self.string(self.root(), VarContext::default());
        write!(f, "{string}")
    }
}

static VARIABLENAMES: [char; 26] = [
    'x', 'y', 'z', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p',
    'q', 'r', 's', 't', 'u', 'v', 'w',
];

pub fn to_var(x: usize) -> String {
    if x < VARIABLENAMES.len() {
        format!("{}", VARIABLENAMES[x])
    } else {
        format!(
            "{}{}",
            VARIABLENAMES[x % VARIABLENAMES.len()],
            x / VARIABLENAMES.len()
        )
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
enum Var {
    Depth(usize),
    Quantifier(Variable),
}

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub(super) struct VarContext {
    vars: HashMap<Var, usize>,
    depth: usize,
}

impl VarContext {
    pub(super) fn inc_depth(mut self) -> (Self, String) {
        let n_var = self.vars.len();
        self.vars.insert(Var::Depth(self.depth), n_var);
        self.depth += 1;
        (self, to_var(n_var))
    }

    pub(super) fn lambda_var(&self, bvar: usize) -> String {
        to_var(*self.vars.get(&Var::Depth(self.depth - bvar - 1)).unwrap())
    }
    pub(super) fn q_var(&self, var: Variable) -> String {
        to_var(
            self.vars
                .get(&Var::Quantifier(var))
                .copied()
                .unwrap_or_else(|| match var {
                    //This is on the off-chance that the string is invalid due to a mutation (e.g.
                    //swaping a quantifier and making a free var invalid)
                    Variable::Actor(a) | Variable::Event(a) => a as usize + 1000,
                }),
        )
    }

    pub(super) fn add_qvar(mut self, x: Variable) -> (Self, String) {
        let n_var = self.vars.len();
        self.vars.insert(Var::Quantifier(x), n_var);
        (self, to_var(n_var))
    }
}

impl<'a> From<LanguageExpression<'a>> for RootedLambdaPool<'a, Expr<'a>> {
    fn from(value: LanguageExpression<'a>) -> Self {
        RootedLambdaPool {
            pool: LambdaPool::from(
                value
                    .pool
                    .0
                    .iter()
                    .map(|x| LambdaExpr::LanguageOfThoughtExpr(*x))
                    .collect(),
            ),
            root: crate::lambda::LambdaExprRef(value.start.0),
        }
    }
}

#[derive(Debug, Copy, Clone)]
enum AssociativityData {
    IsBinom,
    IsMonop,
}

impl<'a> RootedLambdaPool<'a, Expr<'a>> {
    pub fn parse(s: &'a str) -> Result<Self, LambdaParseError> {
        lot_parser::<'a, extra::Err<Rich<_>>>()
            .parse(s)
            .into_result()?
            .to_pool()
    }

    fn string(&self, expr: LambdaExprRef, c: VarContext) -> (String, AssociativityData) {
        match self.get(expr) {
            LambdaExpr::Lambda(child, lambda_type) => {
                let (c, var) = c.inc_depth();
                let (child, child_asso) = self.string(*child, c);
                (
                    format!(
                        "lambda {} {} {}",
                        lambda_type,
                        var,
                        match child_asso {
                            AssociativityData::IsBinom => format!("({child})"),
                            AssociativityData::IsMonop => child,
                        }
                    ),
                    AssociativityData::IsBinom,
                )
            }
            LambdaExpr::BoundVariable(bvar, _) => (c.lambda_var(*bvar), AssociativityData::IsMonop),
            LambdaExpr::FreeVariable(fvar, t) => {
                (format!("{fvar}#{t}"), AssociativityData::IsMonop)
            }

            LambdaExpr::Application {
                subformula,
                argument,
            } => {
                let (sub, associative) = self.string(*subformula, c.clone());
                let (arg, _) = self.string(*argument, c);

                match associative {
                    AssociativityData::IsBinom => {
                        (format!("({sub})({arg})"), AssociativityData::IsBinom)
                    }
                    AssociativityData::IsMonop => {
                        (format!("{sub}({arg})"), AssociativityData::IsMonop)
                    }
                }
            }

            LambdaExpr::LanguageOfThoughtExpr(x) => match x {
                Expr::Quantifier {
                    quantifier,
                    var,
                    restrictor,
                    subformula,
                } => {
                    let (c, var_string) = c.add_qvar(*var);
                    let (restrictor, _) = self.string(LambdaExprRef(restrictor.0), c.clone());
                    let (subformula, _) = self.string(LambdaExprRef(subformula.0), c);
                    (
                        format!(
                            "{}{}({}, {restrictor}, {subformula})",
                            quantifier,
                            match var {
                                Variable::Actor(_) => "",
                                Variable::Event(_) => "_e",
                            },
                            var_string,
                        ),
                        AssociativityData::IsMonop,
                    )
                }
                Expr::Variable(variable) => (c.q_var(*variable), AssociativityData::IsMonop),
                Expr::Actor(a) => (format!("a_{a}"), AssociativityData::IsMonop),
                Expr::Event(e) => (format!("e_{e}"), AssociativityData::IsMonop),
                Expr::Binary(bin_op, x, y) => {
                    let (x, _) = self.string(LambdaExprRef(x.0), c.clone());
                    let (y, _) = self.string(LambdaExprRef(y.0), c);
                    match bin_op {
                        BinOp::AgentOf | BinOp::PatientOf => {
                            (format!("{bin_op}({x}, {y})",), AssociativityData::IsMonop)
                        }

                        BinOp::And | BinOp::Or => {
                            (format!("{x} {bin_op} {y}"), AssociativityData::IsBinom)
                        }
                    }
                }
                Expr::Unary(mon_op, arg) => {
                    let (arg, arg_binom) = self.string(LambdaExprRef(arg.0), c);
                    match (mon_op, arg_binom) {
                        (MonOp::Not, AssociativityData::IsMonop) => {
                            (format!("{mon_op}{arg}"), AssociativityData::IsMonop)
                        }
                        _ => (format!("{mon_op}({arg})"), AssociativityData::IsMonop),
                    }
                }
                Expr::Constant(constant) => (format!("{constant}"), AssociativityData::IsMonop),
            },
        }
    }
}
#[cfg(test)]
mod test {
    use super::to_var;

    use crate::{
        Entity, Scenario, ThetaRoles, lambda::RootedLambdaPool, language::lot_parser,
        parse_executable,
    };

    use chumsky::prelude::*;

    #[test]
    fn fancy_printing() -> anyhow::Result<()> {
        for statement in [
            "~AgentOf(a_John, e_0)",
            "pa_Red(a_John) & ~pa_Red(a_Mary)",
            "every(x, all_a, pa_Blue(x))",
            "every(x, pa_Blue, pa_Blue(x))",
            "every(x, pa_5, pa_10(a_59))",
            "every_e(x, all_e, PatientOf(a_Mary, x))",
        ] {
            println!("{statement}");
            let expression = parse_executable(statement)?;
            assert_eq!(expression.to_string(), statement);
        }
        for s in [
            "cool#<a,t>(a_John)",
            "bad#<a,t>(man#a)",
            "woah#<<e,t>,t>(lambda e x pe_wow(x))",
        ] {
            println!("{s}");
            let p = RootedLambdaPool::parse(s)?;
            assert_eq!(p.to_string(), s);
        }

        Ok(())
    }

    #[test]
    fn type_checking() -> anyhow::Result<()> {
        let parser = lot_parser::<extra::Err<Rich<_>>>().then_ignore(end());
        let john = parser.parse("a_John").unwrap().to_pool()?;
        let likes = parser
            .parse(
                "lambda a x ((lambda a y (some_e(e, all_e, AgentOf(x, e) & PatientOf(y, e) & pe_likes(e)))))",
            )
            .unwrap().to_pool()?;

        let mary = parser.parse("a_Mary").unwrap().to_pool()?;
        let phi = mary.clone().merge(likes.clone()).unwrap();
        let mut phi = phi.merge(john.clone()).unwrap();
        phi.reduce()?;
        let pool = phi.into_pool()?;
        assert_eq!(
            "some_e(x, all_e, AgentOf(a_Mary, x) & PatientOf(a_John, x) & pe_likes(x))",
            pool.to_string()
        );
        let phi = likes.merge(mary).unwrap();
        let mut phi = john.merge(phi).unwrap();
        phi.reduce()?;
        let pool = phi.into_pool()?;
        assert_eq!(
            "some_e(x, all_e, AgentOf(a_Mary, x) & PatientOf(a_John, x) & pe_likes(x))",
            pool.to_string()
        );
        Ok(())
    }

    #[test]
    fn var_name_assigner() {
        assert_eq!(to_var(0), "x");
        assert_eq!(to_var(1), "y");
        assert_eq!(to_var(2), "z");
        assert_eq!(to_var(26), "x1");
        assert_eq!(to_var(27), "y1");
        assert_eq!(to_var(28), "z1");
        assert_eq!(to_var(26 * 300), "x300");
    }

    #[test]
    fn printing() -> anyhow::Result<()> {
        let parser = lot_parser::<extra::Err<Rich<_>>>().then_ignore(end());
        let pool = parser
            .parse("some_e(x0, all_e, AgentOf(a_1, x0) & PatientOf(a_0, x0) & pe_0(x0))")
            .unwrap()
            .to_pool()?;
        assert_eq!(
            pool.to_string(),
            "some_e(x, all_e, AgentOf(a_1, x) & PatientOf(a_0, x) & pe_0(x))"
        );
        let likes = parser
            .parse(
                "lambda e x ((lambda e y (some(e, all_a, AgentOf(e, x) & PatientOf(e, y) & pe_likes(y)))))",
            )
            .unwrap().to_pool()?;

        let s =
            "lambda e x (lambda e y some(z, all_a, AgentOf(z, x) & PatientOf(z, y) & pe_likes(y)))";
        assert_eq!(likes.to_string(), s,);
        let likes2 = parser.parse(s).unwrap().to_pool()?;
        assert_eq!(likes, likes2);

        Ok(())
    }

    #[test]
    fn fancy_quantification_reduction() -> anyhow::Result<()> {
        let parser = lot_parser::<extra::Err<Rich<_>>>().then_ignore(end());
        let pool = parser
            .parse("every_e(x0,pe_0(x0) & pe_1(x0), pe_2(x0))")
            .unwrap()
            .to_pool()?;
        let scenario = Scenario::new(
            vec![],
            vec![ThetaRoles::default(); 5],
            [
                ("0", vec![Entity::Event(1), Entity::Event(2)]),
                ("1", vec![Entity::Event(0), Entity::Event(1)]),
                ("2", vec![Entity::Event(1)]),
            ]
            .into_iter()
            .collect(),
        );

        assert!(pool.into_pool()?.run(&scenario)?.try_into()?);

        let pool = parser
            .parse("every_e(x0, lambda e x (pe_0(x) & pe_1(x)), pe_2(x0))")
            .unwrap()
            .to_pool()?;

        let scenario = Scenario::new(
            vec![],
            vec![ThetaRoles::default(); 5],
            [
                ("0", vec![Entity::Event(1), Entity::Event(2)]),
                ("1", vec![Entity::Event(0), Entity::Event(1)]),
                ("2", vec![Entity::Event(1)]),
            ]
            .into_iter()
            .collect(),
        );

        assert!(pool.into_pool()?.run(&scenario)?.try_into()?);

        Ok(())
    }
}
