use crate::utils::ArgumentIterator;
use ahash::HashMap;
use std::iter::empty;
use thiserror::Error;

use super::{
    ActorOrEvent, BinOp, Constant, Expr, ExprPool, ExprRef, LambdaParseError, LanguageExpression,
    MonOp, Variable,
};
use crate::{
    lambda::{
        LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool, ReductionError,
        RootedLambdaPool, types::LambdaType,
    },
    language::parser::parse_lot,
};

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

    fn n_children(&self) -> usize {
        match self {
            Expr::Quantifier { .. } => 2,
            Expr::Variable(_) => 0,
            Expr::Actor(_) => 0,
            Expr::Event(_) => 0,
            Expr::Constant(_) => 0,
            Expr::Binary(..) => 2,
            Expr::Unary(..) => 1,
        }
    }

    fn inc_depth(&self) -> bool {
        matches!(self, Expr::Quantifier { .. })
    }

    fn var_type(&self) -> Option<&LambdaType> {
        match self {
            Expr::Quantifier { var_type, .. } => match var_type {
                ActorOrEvent::Actor => Some(LambdaType::a()),
                ActorOrEvent::Event => Some(LambdaType::e()),
            },
            _ => None,
        }
    }

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

    fn change_children(&mut self, mut new_children: impl Iterator<Item = LambdaExprRef>) {
        match self {
            Expr::Quantifier {
                restrictor,
                subformula,
                ..
            } => {
                *restrictor = ExprRef(new_children.next().unwrap().0);
                *subformula = ExprRef(new_children.next().unwrap().0);
            }
            Expr::Binary(_, x, y) => {
                *x = ExprRef(new_children.next().unwrap().0);
                *y = ExprRef(new_children.next().unwrap().0);
            }
            Expr::Unary(_, x) => {
                *x = ExprRef(new_children.next().unwrap().0);
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
                MonOp::Property(_, _) | MonOp::Not => LambdaType::t(),
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

    fn to_pool(pool: RootedLambdaPool<Self>) -> Result<Self::Pool, Self::ConversionError> {
        let processed_pool = pool
            .pool
            .0
            .into_iter()
            .map(|x| match x {
                LambdaExpr::LanguageOfThoughtExpr(x) => Ok(x),
                LambdaExpr::BoundVariable(x, LambdaType::A) => {
                    Ok(Expr::Variable(Variable::Actor(x as u32)))
                }
                LambdaExpr::BoundVariable(x, LambdaType::E) => {
                    Ok(Expr::Variable(Variable::Event(x as u32)))
                }
                _ => Err(LambdaConversionError::StillHasLambdaTerms),
            })
            .collect::<Result<Vec<_>, LambdaConversionError>>()?;

        Ok(LanguageExpression {
            pool: ExprPool(processed_pool),
            start: ExprRef(pool.root.0),
        })
    }

    fn get_arguments(&self) -> impl Iterator<Item = LambdaType> {
        match self {
            Expr::Quantifier {
                var_type: ActorOrEvent::Actor,
                ..
            } => {
                ArgumentIterator::A([LambdaType::t().clone(), LambdaType::t().clone()].into_iter())
            }
            Expr::Quantifier {
                var_type: ActorOrEvent::Event,
                ..
            } => {
                ArgumentIterator::A([LambdaType::t().clone(), LambdaType::t().clone()].into_iter())
            }
            Expr::Binary(b, _, _) => {
                ArgumentIterator::B(b.get_argument_type().into_iter().cloned())
            }
            Expr::Unary(mon_op, _) => {
                ArgumentIterator::C([mon_op.get_argument_type().clone()].into_iter())
            }
            Expr::Variable(Variable::Event(_))
            | Expr::Variable(Variable::Actor(_))
            | Expr::Actor(_)
            | Expr::Event(_)
            | Expr::Constant(_) => ArgumentIterator::D(empty()),
        }
    }
}

impl<'a> std::fmt::Display for RootedLambdaPool<'a, Expr<'a>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (string, _) = self.string(self.root(), VarContext::default(), false);
        write!(f, "{string}")
    }
}

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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(super) enum AssociativityData {
    Lambda,
    App,
    Binom(BinOp),
    Monop,
}

///An error which results from a failed application of [`RootedLambdaPool::conjoin`]
#[derive(Debug, Clone, Error, PartialEq, Eq)]
pub enum ConjoiningError {
    ///Both arguments have to have the same type
    #[error("Can't conjoin {0} and {1}")]
    MismatchingTypes(LambdaType, LambdaType),

    ///The type must return a truth value
    #[error("Lambda type, {0} doesn't return a truth value")]
    DoesntReturnT(LambdaType),

    ///One of the arguments has an internal problem leading to reduction errors
    #[error("One of the operands causes problems in reduction: {0})")]
    ReductionError(#[from] ReductionError),
}

fn who_raises_who<'a>(
    a: RootedLambdaPool<'a, Expr<'a>>,
    b: RootedLambdaPool<'a, Expr<'a>>,
) -> Result<
    (
        RootedLambdaPool<'a, Expr<'a>>,
        RootedLambdaPool<'a, Expr<'a>>,
    ),
    ConjoiningError,
> {
    let a_type = a.get_type().unwrap();
    let b_type = b.get_type().unwrap();

    let Ok(a_rhs) = a_type.rhs() else {
        return Err(ConjoiningError::DoesntReturnT(a_type));
    };
    let Ok(b_rhs) = b_type.rhs() else {
        return Err(ConjoiningError::DoesntReturnT(b_type));
    };
    if b_rhs != &LambdaType::T && a_rhs != &LambdaType::T {
        return Err(ConjoiningError::DoesntReturnT(a_type));
    }

    if a_rhs != &b_type && b_rhs != &a_type {
        Err(ConjoiningError::MismatchingTypes(a_type, b_type))
    } else if a_rhs == &b_type {
        Ok((a, b))
    } else {
        Ok((b, a))
    }
}

impl<'a> RootedLambdaPool<'a, Expr<'a>> {
    ///Takes two lambda expressions, phi and psi of type <x, t> where x is any type and returns phi
    ///AND psi.
    pub fn conjoin(self, other: Self) -> Result<Self, ConjoiningError> {
        let self_type = self.get_type().unwrap();
        let other_type = other.get_type().unwrap();
        if self_type != other_type {
            return Err(ConjoiningError::MismatchingTypes(self_type, other_type));
        }

        let Ok((lhs, rhs)) = self_type.split() else {
            return Err(ConjoiningError::DoesntReturnT(self_type));
        };

        if rhs != &LambdaType::T {
            return Err(ConjoiningError::DoesntReturnT(self_type));
        }
        let lhs = lhs.clone();

        let combinator = RootedLambdaPool {
            pool: LambdaPool(vec![
                LambdaExpr::Lambda(LambdaExprRef(1), self_type.clone()),
                LambdaExpr::Lambda(LambdaExprRef(2), other_type.clone()),
                LambdaExpr::Lambda(LambdaExprRef(3), lhs.clone()),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(BinOp::And, ExprRef(4), ExprRef(7))),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(5),
                    argument: LambdaExprRef(6),
                },
                LambdaExpr::BoundVariable(2, self_type),
                LambdaExpr::BoundVariable(0, lhs.clone()),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(8),
                    argument: LambdaExprRef(9),
                },
                LambdaExpr::BoundVariable(1, other_type),
                LambdaExpr::BoundVariable(0, lhs),
            ]),
            root: LambdaExprRef(0),
        };

        let mut conjoined = combinator.merge(self).unwrap().merge(other).unwrap();
        conjoined.reduce()?;
        Ok(conjoined)
    }

    ///Takes two lambda expressions, phi <x, <y,t>> and psi of type <y, t> where x and y is any type and returns phi
    ///AND psi.
    ///
    ///This is a generalized kind of Event Identification from Kratzer (1996)
    ///
    /// - Kratzer, A. (1996). Severing the External Argument from its Verb. In J. Rooryck & L. Zaring (Eds.), Phrase Structure and the Lexicon (pp. 109–137). Springer Netherlands. https://doi.org/10.1007/978-94-015-8617-7_5
    pub fn raised_conjoin(self, other: Self) -> Result<Self, ConjoiningError> {
        let (a, b) = who_raises_who(self, other)?;
        let a_type = a.get_type().unwrap();
        let b_type = b.get_type().unwrap();

        let Ok(event) = a_type.lhs() else {
            return Err(ConjoiningError::DoesntReturnT(a_type));
        };

        let Ok(e) = b_type.lhs() else {
            return Err(ConjoiningError::DoesntReturnT(b_type));
        };
        let e = e.clone();
        let event = event.clone();

        let combinator = RootedLambdaPool {
            pool: LambdaPool(vec![
                LambdaExpr::Lambda(LambdaExprRef(1), a_type.clone()),
                LambdaExpr::Lambda(LambdaExprRef(2), b_type.clone()),
                LambdaExpr::Lambda(LambdaExprRef(3), event.clone()),
                LambdaExpr::Lambda(LambdaExprRef(4), e.clone()),
                LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(
                    BinOp::And,
                    ExprRef(5),
                    ExprRef(10),
                )),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(6),
                    argument: LambdaExprRef(9),
                },
                LambdaExpr::Application {
                    subformula: LambdaExprRef(7),
                    argument: LambdaExprRef(8),
                },
                LambdaExpr::BoundVariable(3, a_type),
                LambdaExpr::BoundVariable(1, event),
                LambdaExpr::BoundVariable(0, e.clone()),
                LambdaExpr::Application {
                    subformula: LambdaExprRef(11),
                    argument: LambdaExprRef(12),
                },
                LambdaExpr::BoundVariable(2, b_type),
                LambdaExpr::BoundVariable(0, e),
            ]),
            root: LambdaExprRef(0),
        };

        let mut conjoined = combinator.merge(a).unwrap().merge(b).unwrap();
        conjoined.reduce()?;
        Ok(conjoined)
    }

    ///Create a [`RootedLambdaPool<Expr>`] from a string.
    pub fn parse(s: &'a str) -> Result<Self, LambdaParseError> {
        parse_lot(s)
    }

    fn string(
        &self,
        expr: LambdaExprRef,
        c: VarContext,
        parent_is_app: bool,
    ) -> (String, AssociativityData) {
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
                    AssociativityData::Lambda | AssociativityData::Binom(_) => {
                        format!("({sub})({arg}")
                    }
                    AssociativityData::Monop => format!("{sub}({arg}"),
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
                (c.lambda_var(*bvar, lambda_type), AssociativityData::Monop)
            }
            LambdaExpr::FreeVariable(fvar, t) => (format!("{fvar}#{t}"), AssociativityData::Monop),
            LambdaExpr::LanguageOfThoughtExpr(x) => match x {
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
                Expr::Actor(a) => (format!("a_{a}"), AssociativityData::Monop),
                Expr::Event(e) => (format!("e_{e}"), AssociativityData::Monop),
                Expr::Binary(bin_op, x, y) => {
                    let (x, x_a) = self.string(LambdaExprRef(x.0), c.clone(), false);
                    let (y, y_a) = self.string(LambdaExprRef(y.0), c, false);
                    match bin_op {
                        BinOp::AgentOf | BinOp::PatientOf => {
                            (format!("{bin_op}({x}, {y})",), AssociativityData::Monop)
                        }

                        BinOp::And | BinOp::Or => (
                            {
                                let mut s = String::default();
                                if add_parenthesis_for_bin_op(*bin_op, x_a) {
                                    s.push_str(&format!("({x})"))
                                } else {
                                    s.push_str(&x)
                                };
                                s.push_str(&format!(" {bin_op} "));
                                if add_parenthesis_for_bin_op(*bin_op, y_a) {
                                    s.push_str(&format!("({y})"))
                                } else {
                                    s.push_str(&y)
                                };
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
                                AssociativityData::Binom(BinOp::And)
                                | AssociativityData::Binom(BinOp::Or) => format!("{mon_op}({arg})"),
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
            },
        }
    }
}

pub(super) fn add_parenthesis_for_bin_op(x: BinOp, data: AssociativityData) -> bool {
    match data {
        AssociativityData::Binom(b) => match b {
            BinOp::AgentOf | BinOp::PatientOf => false,
            BinOp::And | BinOp::Or if b == x => false,
            BinOp::And | BinOp::Or => true,
        },
        AssociativityData::Lambda => true,
        AssociativityData::App | AssociativityData::Monop => false,
    }
}

#[cfg(test)]
mod test {
    use super::to_var;

    use crate::lambda::{FreeVar, types::LambdaType};
    use crate::{Entity, Scenario, ThetaRoles, lambda::RootedLambdaPool, parse_executable};

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
            "lambda <a,t> P lambda a x P(x)",
            "lambda <a,t> P P(a_man) & ~P(a_woman)",
            "loves#<a,<a,t>>(a_john, a_mary)",
            "gives#<a,<a,<a,t>>>(a_john, a_mary, a_present)",
            "lambda e x lambda a y loves#<e,<a,t>>(x, y)",
        ] {
            println!("{s}");
            let p = RootedLambdaPool::parse(s)?;
            assert_eq!(p.to_string(), s);
        }

        Ok(())
    }

    #[test]
    fn type_checking() -> anyhow::Result<()> {
        let john = RootedLambdaPool::parse("a_John")?;
        let likes = RootedLambdaPool::parse(
            "lambda a x ((lambda a y (some_e(e, all_e, AgentOf(x, e) & PatientOf(y, e) & pe_likes(e)))))",
        )?;

        let mary = RootedLambdaPool::parse("a_Mary")?;
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
        let pool = RootedLambdaPool::parse(
            "some_e(x0, all_e, AgentOf(a_1, x0) & PatientOf(a_0, x0) & pe_0(x0))",
        )?;
        assert_eq!(
            pool.to_string(),
            "some_e(x, all_e, AgentOf(a_1, x) & PatientOf(a_0, x) & pe_0(x))"
        );
        let likes = RootedLambdaPool::parse(
            "lambda e x lambda e y (some(e, all_a, AgentOf(e, x) & PatientOf(e, y) & pe_likes(y)))",
        )?;

        let s =
            "lambda e x lambda e y some(z, all_a, AgentOf(z, x) & PatientOf(z, y) & pe_likes(y))";
        assert_eq!(likes.to_string(), s,);
        let likes2 = RootedLambdaPool::parse(s)?;
        assert_eq!(likes, likes2);

        Ok(())
    }

    #[test]
    fn fancy_quantification_reduction() -> anyhow::Result<()> {
        let pool = RootedLambdaPool::parse("every_e(x0,pe_0(x0) & pe_1(x0), pe_2(x0))")?;
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

        dbg!(&pool);
        assert!(pool.into_pool()?.run(&scenario, None)?.try_into()?);

        let pool = RootedLambdaPool::parse("every_e(x0, pe_0(x0) & pe_1(x0), pe_2(x0))")?;

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

        dbg!(&pool);
        assert!(pool.into_pool()?.run(&scenario, None)?.try_into()?);

        let pool =
            RootedLambdaPool::parse("every_e(x, pe_laughs, every(y, pe_sleeps(x), pa_woman(y)))")?;
        println!("{}", pool.into_pool()?);
        Ok(())
    }

    #[test]
    fn conjoining_check() -> anyhow::Result<()> {
        let tall = RootedLambdaPool::parse("lambda a x pa_tall(x)")?;
        let man = RootedLambdaPool::parse("lambda a x pa_man(x)")?;

        let mut tall_man = tall.conjoin(man)?;
        tall_man.reduce()?;
        let weird = RootedLambdaPool::parse("weird#<a,t>")?;
        let man = RootedLambdaPool::parse("lambda a x pa_man(x)")?;
        let weird_man = weird.conjoin(man)?;
        assert_eq!(format!("{tall_man}"), "lambda a x pa_tall(x) & pa_man(x)");
        assert_eq!(
            format!("{weird_man}"),
            "lambda a x weird#<a,t>(x) & pa_man(x)"
        );

        let voice = RootedLambdaPool::parse("lambda a x lambda e y AgentOf(x, y)")?;
        let run = RootedLambdaPool::parse("lambda e x pe_run(x)")?;

        let mut agent_run = voice.raised_conjoin(run)?;
        agent_run.reduce()?;
        assert_eq!(
            format!("{agent_run}"),
            "lambda a x lambda e y AgentOf(x, y) & pe_run(y)"
        );
        let voice = RootedLambdaPool::parse("lambda a x lambda e y AgentOf(x, y)")?;
        let run = RootedLambdaPool::parse("lambda e x pe_run(x)")?;

        let mut agent_run = run.raised_conjoin(voice)?;
        agent_run.reduce()?;
        assert_eq!(
            format!("{agent_run}"),
            "lambda a x lambda e y AgentOf(x, y) & pe_run(y)"
        );
        Ok(())
    }

    #[test]
    fn alpha_check() -> anyhow::Result<()> {
        let everyone = RootedLambdaPool::parse("lambda <a,t> P (every(x, all_a, P(x)))")?;
        let someone = RootedLambdaPool::parse("lambda <a,t> P (some(x, all_a, P(x)))")?;
        let mut likes = RootedLambdaPool::parse(
            "lambda a x (lambda a y (some_e(e, all_e, AgentOf(y, e)&pe_likes(e)&PatientOf(x, e))))",
        )?;

        likes.apply_new_free_variable(FreeVar::Anonymous(0))?;
        let mut sentence = likes.merge(someone).unwrap();
        sentence.lambda_abstract_free_variable(FreeVar::Anonymous(0), LambdaType::A, true)?;
        let mut sentence = sentence.merge(everyone).unwrap();
        sentence.reduce()?;
        assert_eq!(
            sentence.to_string(),
            "every(x, all_a, some(y, all_a, some_e(z, all_e, AgentOf(y, z) & pe_likes(z) & PatientOf(x, z))))"
        );

        let everyone = RootedLambdaPool::parse("lambda <a,t> P (every(x, all_a, P(x)))")?;
        let someone = RootedLambdaPool::parse("lambda <a,t> P (some(x, all_a, P(x)))")?;
        let mut likes = RootedLambdaPool::parse(
            "lambda a x (lambda a y ( some_e(e, all_e, AgentOf(y, e)&pe_likes(e)&PatientOf(x, e)) | some(w, all_a, every_e(e, all_e, AgentOf(y, e)&pe_likes(e)&PatientOf(x, e)))))",
        )?;

        likes.apply_new_free_variable(FreeVar::Anonymous(0))?;
        let mut sentence = likes.merge(someone).unwrap();
        sentence.lambda_abstract_free_variable(FreeVar::Anonymous(0), LambdaType::A, true)?;
        let mut sentence = sentence.merge(everyone).unwrap();
        sentence.reduce()?;
        assert_eq!(
            sentence.to_string(),
            "every(x, all_a, some(y, all_a, some_e(z, all_e, AgentOf(y, z) & pe_likes(z) & PatientOf(x, z)) | some(z, all_a, every_e(a, all_e, AgentOf(y, a) & pe_likes(a) & PatientOf(x, a)))))"
        );
        Ok(())
    }
}
