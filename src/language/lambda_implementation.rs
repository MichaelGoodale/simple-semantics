use ahash::HashMap;
use chumsky::prelude::*;
use std::iter::empty;
use thiserror::Error;

use super::{
    ActorOrEvent, BinOp, Constant, Expr, ExprPool, ExprRef, LambdaParseError, LanguageExpression,
    MonOp, Variable, lot_parser,
};
use crate::{
    LabelledScenarios,
    lambda::{
        LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool, ReductionError,
        RootedLambdaPool, types::LambdaType,
    },
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

impl LambdaLanguageOfThought for Expr {
    type Pool = LanguageExpression;
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
        //e.g. some(x, lambda a y (pa0(y) | pa1(y)), pa3(x)) -> some(x, pa0(x) | pa1(x), pa3(x))
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

    fn get_arguments<'a>(&'a self) -> Box<dyn Iterator<Item = LambdaType> + 'a> {
        match self {
            Expr::Quantifier {
                var: Variable::Actor(_),
                ..
            } => Box::new([LambdaType::at().clone(), LambdaType::t().clone()].into_iter()),
            Expr::Quantifier {
                var: Variable::Event(_),
                ..
            } => Box::new([LambdaType::et().clone(), LambdaType::t().clone()].into_iter()),
            Expr::Variable(Variable::Event(_))
            | Expr::Variable(Variable::Actor(_))
            | Expr::Actor(_)
            | Expr::Event(_)
            | Expr::Constant(_) => Box::new(empty()),
            Expr::Binary(BinOp::AgentOf, ..) | Expr::Binary(BinOp::PatientOf, ..) => {
                Box::new([LambdaType::a().clone(), LambdaType::e().clone()].into_iter())
            }
            Expr::Binary(BinOp::Or, ..) | Expr::Binary(BinOp::And, ..) => {
                Box::new([LambdaType::t().clone(), LambdaType::t().clone()].into_iter())
            }
            Expr::Unary(mon_op, _) => match mon_op {
                MonOp::Property(_, ActorOrEvent::Actor) => {
                    Box::new([LambdaType::a().clone()].into_iter())
                }
                MonOp::Property(_, ActorOrEvent::Event) => {
                    Box::new([LambdaType::a().clone()].into_iter())
                }

                MonOp::Tautology | MonOp::Contradiction | MonOp::Not => {
                    Box::new([LambdaType::t().clone()].into_iter())
                }
            },
        }
    }
}

impl std::fmt::Display for RootedLambdaPool<Expr> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let string = self.string(self.root(), VarContext::default(), None);
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
struct VarContext {
    vars: HashMap<Var, usize>,
    depth: usize,
}

impl VarContext {
    fn inc_depth(mut self) -> (Self, String) {
        let n_var = self.vars.len();
        self.vars.insert(Var::Depth(self.depth), n_var);
        self.depth += 1;
        (self, to_var(n_var))
    }

    fn lambda_var(&self, bvar: usize) -> String {
        to_var(*self.vars.get(&Var::Depth(self.depth - bvar - 1)).unwrap())
    }
    fn q_var(&self, var: Variable) -> String {
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

    fn add_qvar(mut self, x: Variable) -> (Self, String) {
        let n_var = self.vars.len();
        self.vars.insert(Var::Quantifier(x), n_var);
        (self, to_var(n_var))
    }
}

impl From<LanguageExpression> for RootedLambdaPool<Expr> {
    fn from(value: LanguageExpression) -> Self {
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

impl LanguageExpression {
    pub fn to_labeled_string(&self, labels: &LabelledScenarios) -> String {
        let x: RootedLambdaPool<Expr> = self.clone().into();
        x.string(x.root(), VarContext::default(), Some(labels))
    }
}

impl RootedLambdaPool<Expr> {
    pub fn parse(s: &str, labels: &mut LabelledScenarios) -> Result<Self, LambdaParseError> {
        lot_parser::<extra::Err<Rich<_>>>()
            .parse(s)
            .into_result()?
            .to_pool(labels)
    }

    pub fn to_labeled_string(&self, labels: &LabelledScenarios) -> String {
        self.string(self.root(), VarContext::default(), Some(labels))
    }

    fn string(
        &self,
        expr: LambdaExprRef,
        c: VarContext,
        labels: Option<&LabelledScenarios>,
    ) -> String {
        match self.get(expr) {
            LambdaExpr::Lambda(child, lambda_type) => {
                let (c, var) = c.inc_depth();
                format!(
                    "lambda {} {} ({})",
                    lambda_type,
                    var,
                    self.string(*child, c, labels)
                )
            }
            LambdaExpr::BoundVariable(bvar, _) => c.lambda_var(*bvar),
            LambdaExpr::FreeVariable(fvar, t) => {
                if let Some(x) = labels {
                    x.from_fvar(*fvar)
                        .map(|x| format!("{x}#{t}"))
                        .unwrap_or_else(|| format!("{fvar}#{t}"))
                } else {
                    format!("{fvar}#{t}")
                }
            }

            LambdaExpr::Application {
                subformula,
                argument,
            } => format!(
                "({})({})",
                self.string(*subformula, c.clone(), labels),
                self.string(*argument, c, labels)
            ),
            LambdaExpr::LanguageOfThoughtExpr(x) => match x {
                Expr::Quantifier {
                    quantifier,
                    var,
                    restrictor,
                    subformula,
                } => {
                    let (c, var_string) = c.add_qvar(*var);
                    format!(
                        "{}{}({},{},{})",
                        quantifier,
                        match var {
                            Variable::Actor(_) => "",
                            Variable::Event(_) => "_e",
                        },
                        var_string,
                        self.string(LambdaExprRef(restrictor.0), c.clone(), labels),
                        self.string(LambdaExprRef(subformula.0), c, labels)
                    )
                }
                Expr::Variable(variable) => c.q_var(*variable),
                Expr::Actor(a) => {
                    if let Some(x) = labels {
                        x.from_actor(*a)
                            .map(|x| format!("a_{x}"))
                            .unwrap_or_else(|| format!("a{a}"))
                    } else {
                        format!("a{a}")
                    }
                }
                Expr::Event(e) => format!("e{e}"),
                Expr::Binary(bin_op, x, y) => match bin_op {
                    BinOp::AgentOf | BinOp::PatientOf => {
                        format!(
                            "{bin_op}({},{})",
                            self.string(LambdaExprRef(x.0), c.clone(), labels),
                            self.string(LambdaExprRef(y.0), c, labels)
                        )
                    }

                    BinOp::And | BinOp::Or => {
                        format!(
                            "({} {bin_op} {})",
                            self.string(LambdaExprRef(x.0), c.clone(), labels),
                            self.string(LambdaExprRef(y.0), c, labels)
                        )
                    }
                },
                Expr::Unary(mon_op, arg) => {
                    let mon_s = match (mon_op, labels) {
                        (MonOp::Property(p, t), Some(labels)) => labels
                            .from_prop(*p)
                            .map(|x| format!("p{t}_{x}"))
                            .unwrap_or_else(|| format!("{}", MonOp::Property(*p, *t))),
                        _ => mon_op.to_string(),
                    };
                    format!("{mon_s}({})", self.string(LambdaExprRef(arg.0), c, labels))
                }
                Expr::Constant(constant) => match (constant, labels) {
                    (Constant::Property(p, t), Some(labels)) => labels
                        .from_prop(*p)
                        .map(|x| format!("p{t}_{x}"))
                        .unwrap_or_else(|| format!("{}", Constant::Property(*p, *t))),
                    _ => format!("{constant}"),
                },
            },
        }
    }
}
#[cfg(test)]
mod test {
    use super::to_var;

    use crate::{
        Entity, LabelledScenarios, Scenario, ThetaRoles, lambda::RootedLambdaPool,
        language::lot_parser, parse_executable,
    };

    use ahash::HashMap;
    use chumsky::prelude::*;

    #[test]
    fn fancy_printing() -> anyhow::Result<()> {
        let mut properties = HashMap::default();

        properties.insert(1, vec![Entity::Actor(1)]);
        properties.insert(4, vec![Entity::Actor(0), Entity::Actor(1)]);

        let simple_scenario = Scenario {
            question: None,
            actors: vec![0, 1],
            thematic_relations: vec![
                ThetaRoles {
                    agent: Some(0),
                    patient: Some(0),
                },
                ThetaRoles {
                    agent: Some(1),
                    patient: Some(0),
                },
            ],
            properties,
        };

        let actor_labels =
            HashMap::from_iter([("John", 1), ("Mary", 0)].map(|(x, y)| (x.to_string(), y)));
        let property_labels =
            HashMap::from_iter([("Red", 1), ("Blue", 4)].map(|(x, y)| (x.to_string(), y)));
        let mut labels = LabelledScenarios {
            scenarios: vec![simple_scenario.clone()],
            actor_labels,
            property_labels,
            free_variables: HashMap::default(),
            sentences: vec![],
            lemmas: vec![],
        };

        for statement in [
            "~(AgentOf(a_John,e0))",
            "(pa_Red(a_John) & ~(pa_Red(a_Mary)))",
            "every(x,all_a,pa_Blue(x))",
            "every(x,pa_Blue,pa_Blue(x))",
            "every(x,pa5,pa10(a59))",
            "every_e(x,all_e,PatientOf(a_Mary,x))",
        ] {
            let expression = parse_executable(statement, &mut labels)?;
            assert_eq!(expression.to_labeled_string(&labels), statement);
        }
        for s in ["(cool#<a,t>)(a_John)", "(bad#<a,t>)(man#a)"] {
            let p = RootedLambdaPool::parse(s, &mut labels)?;
            assert_eq!(p.to_labeled_string(&labels), s);
        }

        Ok(())
    }

    #[test]
    fn type_checking() -> anyhow::Result<()> {
        let mut labels = LabelledScenarios::default();
        let parser = lot_parser::<extra::Err<Rich<_>>>().then_ignore(end());
        let john = parser.parse("a_j").unwrap().to_pool(&mut labels)?;
        let likes = parser
            .parse(
                "lambda a x ((lambda a y (some_e(e, all_e, AgentOf(e, x) & PatientOf(e,y) & pe_likes(e)))))",
            )
            .unwrap().to_pool(&mut labels)?;

        let mary = parser.parse("a_m").unwrap().to_pool(&mut labels)?;
        let phi = mary.clone().merge(likes.clone()).unwrap();
        let mut phi = phi.merge(john.clone()).unwrap();
        phi.reduce()?;
        let pool = phi.into_pool()?;
        assert_eq!(
            "some_e(x,all_e,((AgentOf(x,a1) & PatientOf(x,a0)) & pe0(x)))",
            pool.to_string()
        );
        let phi = likes.merge(mary).unwrap();
        let mut phi = john.merge(phi).unwrap();
        phi.reduce()?;
        let pool = phi.into_pool()?;
        assert_eq!(
            "some_e(x,all_e,((AgentOf(x,a1) & PatientOf(x,a0)) & pe0(x)))",
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
        let mut labels = LabelledScenarios::default();
        let parser = lot_parser::<extra::Err<Rich<_>>>().then_ignore(end());
        let pool = parser
            .parse("some_e(x0,all_e,((AgentOf(x0,a1) & PatientOf(x0,a0)) & pe0(x0)))")
            .unwrap()
            .to_pool(&mut labels)?;
        assert_eq!(
            pool.to_string(),
            "some_e(x,all_e,((AgentOf(x,a1) & PatientOf(x,a0)) & pe0(x)))"
        );
        let likes = parser
            .parse(
                "lambda e x ((lambda e y (some(e, all_e, AgentOf(x, e) & PatientOf(y,e) & pe_likes(e)))))",
            )
            .unwrap().to_pool(&mut labels)?;

        let s =
            "lambda e x (lambda e y (some(z,all_e,((AgentOf(x,z) & PatientOf(y,z)) & pe0(z)))))";
        assert_eq!(likes.to_string(), s,);
        let likes2 = parser.parse(s).unwrap().to_pool(&mut labels)?;
        assert_eq!(likes, likes2);

        Ok(())
    }

    #[test]
    fn fancy_quantification_reduction() -> anyhow::Result<()> {
        let mut labels = LabelledScenarios::default();
        let parser = lot_parser::<extra::Err<Rich<_>>>().then_ignore(end());
        let pool = parser
            .parse("every_e(x0,pe0(x0) & pe1(x0), pe2(x0))")
            .unwrap()
            .to_pool(&mut labels)?;
        let scenario = Scenario::new(
            vec![],
            vec![ThetaRoles::default(); 5],
            [
                (0, vec![Entity::Event(1), Entity::Event(2)]),
                (1, vec![Entity::Event(0), Entity::Event(1)]),
                (2, vec![Entity::Event(1)]),
            ]
            .into_iter()
            .collect(),
        );

        assert!(pool.into_pool()?.run(&scenario)?.try_into()?);

        let pool = parser
            .parse("every_e(x0, lambda e x (pe0(x) & pe1(x)), pe2(x0))")
            .unwrap()
            .to_pool(&mut labels)?;

        let scenario = Scenario::new(
            vec![],
            vec![ThetaRoles::default(); 5],
            [
                (0, vec![Entity::Event(1), Entity::Event(2)]),
                (1, vec![Entity::Event(0), Entity::Event(1)]),
                (2, vec![Entity::Event(1)]),
            ]
            .into_iter()
            .collect(),
        );

        assert!(pool.into_pool()?.run(&scenario)?.try_into()?);

        Ok(())
    }
}
