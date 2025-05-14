use super::{
    ActorOrEvent, BinOp, Constant, Expr, ExprPool, ExprRef, LanguageExpression, MonOp, Quantifier,
    Variable,
};
use crate::{
    Actor, Entity,
    lambda::{
        Bvar, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool, RootedLambdaPool,
        types::LambdaType,
    },
};
use rand::{
    Rng,
    distr::{Distribution, weighted::WeightedIndex},
    seq::IteratorRandom,
};

pub mod mutations;

impl LambdaLanguageOfThought for Expr {
    type Pool = LanguageExpression;
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

    fn get_type(&self) -> LambdaType {
        match self {
            Expr::Quantifier { .. } => LambdaType::T,
            Expr::Variable(Variable::Event(_)) => LambdaType::E,
            Expr::Variable(Variable::Actor(_)) => LambdaType::A,
            Expr::Actor(_) => LambdaType::A,
            Expr::Event(_) => LambdaType::E,
            Expr::Binary(bin, ..) => match bin {
                BinOp::AgentOf | BinOp::PatientOf | BinOp::And | BinOp::Or => LambdaType::T,
            },
            Expr::Unary(mon_op, _) => match mon_op {
                MonOp::Property(_, _) | MonOp::Tautology | MonOp::Contradiction | MonOp::Not => {
                    LambdaType::T
                }
            },
            Expr::Constant(constant) => match constant {
                Constant::Everyone | Constant::Property(_, ActorOrEvent::Actor) => LambdaType::at(),
                Constant::EveryEvent | Constant::Property(_, ActorOrEvent::Event) => {
                    LambdaType::et()
                }
                Constant::Contradiction | Constant::Tautology => LambdaType::T,
            },
        }
    }

    fn to_pool(pool: Vec<Self>, root: LambdaExprRef) -> Self::Pool {
        LanguageExpression {
            pool: ExprPool(pool),
            start: ExprRef(root.0),
        }
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
}

impl std::fmt::Display for RootedLambdaPool<Expr> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let string = self.string(self.root(), 0);
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

impl RootedLambdaPool<Expr> {
    fn string(&self, expr: LambdaExprRef, lambda_depth: usize) -> String {
        match self.get(expr) {
            LambdaExpr::Lambda(child, lambda_type) => {
                format!(
                    "lambda {} {}_l ({})",
                    lambda_type,
                    to_var(lambda_depth),
                    self.string(*child, lambda_depth + 1)
                )
            }
            LambdaExpr::BoundVariable(bvar, _) => format!("{}_l", to_var(lambda_depth - bvar - 1)),
            LambdaExpr::FreeVariable(fvar, _) => format!("{fvar}_f"),
            LambdaExpr::Application {
                subformula,
                argument,
            } => format!(
                "({})({})",
                self.string(*subformula, lambda_depth),
                self.string(*argument, lambda_depth)
            ),
            LambdaExpr::LanguageOfThoughtExpr(x) => match x {
                Expr::Quantifier {
                    quantifier,
                    var,
                    restrictor,
                    subformula,
                } => format!(
                    "{}({},{},{})",
                    quantifier,
                    var.to_var_string(),
                    self.string(LambdaExprRef(restrictor.0), lambda_depth),
                    self.string(LambdaExprRef(subformula.0), lambda_depth)
                ),
                Expr::Variable(variable) => variable.to_var_string(),
                Expr::Actor(a) => format!("a{a}"),
                Expr::Event(e) => format!("e{e}"),
                Expr::Binary(bin_op, x, y) => match bin_op {
                    BinOp::AgentOf | BinOp::PatientOf => {
                        format!(
                            "{bin_op}({},{})",
                            self.string(LambdaExprRef(x.0), lambda_depth),
                            self.string(LambdaExprRef(y.0), lambda_depth)
                        )
                    }

                    BinOp::And | BinOp::Or => {
                        format!(
                            "({} {bin_op} {})",
                            self.string(LambdaExprRef(x.0), lambda_depth),
                            self.string(LambdaExprRef(y.0), lambda_depth)
                        )
                    }
                },
                Expr::Unary(mon_op, arg) => {
                    format!(
                        "{mon_op}({})",
                        self.string(LambdaExprRef(arg.0), lambda_depth)
                    )
                }
                Expr::Constant(constant) => format!("{constant}"),
            },
        }
    }
}
#[cfg(test)]
mod test {
    use super::to_var;

    use crate::{
        LabelledScenarios,
        lambda::{RootedLambdaPool, types::LambdaType},
        lot_parser,
    };
    use chumsky::prelude::*;
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    #[test]
    fn type_checking() -> anyhow::Result<()> {
        let labels = LabelledScenarios::default();
        let mut label_state = extra::SimpleState(labels.clone());
        let parser = lot_parser().then_ignore(end());
        let john = parser.parse_with_state("a_j", &mut label_state).unwrap();
        let likes = parser
            .parse_with_state(
                "lambda e x ((lambda e y (some(e, all_e, AgentOf(e, x) & PatientOf(e,y) & p_likes(e)))))",
                &mut label_state,
            )
            .unwrap();

        let mary = parser.parse_with_state("a_m", &mut label_state).unwrap();
        let phi = mary.clone().merge(likes.clone()).unwrap();
        let mut phi = phi.merge(john.clone()).unwrap();
        phi.reduce()?;
        let pool = phi.into_pool()?;
        assert_eq!(
            "some(x,all_e,((AgentOf(x,a1) & PatientOf(x,a0)) & p0(x)))",
            pool.to_string()
        );
        let phi = likes.merge(mary).unwrap();
        let mut phi = john.merge(phi).unwrap();
        phi.reduce()?;
        let pool = phi.into_pool()?;
        assert_eq!(
            "some(x,all_e,((AgentOf(x,a1) & PatientOf(x,a0)) & p0(x)))",
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
        let labels = LabelledScenarios::default();
        let mut label_state = extra::SimpleState(labels.clone());
        let parser = lot_parser().then_ignore(end());
        let pool = parser
            .parse_with_state(
                "some(x0,all_e,((AgentOf(x0,a1) & PatientOf(x0,a0)) & p0(x0)))",
                &mut label_state,
            )
            .unwrap();
        assert_eq!(
            pool.to_string(),
            "some(x,all_e,((AgentOf(x,a1) & PatientOf(x,a0)) & p0(x)))"
        );
        let likes = parser
            .parse_with_state(
                "lambda e x ((lambda e y (some(e, all_e, AgentOf(e, x) & PatientOf(e,y) & p_likes(e)))))",
                &mut label_state,
            )
            .unwrap();

        let s = "lambda e x_l (lambda e y_l (some(x,all_e,((AgentOf(x,x_l) & PatientOf(x,y_l)) & p0(x)))))";
        assert_eq!(likes.to_string(), s,);
        let likes2 = parser.parse_with_state(s, &mut label_state).unwrap();
        assert_eq!(likes, likes2);

        Ok(())
    }

    #[test]
    fn randomness() -> anyhow::Result<()> {
        let mut rng = ChaCha8Rng::seed_from_u64(2);
        let actors = [0, 1];
        let properties = [0, 1, 2, 3];
        for _ in 0..100 {
            let t = LambdaType::random(&mut rng);
            let pool =
                RootedLambdaPool::random_expr(t.clone(), &actors, &properties, None, &mut rng);
            println!("{}: {}", t, pool);
            assert_eq!(t, pool.get_type()?);
            let pool = pool.resample_from_expr(&actors, &properties, None, &mut rng);
            println!("{}: {}", t, pool);
            assert_eq!(t, pool.get_type()?);
        }
        Ok(())
    }
}
