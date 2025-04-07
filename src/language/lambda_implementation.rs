use super::{BinOp, Constant, Expr, ExprPool, ExprRef, LanguageExpression, MonOp, Variable};
use crate::lambda::{
    types::LambdaType, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool,
};

impl LambdaLanguageOfThought for Expr {
    fn get_children(&self) -> impl Iterator<Item = LambdaExprRef> {
        match self {
            Expr::Quantifier {
                restrictor,
                subformula,
                ..
            } => vec![restrictor, subformula],
            Expr::Binary(_, x, y) => vec![x, y],
            Expr::Unary(_, x) => vec![x],
            Expr::Constant(_) | Expr::Entity(_) | Expr::Variable(_) => vec![],
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
            Expr::Variable(_) | Expr::Entity(_) | Expr::Constant(_) => (),
        }
    }

    fn get_type(&self) -> LambdaType {
        match self {
            Expr::Quantifier { .. } => LambdaType::T,
            Expr::Variable(_) => LambdaType::E,
            Expr::Entity(_) => LambdaType::E,
            Expr::Binary(bin, ..) => match bin {
                BinOp::AgentOf | BinOp::PatientOf => LambdaType::eet(),
                BinOp::And | BinOp::Or => LambdaType::Composition(
                    Box::new(LambdaType::T),
                    Box::new(LambdaType::Composition(
                        Box::new(LambdaType::T),
                        Box::new(LambdaType::T),
                    )),
                ),
            },
            Expr::Unary(mon_op, _) => match mon_op {
                MonOp::Property(_) | MonOp::Tautology | MonOp::Contradiction => LambdaType::et(),
                MonOp::Not => {
                    LambdaType::Composition(Box::new(LambdaType::T), Box::new(LambdaType::T))
                }
            },
            Expr::Constant(constant) => match constant {
                Constant::Everyone | Constant::EveryEvent | Constant::Property(_) => {
                    LambdaType::et()
                }
                Constant::Contradiction | Constant::Tautology => LambdaType::T,
            },
        }
    }

    type Pool = LanguageExpression;

    fn to_pool(pool: Vec<Self>, root: LambdaExprRef) -> Self::Pool {
        LanguageExpression {
            pool: ExprPool(pool),
            start: ExprRef(root.0),
        }
    }

    fn alpha_reduce(a: &mut LambdaPool<Self>, b: &mut LambdaPool<Self>) {
        let mut max_var = 0;
        for x in a.iter_mut() {
            match x {
                LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier { var: v, .. })
                | LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(v)) => {
                    let v = v.0;
                    if v > max_var {
                        max_var = v;
                    }
                }
                _ => (),
            }
        }

        for x in b.iter_mut() {
            match x {
                LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier { var: v, .. })
                | LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(v)) => {
                    *v = Variable(max_var + v.0 + 1);
                }
                _ => (),
            }
        }
    }
}
