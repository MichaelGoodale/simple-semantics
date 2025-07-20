use super::*;

//Need to add applications
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum UnbuiltExpr<'src, 't> {
    Quantifier(Quantifier, ActorOrEvent),
    Variable(Variable),
    Actor(Actor<'src>),
    Event(Event),
    Binary(BinOp),
    Unary(MonOp<'src>),
    Constant(Constant<'src>),
    Lambda(&'t LambdaType, &'t LambdaType),
    BoundVariable(Bvar, &'t LambdaType),
}

impl UnbuiltExpr<'_, '_> {
    pub fn get_expression_type(&self) -> ExpressionType {
        match self {
            UnbuiltExpr::Quantifier(_, actor_or_event) => ExpressionType {
                output: LambdaType::t().clone(),
                arguments: vec![
                    match actor_or_event {
                        ActorOrEvent::Actor => LambdaType::at().clone(),
                        ActorOrEvent::Event => LambdaType::et().clone(),
                    },
                    LambdaType::t().clone(),
                ],
            },
            UnbuiltExpr::Variable(var) => ExpressionType::new_no_args(match var {
                Variable::Actor(_) => LambdaType::a().clone(),
                Variable::Event(_) => LambdaType::e().clone(),
            }),
            UnbuiltExpr::Actor(_) => ExpressionType::new_no_args(LambdaType::a().clone()),
            UnbuiltExpr::Event(_) => ExpressionType::new_no_args(LambdaType::e().clone()),
            UnbuiltExpr::Binary(b) => match b {
                BinOp::AgentOf | BinOp::PatientOf => ExpressionType {
                    output: LambdaType::t().clone(),
                    arguments: vec![LambdaType::a().clone(), LambdaType::e().clone()],
                },
                BinOp::And | BinOp::Or => ExpressionType {
                    output: LambdaType::t().clone(),
                    arguments: vec![LambdaType::t().clone(), LambdaType::t().clone()],
                },
            },
            UnbuiltExpr::Unary(m) => match m {
                MonOp::Not => ExpressionType {
                    output: LambdaType::t().clone(),
                    arguments: vec![LambdaType::t().clone()],
                },
                MonOp::Property(_, actor_or_event) => ExpressionType {
                    output: LambdaType::t().clone(),
                    arguments: vec![match actor_or_event {
                        ActorOrEvent::Actor => LambdaType::a().clone(),
                        ActorOrEvent::Event => LambdaType::e().clone(),
                    }],
                },
            },
            UnbuiltExpr::Constant(c) => match c {
                Constant::Everyone => ExpressionType::new_no_args(LambdaType::at().clone()),
                Constant::EveryEvent => ExpressionType::new_no_args(LambdaType::et().clone()),
                Constant::Contradiction | Constant::Tautology => {
                    ExpressionType::new_no_args(LambdaType::t().clone())
                }
                Constant::Property(_, actor_or_event) => {
                    ExpressionType::new_no_args(match actor_or_event {
                        ActorOrEvent::Actor => LambdaType::at().clone(),
                        ActorOrEvent::Event => LambdaType::et().clone(),
                    })
                }
            },
            UnbuiltExpr::Lambda(lhs, rhs) => ExpressionType {
                output: (*rhs).clone(),
                arguments: vec![(*lhs).clone()],
            },
            UnbuiltExpr::BoundVariable(_, lambda_type) => {
                ExpressionType::new_no_args((*lambda_type).clone())
            }
        }
    }
}

pub fn add_expr<'src, 'pool>(
    e: UnbuiltExpr<'src, 'pool>,
    pos: u32,
    mut context: Context<'pool>,
    fresher: &mut Fresher,
    pool: &mut Vec<Option<LambdaExpr<Expr<'src>>>>,
) -> Vec<(u32, &'pool LambdaType, Context<'pool>)> {
    let cur_size = pool.len() as u32 - 1;
    let mut children = vec![];
    let expr = match e {
        UnbuiltExpr::Quantifier(quantifier, actor_or_event) => {
            children.extend_from_slice(&[
                (
                    cur_size + 1,
                    match actor_or_event {
                        ActorOrEvent::Actor => LambdaType::at(),
                        ActorOrEvent::Event => LambdaType::et(),
                    },
                ),
                (cur_size + 2, LambdaType::t()),
            ]);
            let var = context.add_var(fresher.fresh(actor_or_event));
            LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                quantifier,
                var_type: var,
                restrictor: ExprRef(cur_size + 1),
                subformula: ExprRef(cur_size + 2),
            })
        }
        UnbuiltExpr::Variable(var) => LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(var)),
        UnbuiltExpr::Event(event) => LambdaExpr::LanguageOfThoughtExpr(Expr::Event(event)),
        UnbuiltExpr::Actor(actor) => LambdaExpr::LanguageOfThoughtExpr(Expr::Actor(actor)),
        UnbuiltExpr::Binary(bin_op) => {
            children.extend_from_slice(&match bin_op {
                BinOp::AgentOf | BinOp::PatientOf => [
                    (cur_size + 1, LambdaType::a()),
                    (cur_size + 2, LambdaType::e()),
                ],
                BinOp::And | BinOp::Or => [
                    (cur_size + 1, LambdaType::t()),
                    (cur_size + 2, LambdaType::t()),
                ],
            });
            LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(
                bin_op,
                ExprRef(cur_size + 1),
                ExprRef(cur_size + 2),
            ))
        }
        UnbuiltExpr::Unary(mon_op) => {
            children.push(match mon_op {
                MonOp::Property(_, ActorOrEvent::Actor) => (cur_size + 1, LambdaType::a()),
                MonOp::Property(_, ActorOrEvent::Event) => (cur_size + 1, LambdaType::e()),
                MonOp::Not => (cur_size + 1, LambdaType::t()),
            });
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(mon_op, ExprRef(cur_size + 1)))
        }
        UnbuiltExpr::Constant(constant) => {
            LambdaExpr::LanguageOfThoughtExpr(Expr::Constant(constant))
        }
        UnbuiltExpr::Lambda(lhs, rhs) => {
            children.push((cur_size + 1, rhs));
            context.add_lambda(lhs);
            LambdaExpr::Lambda(LambdaExprRef(cur_size + 1), lhs.clone())
        }
        UnbuiltExpr::BoundVariable(bvar, lambda_type) => {
            LambdaExpr::BoundVariable(bvar, lambda_type.clone())
        }
    };

    pool[pos as usize] = Some(expr);
    pool.resize(pool.len() + children.len(), None);
    children
        .into_iter()
        .map(|(a, b)| (a, b, context.clone()))
        .collect()
}

#[derive(Debug, Copy, Clone, Default)]
pub struct Fresher(u32);

impl Fresher {
    pub fn fresh(&mut self, actor_or_event: ActorOrEvent) -> Variable {
        self.0 += 1;
        actor_or_event.to_variable(self.0)
    }

    pub fn new_rooted(pool: &RootedLambdaPool<Expr>) -> Self {
        Fresher(
            pool.pool
                .0
                .iter()
                .filter_map(|x| match x {
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(v))
                    | LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier { var_type: v, .. }) => {
                        Some(v.id())
                    }
                    _ => None,
                })
                .max()
                .unwrap_or(0),
        )
    }

    pub fn new(pool: &[Option<LambdaExpr<Expr>>]) -> Self {
        Fresher(
            pool.iter()
                .filter_map(|x| match x {
                    Some(LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(v)))
                    | Some(LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                        var_type: v,
                        ..
                    })) => Some(v.id()),
                    _ => None,
                })
                .max()
                .unwrap_or(0),
        )
    }
}
