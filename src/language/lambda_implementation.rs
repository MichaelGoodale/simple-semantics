use super::{
    BinOp, Constant, Expr, ExprPool, ExprRef, LanguageExpression, MonOp, Quantifier, Variable,
};
use crate::{
    Entity,
    lambda::{
        Bvar, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool, RootedLambdaPool,
        types::LambdaType,
    },
};
use rand::{
    Rng,
    distr::{Distribution, weighted::WeightedIndex},
    seq::{IndexedRandom, IteratorRandom},
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
                BinOp::AgentOf | BinOp::PatientOf | BinOp::And | BinOp::Or => LambdaType::T,
            },
            Expr::Unary(mon_op, _) => match mon_op {
                MonOp::Property(_) | MonOp::Tautology | MonOp::Contradiction | MonOp::Not => {
                    LambdaType::T
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
        let mut max_var = None;
        for x in a.iter_mut() {
            match x {
                LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier { var: v, .. })
                | LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(v)) => {
                    if let Some(max_var) = max_var.as_mut() {
                        let v = v.0;
                        if v > *max_var {
                            *max_var = v;
                        }
                    } else {
                        max_var = Some(v.0);
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
                        *v = Variable(max_var + v.0 + 1);
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
                    to_var(var.0 as usize),
                    self.string(LambdaExprRef(restrictor.0), lambda_depth),
                    self.string(LambdaExprRef(subformula.0), lambda_depth)
                ),
                Expr::Variable(variable) => to_var(variable.0 as usize),
                Expr::Entity(entity) => format!("{}", entity),
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

    fn random_expr(
        lambda_type: LambdaType,
        available_actors: &[Entity],
        rng: &mut impl Rng,
    ) -> Self {
        let mut pool = vec![None];

        let context = Context {
            lambdas: vec![],
            available_vars: vec![],
            available_actors,
        };
        let mut fresher = Fresher::default();

        let e = Expr::get_new_from_type(&lambda_type, &context, &mut fresher, rng)
            .unwrap_or(UnbuiltExpr::Lambda(lambda_type));

        let mut stack = add_expr(e, 0, context, &mut pool);

        while let Some((pos, lambda_type, context)) = stack.pop() {
            let e = Expr::get_new_from_type(&lambda_type, &context, &mut fresher, rng)
                .unwrap_or(UnbuiltExpr::Lambda(lambda_type));

            stack.extend(add_expr(e, pos, context, &mut pool));
        }

        let pool = pool.into_iter().collect::<Option<Vec<_>>>().unwrap();
        RootedLambdaPool::new(LambdaPool::from(pool), LambdaExprRef(0))
    }
}

#[derive(Debug, Clone)]
struct Context<'a> {
    lambdas: Vec<LambdaType>,
    available_vars: Vec<(Variable, LambdaType)>,
    available_actors: &'a [Entity],
}

impl Context<'_> {
    fn sample_actor(&self, rng: &mut impl Rng) -> Option<UnbuiltExpr> {
        self.available_actors
            .choose(rng)
            .cloned()
            .map(UnbuiltExpr::Entity)
    }

    fn sample_variable(&self, lambda_type: &LambdaType, rng: &mut impl Rng) -> Option<UnbuiltExpr> {
        let n = self.lambdas.len();
        self.lambdas
            .iter()
            .enumerate()
            .filter_map(|(i, t)| {
                if t == lambda_type {
                    Some(UnbuiltExpr::BoundVariable(n - i - 1, t.clone()))
                } else {
                    None
                }
            })
            .choose(rng)
    }
}

fn add_expr<'a>(
    e: UnbuiltExpr,
    pos: u32,
    mut context: Context<'a>,
    pool: &mut Vec<Option<LambdaExpr<Expr>>>,
) -> Vec<(u32, LambdaType, Context<'a>)> {
    let cur_size = pool.len() as u32 - 1;
    let mut children = vec![];
    let expr = match e {
        UnbuiltExpr::Quantifier { quantifier, var } => {
            children.extend_from_slice(&[
                (cur_size + 1, LambdaType::et()),
                (cur_size + 2, LambdaType::T),
            ]);
            context.available_vars.push((var, LambdaType::E));
            LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                quantifier,
                var,
                restrictor: ExprRef(cur_size + 1),
                subformula: ExprRef(cur_size + 2),
            })
        }
        UnbuiltExpr::Variable(var) => LambdaExpr::LanguageOfThoughtExpr(Expr::Variable(var)),
        UnbuiltExpr::Entity(entity) => LambdaExpr::LanguageOfThoughtExpr(Expr::Entity(entity)),
        UnbuiltExpr::Binary(bin_op) => {
            children.extend_from_slice(&match bin_op {
                BinOp::AgentOf | BinOp::PatientOf => {
                    [(cur_size + 1, LambdaType::E), (cur_size + 2, LambdaType::E)]
                }
                BinOp::And | BinOp::Or => {
                    [(cur_size + 1, LambdaType::T), (cur_size + 2, LambdaType::T)]
                }
            });
            LambdaExpr::LanguageOfThoughtExpr(Expr::Binary(
                bin_op,
                ExprRef(cur_size + 1),
                ExprRef(cur_size + 2),
            ))
        }
        UnbuiltExpr::Unary(mon_op) => {
            children.push(match mon_op {
                MonOp::Property(_) => (cur_size + 1, LambdaType::E),
                MonOp::Not | MonOp::Tautology | MonOp::Contradiction => {
                    (cur_size + 1, LambdaType::T)
                }
            });
            LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(mon_op, ExprRef(cur_size + 1)))
        }
        UnbuiltExpr::Constant(constant) => {
            LambdaExpr::LanguageOfThoughtExpr(Expr::Constant(constant))
        }
        UnbuiltExpr::Lambda(lambda_type) => {
            children.push((cur_size + 1, lambda_type.rhs_clone().unwrap()));
            context.lambdas.push(lambda_type.lhs_clone().unwrap());
            LambdaExpr::Lambda(LambdaExprRef(cur_size + 1), lambda_type)
        }
        UnbuiltExpr::BoundVariable(bvar, lambda_type) => {
            LambdaExpr::BoundVariable(bvar, lambda_type)
        }
    };

    pool[pos as usize] = Some(expr);
    pool.resize(pool.len() + children.len(), None);
    children
        .into_iter()
        .map(|(a, b)| (a, b, context.clone()))
        .collect()
}

//We never do applications since they would be redundant. Bound variables are not yet implemented.
#[derive(Debug, Clone)]
enum UnbuiltExpr {
    Quantifier {
        quantifier: Quantifier,
        var: Variable,
    },
    Variable(Variable),
    Entity(Entity),
    Binary(BinOp),
    Unary(MonOp),
    Constant(Constant),
    Lambda(LambdaType),
    BoundVariable(Bvar, LambdaType),
}

#[derive(Debug, Copy, Clone, Default)]
struct Fresher(u32);

impl Fresher {
    fn fresh(&mut self) -> Variable {
        self.0 += 1;
        Variable(self.0)
    }
}

static WEIGHTED_T: std::sync::LazyLock<WeightedIndex<usize>> =
    std::sync::LazyLock::new(|| WeightedIndex::new([8, 8, 4, 4, 2, 2, 1, 1]).unwrap());

impl Expr {
    fn get_new_from_type(
        lambda_type: &LambdaType,
        context: &Context,
        fresher: &mut Fresher,
        rng: &mut impl Rng,
    ) -> Option<UnbuiltExpr> {
        if lambda_type != &LambdaType::E
            && lambda_type != &LambdaType::T
            && rng.random::<f64>() < 0.2
        {
            return Some(UnbuiltExpr::Lambda(lambda_type.clone()));
        }
        if rng.random::<f64>() < 0.5 {
            let x = context.sample_variable(lambda_type, rng);
            if x.is_some() {
                return x;
            }
        }

        if lambda_type == &LambdaType::et() {
            let mut options = [Constant::Everyone, Constant::EveryEvent]
                .map(UnbuiltExpr::Constant)
                .to_vec();

            let choice = (0..options.len()).choose(rng).unwrap();
            Some(options.remove(choice))
        } else {
            match lambda_type {
                LambdaType::T => {
                    let mut options: Vec<UnbuiltExpr> = vec![
                        UnbuiltExpr::Unary(MonOp::Not),
                        UnbuiltExpr::Unary(MonOp::Property(0)),
                        UnbuiltExpr::Binary(BinOp::AgentOf),
                        UnbuiltExpr::Binary(BinOp::PatientOf),
                        UnbuiltExpr::Binary(BinOp::And),
                        UnbuiltExpr::Binary(BinOp::Or),
                        UnbuiltExpr::Quantifier {
                            quantifier: Quantifier::Existential,
                            var: fresher.fresh(),
                        },
                        UnbuiltExpr::Quantifier {
                            quantifier: Quantifier::Universal,
                            var: fresher.fresh(),
                        },
                    ];

                    let choice = WEIGHTED_T.sample(rng);
                    Some(options.remove(choice))
                }
                LambdaType::E => context.sample_actor(rng),
                _ => None,
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::to_var;
    use std::collections::HashMap;

    use crate::{
        Entity, LabelledScenarios,
        lambda::{RootedLambdaPool, types::LambdaType},
        lot_parser,
    };
    use chumsky::prelude::*;
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    #[test]
    fn type_checking() -> anyhow::Result<()> {
        let labels = LabelledScenarios {
            scenarios: vec![],
            actor_labels: HashMap::default(),
            property_labels: HashMap::default(),
            free_variables: HashMap::default(),
        };
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
        let labels = LabelledScenarios {
            scenarios: vec![],
            actor_labels: HashMap::default(),
            property_labels: HashMap::default(),
            free_variables: HashMap::default(),
        };
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
        let actors = [Entity::Actor(0), Entity::Actor(1)];
        for _ in 0..100 {
            let t = LambdaType::random(&mut rng);
            let pool = RootedLambdaPool::random_expr(t.clone(), &actors, &mut rng);
            println!("{}: {}", t, pool);
        }
        Ok(())
    }
}
