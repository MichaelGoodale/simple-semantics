use super::*;

#[derive(Debug, Clone)]
pub struct Context<'a, 't> {
    lambdas: Vec<&'t LambdaType>,
    available_vars: Vec<Variable>,
    possible_expressions: &'a PossibleExpressions<'t>,
    depth: usize,
}

impl<'a, 't> Context<'a, 't> {
    pub fn new(possible_expressions: &'a PossibleExpressions<'t>) -> Self {
        Context {
            lambdas: vec![],
            available_vars: vec![],
            possible_expressions,
            depth: 0,
        }
    }

    pub fn lambdas(&self) -> &[&LambdaType] {
        &self.lambdas
    }

    pub fn to_owned_lambdas<'c, 'd>(
        self,
        new_lambdas: &'c [LambdaType],
        possible_expressions: &'d PossibleExpressions<'c>,
    ) -> Context<'d, 'c> {
        Context {
            lambdas: new_lambdas.iter().collect(),
            available_vars: self.available_vars,
            possible_expressions,
            depth: self.depth,
        }
    }

    pub fn sample_expr(
        &self,
        lambda_type: &'t LambdaType,
        config: &RandomExprConfig,
        rng: &mut impl Rng,
    ) -> UnbuiltExpr<'t> {
        let (expressions, n_args) = self
            .possible_expressions
            .expr_from_output(lambda_type, self);
        let i = (0..expressions.len()).choose(rng).unwrap();
        expressions[i].clone().into_owned()
    }

    pub fn add_var(&mut self, v: Variable) -> Variable {
        self.available_vars.push(v);
        v
    }
    pub fn add_lambda(&mut self, lhs: &'t LambdaType) {
        self.lambdas.push(lhs);
    }

    pub fn event_variables(&self) -> impl Iterator<Item = UnbuiltExpr<'t>> {
        self.available_vars.iter().filter_map(|x| {
            if matches!(x, Variable::Event(_)) {
                Some(UnbuiltExpr::Variable(*x))
            } else {
                None
            }
        })
    }

    pub fn actor_variables(&self) -> impl Iterator<Item = UnbuiltExpr<'t>> {
        self.available_vars.iter().filter_map(|x| {
            if matches!(x, Variable::Actor(_)) {
                Some(UnbuiltExpr::Variable(*x))
            } else {
                None
            }
        })
    }

    pub fn can_sample_event(&self) -> bool {
        self.available_vars
            .iter()
            .any(|x| matches!(x, Variable::Event(_)))
            | self.lambdas.iter().any(|lam| *lam == LambdaType::e())
    }

    pub fn lambda_variables(
        &self,
        lambda_type: &LambdaType,
    ) -> impl Iterator<Item = UnbuiltExpr<'t>> {
        let n = self.lambdas.len();
        self.lambdas.iter().enumerate().filter_map(move |(i, t)| {
            if *t == lambda_type {
                Some(UnbuiltExpr::BoundVariable(n - i - 1, t))
            } else {
                None
            }
        })
    }
}

pub struct ContextBFSIterator<'a, 'b> {
    pool: &'a RootedLambdaPool<Expr>,
    queue: VecDeque<(LambdaExprRef, Context<'b, 'a>)>,
}

impl<'a, 'b> Iterator for ContextBFSIterator<'a, 'b> {
    type Item = (LambdaExprRef, Context<'b, 'a>);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((x, context)) = self.queue.pop_front() {
            match self.pool.get(x) {
                LambdaExpr::Lambda(x, c) => {
                    let mut context = context.clone();
                    context.lambdas.push(c);
                    context.depth += 1;
                    self.queue.push_back((*x, context))
                }
                LambdaExpr::Application {
                    subformula,
                    argument,
                } => {
                    let mut context = context.clone();
                    context.depth += 1;
                    self.queue.push_back((*subformula, context.clone()));
                    self.queue.push_back((*argument, context));
                }
                LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                    var,
                    restrictor,
                    subformula,
                    ..
                }) => {
                    let mut context = context.clone();
                    context.available_vars.push(*var);
                    context.depth += 1;
                    self.queue
                        .push_back((LambdaExprRef(restrictor.0), context.clone()));
                    self.queue.push_back((LambdaExprRef(subformula.0), context));
                }
                LambdaExpr::LanguageOfThoughtExpr(x) => x.get_children().for_each(|x| {
                    let mut context = context.clone();
                    context.depth += 1;
                    self.queue.push_back((x, context))
                }),
                LambdaExpr::BoundVariable(..) | LambdaExpr::FreeVariable(..) => (),
            }
            Some((x, context))
        } else {
            None
        }
    }
}

impl RootedLambdaPool<Expr> {
    pub fn context_bfs_iter<'a, 'b: 'a>(
        &'a self,
        possible_expressions: &'b PossibleExpressions,
    ) -> ContextBFSIterator<'a, 'b> {
        let mut queue = VecDeque::new();
        queue.push_back((
            self.root,
            Context {
                lambdas: vec![],
                available_vars: vec![],
                possible_expressions,
                depth: 0,
            },
        ));
        ContextBFSIterator { pool: self, queue }
    }
}
