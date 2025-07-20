use super::*;

#[derive(Debug, Default, Clone)]
pub(super) struct Context<'t> {
    lambdas: Vec<&'t LambdaType>,
    depth: usize,
}

impl<'t> Context<'t> {
    pub fn lambdas(&self) -> &[&LambdaType] {
        &self.lambdas
    }

    pub fn depth(&self) -> usize {
        self.depth
    }

    pub fn into_owned_lambdas<'b>(self, new_lambdas: &'b [LambdaType]) -> Context<'b> {
        Context {
            lambdas: new_lambdas.iter().collect(),
            depth: self.depth,
        }
    }

    pub fn add_var(&mut self, actor_or_event: ActorOrEvent) {
        self.lambdas.push(match actor_or_event {
            ActorOrEvent::Actor => LambdaType::a(),
            ActorOrEvent::Event => LambdaType::e(),
        })
    }

    pub fn add_lambda(&mut self, lhs: &'t LambdaType) {
        self.lambdas.push(lhs);
    }

    pub fn can_sample_event(&self) -> bool {
        self.lambdas.iter().any(|lam| *lam == LambdaType::e())
    }

    pub fn variables<'a>(
        &self,
        lambda_type: &LambdaType,
    ) -> impl Iterator<Item = UnbuiltExpr<'a, 't>> {
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

pub(super) struct ContextBFSIterator<'src, 'a> {
    pool: &'a RootedLambdaPool<'src, Expr<'src>>,
    queue: VecDeque<(LambdaExprRef, Context<'a>)>,
}

impl<'src, 'a> Iterator for ContextBFSIterator<'src, 'a> {
    type Item = (LambdaExprRef, Context<'a>);

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
                    var_type: var,
                    restrictor,
                    subformula,
                    ..
                }) => {
                    let mut context = context.clone();
                    context.add_var(*var);
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

impl<'src> RootedLambdaPool<'src, Expr<'src>> {
    pub(super) fn context_bfs_iter<'a>(&'a self) -> ContextBFSIterator<'src, 'a> {
        let mut queue = VecDeque::new();
        queue.push_back((
            self.root,
            Context {
                lambdas: vec![],
                depth: 0,
            },
        ));
        ContextBFSIterator { pool: self, queue }
    }
}
