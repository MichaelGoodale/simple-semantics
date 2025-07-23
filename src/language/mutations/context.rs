use std::cell::Cell;

use super::*;

#[derive(Debug, Default, Clone)]
pub(super) struct Context<'t> {
    lambdas: Vec<&'t LambdaType>,
    used_lambda: Vec<Cell<bool>>,
    future_branches: Vec<usize>,
    depth: usize,
}

#[derive(Debug, Clone, Eq, PartialEq, Copy)]
pub(super) struct LambdaInfo<'t> {
    lambda_type: &'t LambdaType,
    has_been_used: bool,
    lambda_id: usize,
    future_opportunities: usize,
}

impl<'t> LambdaInfo<'t> {
    pub fn has_been_used(&self) -> bool {
        self.has_been_used
    }

    pub fn lambda_type(&self) -> &'t LambdaType {
        self.lambda_type
    }

    pub fn lambda_id(&self) -> usize {
        self.lambda_id
    }

    pub fn future_opportunities(&self) -> usize {
        self.future_opportunities
    }
}

impl<'t> Context<'t> {
    pub fn lambdas(&self) -> &[&LambdaType] {
        &self.lambdas
    }

    pub fn depth(&self) -> usize {
        self.depth
    }

    pub fn all_variables(&self) -> impl Iterator<Item = LambdaInfo<'t>> {
        self.lambdas
            .iter()
            .copied()
            .zip(self.used_lambda.iter().map(|x| x.get()))
            .zip((1..(1 + self.lambdas.len())).rev().map(|x| x - 1))
            .zip(self.future_branches.iter().copied())
            .map(
                |(((lambda_type, has_been_used), lambda_id), future_opportunities)| LambdaInfo {
                    lambda_type,
                    lambda_id,
                    has_been_used,
                    future_opportunities,
                },
            )
    }

    pub fn into_owned_lambdas<'b>(self, new_lambdas: &'b [LambdaType]) -> Context<'b> {
        Context {
            lambdas: new_lambdas.iter().collect(),
            used_lambda: self.used_lambda,
            future_branches: self.future_branches,
            depth: self.depth,
        }
    }

    pub fn add_var(&mut self, actor_or_event: ActorOrEvent) {
        self.lambdas.push(match actor_or_event {
            ActorOrEvent::Actor => LambdaType::a(),
            ActorOrEvent::Event => LambdaType::e(),
        });
        self.used_lambda.push(Cell::new(false));
        self.future_branches.push(0);
    }

    pub fn add_lambda(&mut self, lhs: &'t LambdaType) {
        self.lambdas.push(lhs);
        self.used_lambda.push(Cell::new(false));
        self.future_branches.push(0);
    }

    pub fn can_sample_event(&self) -> bool {
        self.lambdas.iter().any(|lam| *lam == LambdaType::e())
    }

    pub fn add_bound_var(&self, bvar: usize) {
        let i = self.lambdas.len() - 1 - bvar;
        self.used_lambda[i].set(true);
    }

    pub fn with_future_branch(mut self, n: usize) -> Self {
        self.future_branches.iter_mut().for_each(|x| *x += n);
        self
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

    pub fn clear_future_branches(&mut self) {
        self.future_branches.iter_mut().for_each(|x| *x = 0);
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
            match self.pool.get_opt(x) {
                Some(LambdaExpr::Lambda(x, c)) => {
                    let mut context = context.clone();
                    context.add_lambda(c);
                    context.depth += 1;
                    self.queue.push_back((*x, context))
                }
                Some(LambdaExpr::Application {
                    subformula,
                    argument,
                }) => {
                    let mut context = context.clone();
                    context.depth += 1;
                    self.queue
                        .push_back((*subformula, context.clone().with_future_branch(1)));
                    self.queue.push_back((*argument, context));
                }
                Some(LambdaExpr::LanguageOfThoughtExpr(Expr::Quantifier {
                    var_type: var,
                    restrictor,
                    subformula,
                    ..
                })) => {
                    let mut context = context.clone();
                    context.add_var(*var);
                    context.depth += 1;
                    self.queue.push_back((
                        LambdaExprRef(restrictor.0),
                        context.clone().with_future_branch(1),
                    ));
                    self.queue.push_back((LambdaExprRef(subformula.0), context));
                }
                Some(LambdaExpr::LanguageOfThoughtExpr(x)) => {
                    let n_children = x.n_children();
                    x.get_children().enumerate().for_each(|(i, x)| {
                        let mut context = context.clone();
                        context.depth += 1;
                        self.queue
                            .push_back((x, context.with_future_branch(n_children - i - 1)))
                    })
                }
                Some(LambdaExpr::BoundVariable(d, _)) => context.add_bound_var(*d),
                Some(LambdaExpr::FreeVariable(..)) => (),
                None => (),
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
                used_lambda: vec![],
                future_branches: vec![],
                depth: 0,
            },
        ));
        ContextBFSIterator { pool: self, queue }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_context() -> anyhow::Result<()> {
        let t = LambdaType::A;
        let c = Context {
            lambdas: vec![&t],
            used_lambda: vec![Cell::new(false)],
            future_branches: vec![0],
            depth: 0,
        };
        let vars = c.all_variables().collect::<Vec<_>>();

        assert_eq!(
            vars,
            vec![LambdaInfo {
                lambda_type: &t,
                has_been_used: false,
                lambda_id: 0,
                future_opportunities: 0
            }]
        );
        Ok(())
    }
}
