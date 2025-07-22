use std::cell::Cell;

use super::*;

#[derive(Debug, Default, Clone)]
pub(super) struct Context<'t> {
    lambdas: Vec<&'t LambdaType>,
    used_lambda: Vec<Cell<bool>>,
    depth: usize,
}

impl<'t> Context<'t> {
    pub fn lambdas(&self) -> &[&LambdaType] {
        &self.lambdas
    }

    pub fn depth(&self) -> usize {
        self.depth
    }

    pub fn all_variables(&self) -> impl Iterator<Item = (&LambdaType, bool, usize)> {
        self.lambdas
            .iter()
            .copied()
            .zip(self.used_lambda.iter().map(|x| x.get()))
            .zip((1..(1 + self.lambdas.len())).rev().map(|x| x - 1))
            .map(|((a, b), c)| (a, b, c))
    }

    pub fn into_owned_lambdas<'b>(self, new_lambdas: &'b [LambdaType]) -> Context<'b> {
        Context {
            lambdas: new_lambdas.iter().collect(),
            used_lambda: self.used_lambda,
            depth: self.depth,
        }
    }

    pub fn add_var(&mut self, actor_or_event: ActorOrEvent) {
        self.lambdas.push(match actor_or_event {
            ActorOrEvent::Actor => LambdaType::a(),
            ActorOrEvent::Event => LambdaType::e(),
        });
        self.used_lambda.push(Cell::new(false));
    }

    pub fn add_lambda(&mut self, lhs: &'t LambdaType) {
        self.lambdas.push(lhs);
        self.used_lambda.push(Cell::new(false));
    }

    pub fn can_sample_event(&self) -> bool {
        self.lambdas.iter().any(|lam| *lam == LambdaType::e())
    }

    pub fn add_bound_var(&self, bvar: usize) {
        let i = self.lambdas.len() - 1 - bvar;
        self.used_lambda[i].set(true);
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
                    self.queue.push_back((*subformula, context.clone()));
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
                    self.queue
                        .push_back((LambdaExprRef(restrictor.0), context.clone()));
                    self.queue.push_back((LambdaExprRef(subformula.0), context));
                }
                Some(LambdaExpr::LanguageOfThoughtExpr(x)) => x.get_children().for_each(|x| {
                    let mut context = context.clone();
                    context.depth += 1;
                    self.queue.push_back((x, context))
                }),
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
            depth: 0,
        };
        let vars = c.all_variables().collect::<Vec<_>>();

        assert_eq!(vars, vec![(&t, false, 0)]);
        Ok(())
    }
}
