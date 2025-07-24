use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Context {
    lambdas: Vec<(LambdaType, bool)>,
    pub pool_index: usize,
    pub position: usize,
    pub depth: usize,
    done: bool,
    pub open_nodes: usize,
    constant_function: bool,
}

impl PartialOrd for Context {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Context {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other
            .done
            .cmp(&self.done)
            .then(self.open_depth_score().cmp(&other.open_depth_score()))
            .then(self.constant_function.cmp(&other.constant_function))
    }
}
impl Context {
    fn open_depth_score(&self) -> usize {
        self.depth + self.open_nodes.pow(2)
    }
}

impl Context {
    pub(super) fn from_pos<'src, T: LambdaLanguageOfThought>(
        pool: &RootedLambdaPool<'src, T>,
        pos: LambdaExprRef,
    ) -> Context {
        let mut context = Context::new(0, vec![]);
        let mut stack = VecDeque::from([(pool.root, 0)]);
        while let Some((x, mut n_lambdas)) = stack.pop_front() {
            context.depth += 1;
            let e = pool.get(x);
            if let Some(v) = e.var_type() {
                context.add_lambda(v);
                n_lambdas += 1;
            } else if let LambdaExpr::BoundVariable(n, _) = e {
                context.use_bvar(*n);
            } else if context.lambdas.len() != n_lambdas {
                context.pop_lambda();
            }

            if pos == x {
                break;
            }

            stack.extend(e.get_children().map(|x| (x, n_lambdas)));
        }
        context
    }

    pub fn new(position: usize, lambdas: Vec<(LambdaType, bool)>) -> Self {
        Context {
            lambdas,
            pool_index: 0,
            position,
            done: false,
            depth: 0,
            open_nodes: 1,
            constant_function: false,
        }
    }

    pub fn add_lambda(&mut self, t: &LambdaType) {
        self.lambdas.push((t.clone(), false));
    }

    pub fn pop_lambda(&mut self) {
        let (_, used) = self.lambdas.pop().unwrap();
        self.constant_function |= !used;
    }

    pub fn use_bvar(&mut self, b: usize) {
        let n = self.lambdas.len() - b - 1;
        self.lambdas.get_mut(n).unwrap().1 = true;
    }

    pub fn is_constant(&self) -> bool {
        self.constant_function
    }

    pub fn can_sample_event(&self) -> bool {
        self.lambdas.iter().any(|(lam, _)| lam == LambdaType::e())
    }

    pub fn variables<'src, T: LambdaLanguageOfThought>(
        &self,
        lambda_type: &LambdaType,
    ) -> impl Iterator<Item = LambdaExpr<'src, T>> {
        let n = self.lambdas.len();
        self.lambdas
            .iter()
            .enumerate()
            .filter_map(move |(i, (lambda, _))| {
                if lambda == lambda_type {
                    Some(LambdaExpr::BoundVariable(n - i - 1, lambda.clone()))
                } else {
                    None
                }
            })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_context() -> anyhow::Result<()> {
        let a = Context {
            depth: 1,
            done: false,
            lambdas: vec![],
            pool_index: 0,
            position: 0,
            open_nodes: 0,
            constant_function: false,
        };
        let b = Context {
            depth: 2,
            done: false,
            lambdas: vec![],
            pool_index: 0,
            position: 0,
            open_nodes: 0,
            constant_function: false,
        };
        let c = Context {
            depth: 5,
            done: true,
            lambdas: vec![],
            pool_index: 0,
            position: 0,
            open_nodes: 0,
            constant_function: false,
        };
        let d = Context {
            depth: 5,
            done: true,
            lambdas: vec![],
            pool_index: 0,
            position: 0,
            open_nodes: 54,
            constant_function: false,
        };

        assert!(a < b);
        assert!(c < b);
        assert!(c < a);
        assert!(c < d);

        Ok(())
    }
}
