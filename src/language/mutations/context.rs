use ahash::{HashMap, HashSet};
use itertools::Either;

use super::*;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) enum ConstantFunctionState {
    Constant,
    PotentiallyConstant,
    NonConstant,
}

impl ConstantFunctionState {
    fn update(&mut self, new: Self) {
        match self {
            ConstantFunctionState::Constant => (),
            ConstantFunctionState::PotentiallyConstant => match new {
                ConstantFunctionState::Constant => *self = ConstantFunctionState::Constant,
                ConstantFunctionState::PotentiallyConstant => (),
                ConstantFunctionState::NonConstant => (),
            },
            ConstantFunctionState::NonConstant => match new {
                ConstantFunctionState::Constant => *self = ConstantFunctionState::Constant,
                ConstantFunctionState::PotentiallyConstant => {
                    *self = ConstantFunctionState::PotentiallyConstant
                }
                ConstantFunctionState::NonConstant => *self = ConstantFunctionState::NonConstant,
            },
        }
    }

    fn done(&mut self) {
        match self {
            ConstantFunctionState::Constant => (),
            ConstantFunctionState::PotentiallyConstant => *self = ConstantFunctionState::Constant,
            ConstantFunctionState::NonConstant => (),
        }
    }
}

///A struct which keeps track of the context leading up to some expression, e.g. its depth, what
///variables are accessible, and whether the context has a constant function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Context {
    lambdas: Vec<(LambdaType, ConstantFunctionState)>,
    possible_types: HashMap<LambdaType, HashSet<LambdaType>>,
    pub(super) pool_index: usize,
    pub(super) position: usize,
    pub(super) depth: usize,
    done: bool,
    pub(super) open_nodes: usize,
    constant_function: ConstantFunctionState,
}

impl PartialOrd for RandomPQ {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

///Reversed to deal with pq
impl Ord for RandomPQ {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let c = &self.0;
        let o = &other.0;
        c.done
            .cmp(&o.done)
            .then(o.open_depth_score().cmp(&c.open_depth_score()))
            .then(o.constant_function.cmp(&c.constant_function))
            .then(self.1.partial_cmp(&other.1).unwrap())
    }
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
            .then(self.pool_index.cmp(&other.pool_index))
    }
}
impl Context {
    fn open_depth_score(&self) -> usize {
        self.depth + self.open_nodes.pow(2)
    }
}

impl<'src, T: LambdaLanguageOfThought> LambdaPool<'src, T> {
    //If something at position `pos` can be moved from `old_context` to `new_context`
    fn compatible_with(
        &self,
        pos: LambdaExprRef,
        new_context: &Context,
        old_context: &Context,
    ) -> bool {
        for (x, d) in self.bfs_from(pos) {
            if let LambdaExpr::BoundVariable(b, _) = self.get(x) {
                if b + 1 > d {
                    //this involves the outside context;
                    let old_lambda_pos = old_context.lambdas.len() + d - b - 1;

                    if b + 1 > d + new_context.lambdas.len() {
                        //Impossible to access
                        //TODO: Maybe some remapping system if old_context is contained by
                        //new_context
                        return false;
                    }
                    let new_lambda_pos = new_context.lambdas.len() + d - b - 1;
                    if new_context.lambdas.get(new_lambda_pos)
                        != old_context.lambdas.get(old_lambda_pos)
                    {
                        return false;
                    }
                }
            }
        }
        true
    }
}

impl Context {
    ///The number of variables in the current [`Context`]
    pub fn n_vars(&self) -> usize {
        self.lambdas.len()
    }

    //We make it so that if there are multiple children of something that introduces a
    //function, then all of its children must be non-constants, by calling this whenever we access
    //a child of a variable-introducing expr
    pub(super) fn reset_lambda(&mut self, i: usize) {
        let x: &mut (LambdaType, ConstantFunctionState) = &mut self.lambdas[i];
        x.1.update(ConstantFunctionState::PotentiallyConstant);
    }

    pub(super) fn from_pos<'src, T: LambdaLanguageOfThought>(
        pool: &RootedLambdaPool<'src, T>,
        pos: LambdaExprRef,
    ) -> (Context, bool) {
        let mut context = Context::new(0, vec![]);
        let mut stack = vec![(pool.root, 0, false, None)];
        let mut return_is_subformula = false;

        while let Some((x, n_lambdas, is_subformula, reset)) = stack.pop() {
            if let Some(reset) = reset {
                context.reset_lambda(reset);
            }

            context.depth += 1;
            let e = pool.get(x);
            if context.lambdas.len() != n_lambdas {
                for _ in 0..(context.lambdas.len() - n_lambdas) {
                    context.pop_lambda();
                }
            }

            if pos == x {
                return_is_subformula = is_subformula;
                break;
            }

            if let Some(v) = e.var_type() {
                context.add_lambda(v);
            } else if let LambdaExpr::BoundVariable(n, _) = e {
                context.use_bvar(*n);
            }

            if let LambdaExpr::Application {
                subformula,
                argument,
            } = e
            {
                stack.push((*subformula, context.lambdas.len(), true, None));
                stack.push((*argument, context.lambdas.len(), false, None));
            } else {
                let reset = e.var_type().map(|_| context.lambdas.len() - 1);
                stack.extend(
                    e.get_children()
                        .map(|x| (x, context.lambdas.len(), false, reset)),
                );
            }
        }
        (context, return_is_subformula)
    }

    pub(super) fn find_compatible<'src, T: LambdaLanguageOfThought>(
        &self,
        pool: &RootedLambdaPool<'src, T>,
        pos: LambdaExprRef,
    ) -> Result<Vec<LambdaExprRef>, TypeError> {
        let t = pool.pool.get_type(pos)?;

        let mut this_context = Context::new(0, vec![]);
        let mut stack = vec![(pool.root, 0)];
        let mut options: Vec<_> = vec![];
        while let Some((x, n_lambdas)) = stack.pop() {
            this_context.depth += 1;
            let e = pool.get(x);
            if this_context.lambdas.len() != n_lambdas {
                for _ in 0..(this_context.lambdas.len() - n_lambdas) {
                    this_context.pop_lambda();
                }
            }
            if pos != x
                && t == pool.pool.get_type(x)?
                && pool.pool.compatible_with(x, self, &this_context)
            {
                options.push(x);
            }

            if let Some(v) = e.var_type() {
                this_context.add_lambda(v);
            } else if let LambdaExpr::BoundVariable(n, _) = e {
                this_context.use_bvar(*n);
            }

            stack.extend(e.get_children().map(|x| (x, this_context.lambdas.len())));
        }
        Ok(options)
    }

    fn update_possible_types(&mut self) {
        self.possible_types.clear();

        let mut new_types: HashSet<(&LambdaType, &LambdaType)> = HashSet::default();
        let mut base_types: HashSet<_> = self.lambdas.iter().map(|(x, _)| x).collect();
        base_types.insert(LambdaType::a());
        base_types.insert(LambdaType::t());
        base_types.insert(LambdaType::at());
        base_types.insert(LambdaType::et());

        loop {
            for subformula in base_types.iter() {
                if let Ok((argument, result_type)) = subformula.split() {
                    let already_has_type = self
                        .possible_types
                        .get(result_type)
                        .map(|x| x.contains(argument))
                        .unwrap_or(false);

                    if base_types.contains(argument) && !already_has_type {
                        new_types.insert((result_type, argument));
                    }
                }
            }
            if new_types.is_empty() {
                break;
            } else {
                for (result, argument) in new_types.iter() {
                    self.possible_types
                        .entry((*result).clone())
                        .or_default()
                        .insert((*argument).clone());
                }
                base_types.extend(new_types.drain().map(|(result, _arg)| result));
            }
        }
    }

    pub(super) fn new(position: usize, lambdas: Vec<(LambdaType, ConstantFunctionState)>) -> Self {
        let mut c = Context {
            pool_index: 0,
            position,
            done: false,
            depth: 0,
            possible_types: HashMap::default(),
            open_nodes: 1,
            constant_function: if lambdas.is_empty() {
                ConstantFunctionState::NonConstant
            } else {
                ConstantFunctionState::PotentiallyConstant
            },
            lambdas,
        };
        c.update_possible_types();
        c
    }

    pub(super) fn add_lambda(&mut self, t: &LambdaType) {
        self.constant_function
            .update(ConstantFunctionState::PotentiallyConstant);
        self.lambdas
            .push((t.clone(), ConstantFunctionState::PotentiallyConstant));
        self.update_possible_types();
    }

    pub(super) fn pop_lambda(&mut self) {
        let (_, mut function_state) = self.lambdas.pop().unwrap();
        function_state.done();
        self.constant_function.update(function_state);
        if self.lambdas.is_empty() {
            function_state.done();
        }
        self.update_possible_types();
    }

    pub(super) fn use_bvar(&mut self, b: usize) {
        let n = self.lambdas.len() - b - 1;
        self.lambdas.get_mut(n).unwrap().1 = ConstantFunctionState::NonConstant;
    }

    pub fn is_constant(&self) -> bool {
        self.constant_function == ConstantFunctionState::Constant
    }

    pub fn can_sample_event(&self) -> bool {
        self.lambdas.iter().any(|(lam, _)| lam == LambdaType::e())
    }

    pub fn current_variable_types(&self) -> impl Iterator<Item = &LambdaType> {
        self.lambdas.iter().map(|(x, _)| x)
    }

    pub fn applications<'a, 'b: 'a>(
        &'a self,
        lambda_type: &'b LambdaType,
    ) -> impl Iterator<Item = (LambdaType, LambdaType)> + 'a {
        match self.possible_types.get(lambda_type) {
            Some(x) => Either::Left(x.iter().map(|x| {
                (
                    LambdaType::compose(x.clone(), lambda_type.clone()),
                    x.clone(),
                )
            })),
            None => Either::Right(std::iter::empty()),
        }
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
            possible_types: HashMap::default(),
            open_nodes: 0,
            constant_function: ConstantFunctionState::NonConstant,
        };
        let b = Context {
            depth: 2,
            done: false,
            lambdas: vec![],
            possible_types: HashMap::default(),
            pool_index: 0,
            position: 0,
            open_nodes: 0,
            constant_function: ConstantFunctionState::NonConstant,
        };
        let c = Context {
            depth: 5,
            done: true,
            lambdas: vec![],
            possible_types: HashMap::default(),
            pool_index: 0,
            position: 0,
            open_nodes: 0,
            constant_function: ConstantFunctionState::NonConstant,
        };
        let d = Context {
            depth: 5,
            done: true,
            lambdas: vec![],
            possible_types: HashMap::default(),
            pool_index: 0,
            position: 0,
            open_nodes: 54,
            constant_function: ConstantFunctionState::NonConstant,
        };

        assert!(a < b);
        assert!(c < b);
        assert!(c < a);
        assert!(c < d);

        Ok(())
    }

    #[test]
    fn possible_type_check() -> anyhow::Result<()> {
        let mut c = Context {
            depth: 0,
            done: false,
            lambdas: vec![
                (
                    LambdaType::from_string("<a,t>")?,
                    ConstantFunctionState::PotentiallyConstant,
                ),
                (
                    LambdaType::from_string("<<a,t>, <a,t>>")?,
                    ConstantFunctionState::PotentiallyConstant,
                ),
                (
                    LambdaType::from_string("<<a,t>, <<a,t>, <e,t>>>")?,
                    ConstantFunctionState::PotentiallyConstant,
                ),
                (
                    LambdaType::from_string("<<a,t>, e>")?,
                    ConstantFunctionState::PotentiallyConstant,
                ),
                (
                    LambdaType::from_string("<e, <a,<a,t>>>")?,
                    ConstantFunctionState::PotentiallyConstant,
                ),
            ],
            possible_types: HashMap::default(),
            pool_index: 0,
            position: 0,
            open_nodes: 54,
            constant_function: ConstantFunctionState::PotentiallyConstant,
        };

        c.update_possible_types();
        let mut z = c
            .possible_types
            .iter()
            .map(|(x, y)| {
                let mut v = y.iter().map(|y| y.to_string()).collect::<Vec<_>>();
                v.sort();
                (x.to_string(), v)
            })
            .collect::<Vec<_>>();
        z.sort();

        assert_eq!(
            z,
            vec![
                ("<<a,t>,<e,t>>".to_string(), vec!["<a,t>".to_string()]),
                ("<a,<a,t>>".to_string(), vec!["e".to_string()]),
                (
                    "<a,t>".to_string(),
                    vec!["<a,t>".to_string(), "a".to_string()]
                ),
                ("<e,t>".to_string(), vec!["<a,t>".to_string()]),
                ("e".to_string(), vec!["<a,t>".to_string()]),
                ("t".to_string(), vec!["a".to_string(), "e".to_string()]),
            ]
        );

        Ok(())
    }
}
