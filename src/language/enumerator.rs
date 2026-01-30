use std::fmt::Debug;

use ahash::{HashMap, HashSet};
use itertools::{Either, repeat_n};

use crate::{
    lambda::{LambdaExpr, LambdaLanguageOfThought, types::LambdaType},
    language::{Expr, PossibleExpressions, mutations::PossibleExpr},
};

#[derive(Debug, Clone, Eq, PartialEq)]
pub(crate) struct SimpleContext {
    lambdas: Vec<LambdaType>,
    possible_types: HashMap<LambdaType, HashSet<LambdaType>>,
}

impl SimpleContext {
    pub fn variables<'src, T: LambdaLanguageOfThought>(
        &self,
        lambda_type: &LambdaType,
    ) -> impl Iterator<Item = LambdaExpr<'src, T>> {
        let n = self.lambdas.len();
        self.lambdas
            .iter()
            .enumerate()
            .filter_map(move |(i, lambda)| {
                if lambda == lambda_type {
                    Some(LambdaExpr::BoundVariable(n - i - 1, lambda.clone()))
                } else {
                    None
                }
            })
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
}

impl Default for SimpleContext {
    fn default() -> Self {
        let mut possible_types: HashMap<LambdaType, HashSet<LambdaType>> = HashMap::default();
        let mut new_types: HashSet<(&LambdaType, &LambdaType)> = HashSet::default();
        let mut base_types: HashSet<_> = [
            LambdaType::a(),
            LambdaType::e(),
            LambdaType::t(),
            LambdaType::at(),
            LambdaType::et(),
        ]
        .into_iter()
        .collect();

        loop {
            for subformula in base_types.iter() {
                if let Ok((argument, result_type)) = subformula.split() {
                    let already_has_type = possible_types
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
                    possible_types
                        .entry((*result).clone())
                        .or_default()
                        .insert((*argument).clone());
                }
                base_types.extend(new_types.drain().map(|(result, _arg)| result));
            }
        }
        SimpleContext {
            lambdas: vec![],
            possible_types,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum ExprOrType<'src, T: LambdaLanguageOfThought> {
    Type {
        lambda_type: LambdaType,
        is_app_subformula: bool,
    },
    Expr {
        lambda_expr: LambdaExpr<'src, T>,
    },
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct PartialExpr<'src, T: LambdaLanguageOfThought> {
    pool: Vec<ExprOrType<'src, T>>,
    edges: Vec<(usize, usize)>,
    position: Option<usize>,
}

impl<'src, T: LambdaLanguageOfThought + Clone + Debug> PartialExpr<'src, T> {
    fn new(t: &LambdaType) -> Self {
        PartialExpr {
            pool: vec![ExprOrType::Type {
                lambda_type: t.clone(),
                is_app_subformula: false,
            }],
            edges: vec![],
            position: Some(0),
        }
    }

    fn parent(&self, i: usize) -> Option<usize> {
        self.edges
            .iter()
            .find_map(|(src, dest)| if *dest == i { Some(*src) } else { None })
    }

    fn variables(&self, mut i: usize, t: &LambdaType) -> Vec<LambdaExpr<'src, T>> {
        let mut variables = vec![];
        let mut debruijn = 0;
        while let Some(parent) = self.parent(i) {
            if let ExprOrType::Expr { lambda_expr } = &self.pool[parent]
                && let Some(v) = lambda_expr.var_type()
            {
                if v == t {
                    variables.push(LambdaExpr::BoundVariable(debruijn, v.clone()));
                }
                debruijn += 1;
            }

            i = parent;
        }
        variables
    }

    fn expand_position(
        self,
        possibles: &PossibleExpressions<'src, T>,
    ) -> impl Iterator<Item = Self> {
        let ExprOrType::Type {
            lambda_type,
            is_app_subformula: _,
        } = &self.pool[self.position.unwrap()]
        else {
            panic!()
        };
        let variables = self.variables(self.position.unwrap(), lambda_type);

        let terms = possibles.terms(lambda_type, false, variables);

        repeat_n(self, terms.len())
            .zip(terms)
            .map(|(x, term)| x.set_position(term))
    }

    fn done(&self) -> bool {
        self.position.is_none()
    }

    fn set_position(mut self, term: PossibleExpr<'_, 'src, T>) -> Self {
        let (lambda_expr, x) = term.into_expr();
        if x.is_some() {
            todo!()
        };

        match &lambda_expr {
            LambdaExpr::LanguageOfThoughtExpr(e) => {
                for a in e.get_arguments() {
                    self.pool.push(ExprOrType::Type {
                        lambda_type: a,
                        is_app_subformula: false,
                    });
                    self.edges
                        .push((self.position.unwrap(), self.pool.len() - 1));
                }
            }
            LambdaExpr::BoundVariable(..) | LambdaExpr::FreeVariable(..) => (),
            _ => todo!(),
        }
        self.pool[self.position.unwrap()] = ExprOrType::Expr { lambda_expr };

        self.position = self
            .pool
            .iter()
            .position(|x| matches!(x, ExprOrType::Type { .. }));

        self
    }
}

impl<'src> PossibleExpressions<'src, Expr<'src>> {
    fn enumerate(&self, t: &LambdaType) {
        let x: PartialExpr<'src, Expr<'src>> = PartialExpr::new(t);
        let mut stack = vec![x];
        let mut done = vec![];
        while let Some(s) = stack.pop() {
            if s.pool.len() > 5 {
                continue;
            }
            for x in s.expand_position(self) {
                if x.done() {
                    done.push(x);
                } else {
                    stack.push(x);
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new_enumerate() -> anyhow::Result<()> {
        let actors = ["john", "mary", "phil", "sue"];
        let actor_properties = ["a"];
        let event_properties = ["e"];
        let possibles = PossibleExpressions::new(&actors, &actor_properties, &event_properties);
        let t = vec![LambdaType::A];
        for t in t {
            possibles.enumerate(&t);
        }
        Ok(())
    }
}
