use std::{
    fmt::Debug,
    hash::Hash,
    rc::{Rc, Weak},
};

use ahash::HashSet;
use itertools::repeat_n;
use thiserror::Error;
use weak_table::WeakHashSet;

use crate::{
    lambda::{
        LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool, RootedLambdaPool,
        types::LambdaType,
    },
    language::{Expr, MonOp, PossibleExpressions, mutations::PossibleExpr},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum FinishedOrType<'src, T: LambdaLanguageOfThought> {
    Type(LambdaType),
    PartiallyExpanded(ExprWrapper<'src, T>),
    Expr(Rc<FinishedExpr<'src, T>>),
}

impl<'src, T: LambdaLanguageOfThought + Clone + Hash + Eq + PartialEq + Debug + Ord>
    FinishedOrType<'src, T>
{
    fn make_not_partial_if_possible(
        &mut self,
        table: &mut WeakHashSet<Weak<FinishedExpr<'src, T>>>,
    ) -> bool {
        if let FinishedOrType::PartiallyExpanded(ExprWrapper { h, variables: _ }) = self {
            if !h.is_done() {
                let now_done = h
                    .children
                    .iter_mut()
                    .all(|x| x.make_not_partial_if_possible(table));
                if !now_done {
                    return false;
                }
            }
            //annoying stuff to get h out.
            let temp = std::mem::replace(self, FinishedOrType::Type(LambdaType::A));
            let FinishedOrType::PartiallyExpanded(ExprWrapper { h, .. }) = temp else {
                panic!()
            };

            let h: FinishedExpr<'src, T> = h.try_into().unwrap();
            let h = match table.get(&h) {
                Some(h) => h,
                None => {
                    let h = Rc::new(h);
                    table.insert(h.clone());
                    table.get(&h).unwrap()
                }
            };
            *self = FinishedOrType::Expr(h);
            true
        } else {
            matches!(self, FinishedOrType::Expr(_))
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct FinishedExpr<'src, T: LambdaLanguageOfThought> {
    expr: LambdaExpr<'src, T>,
    children: Vec<Rc<FinishedExpr<'src, T>>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct HashedExpr<'src, T: LambdaLanguageOfThought> {
    expr: LambdaExpr<'src, T>,
    children: Vec<FinishedOrType<'src, T>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ExprWrapper<'src, T: LambdaLanguageOfThought> {
    h: HashedExpr<'src, T>,
    variables: Vec<LambdaType>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Enumerator<'a, 'src> {
    max_length: usize,
    stack: Vec<(usize, ExprWrapper<'src, Expr<'src>>)>,
    table: WeakHashSet<Weak<FinishedExpr<'src, Expr<'src>>>>,
    done: HashSet<Rc<FinishedExpr<'src, Expr<'src>>>>,
    possibles: &'a PossibleExpressions<'src, Expr<'src>>,
}

impl<'src> Iterator for Enumerator<'_, 'src> {
    type Item = RootedLambdaPool<'src, Expr<'src>>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((n, x)) = self.stack.pop() {
            if let Some(new) = x.expand(
                vec![],
                self.possibles,
                &mut self.table,
                &mut self.stack,
                self.max_length,
                n,
            ) {
                let h = new.clone();
                if self.done.insert(new) {
                    return Some((*h).clone().into());
                }
            }
        }
        None
    }
}

impl<'src> PossibleExpressions<'src, Expr<'src>> {
    ///Enumerate over all possible expressions of type [`t`]
    pub fn alt_enumerator<'a>(&'a self, t: &LambdaType, max_length: usize) -> Enumerator<'a, 'src> {
        let mut stack: Vec<HashedExpr<_>> = self
            .terms(t, false, vec![])
            .iter()
            .map(|x| {
                let mut h: HashedExpr<_> = x.expr().clone().into();
                if let LambdaExpr::Lambda(_, _) = h.expr {
                    h.children = vec![FinishedOrType::Type(t.rhs().unwrap().clone())];
                }
                h
            })
            .collect();

        let mut table: WeakHashSet<Weak<FinishedExpr<'src, Expr<'src>>>> = WeakHashSet::new();
        let done: HashSet<Rc<FinishedExpr<_>>> = stack
            .extract_if(.., |x| x.is_done())
            .map(|x| Rc::new(x.try_into().unwrap()))
            .collect();

        let stack = stack
            .into_iter()
            .map(|h| {
                (
                    1 + h.children.len(),
                    ExprWrapper {
                        variables: std::iter::once(h.expr.var_type().cloned())
                            .flatten()
                            .collect(),
                        h,
                    },
                )
            })
            .collect::<Vec<_>>();

        for x in done.iter() {
            table.insert(x.clone());
        }

        Enumerator {
            max_length,
            stack,
            table,
            possibles: self,
            done,
        }
    }
}

fn get_this<'a, 'src, T: LambdaLanguageOfThought + Debug>(
    x: &'a mut ExprWrapper<'src, T>,
    path: &[usize],
) -> &'a mut ExprWrapper<'src, T> {
    let mut this = x;
    for i in path.iter().copied() {
        match &mut this.h.children[i] {
            FinishedOrType::PartiallyExpanded(expr_wrapper) => {
                this = expr_wrapper;
            }
            _ => panic!(),
        }
    }
    this
}

impl<'src> ExprWrapper<'src, Expr<'src>> {
    fn expand(
        mut self,
        mut path: Vec<usize>,
        possibles: &PossibleExpressions<'src, Expr<'src>>,
        table: &mut WeakHashSet<Weak<FinishedExpr<'src, Expr<'src>>>>,
        stack: &mut Vec<(usize, ExprWrapper<'src, Expr<'src>>)>,
        max_length: usize,
        n: usize,
    ) -> Option<Rc<FinishedExpr<'src, Expr<'src>>>> {
        let this = get_this(&mut self, &path);

        this.h.children.iter_mut().for_each(|x| {
            x.make_not_partial_if_possible(table);
        });

        //Initialize any types that haven't been started.
        if let Some((i, typ)) = this
            .h
            .children
            .iter()
            .enumerate()
            .find_map(|(i, x)| match x {
                FinishedOrType::Type(lambda_type) => Some((i, lambda_type)),
                _ => None,
            })
        {
            let mut terms = possibles.terms(typ, false, vec![]);

            terms.retain(|x| {
                (x.expr().n_children() + n) <= max_length
                    && !(matches!(
                        this.h.expr,
                        LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Not, _))
                    ) && matches!(
                        x.expr(),
                        LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Not, _))
                    ))
            });
            let terms = terms
                .into_iter()
                .map(|x| {
                    let (e, _) = x.into_expr();
                    let mut h = HashedExpr::from(e);
                    if let LambdaExpr::Lambda(_, _) = h.expr {
                        h.children = vec![FinishedOrType::Type(typ.rhs().unwrap().clone())];
                    }
                    h
                })
                .collect::<Vec<_>>();

            for (mut parent, h) in repeat_n(self, terms.len()).zip(terms) {
                if h.is_done() {
                    let h = h.try_into().unwrap();
                    let h = match table.get(&h) {
                        Some(h) => h,
                        None => {
                            let h = Rc::new(h);
                            table.insert(h.clone());
                            table.get(&h).unwrap()
                        }
                    };
                    let this = get_this(&mut parent, &path);
                    this.h.children[i] = FinishedOrType::Expr(h);
                    stack.push((n, parent));
                } else {
                    let mut variables = parent.variables.clone();
                    if let Some(t) = h.expr.var_type() {
                        variables.push(t.clone());
                    }

                    let this = get_this(&mut parent, &path);
                    let n_children = h.children.len();
                    this.h.children[i] =
                        FinishedOrType::PartiallyExpanded(ExprWrapper { h, variables });
                    stack.push((n + n_children, parent));
                }
            }
        } else if let Some(i) = this
            .h
            .children
            .iter()
            .position(|x| matches!(x, FinishedOrType::PartiallyExpanded(_)))
        {
            path.push(i);
            self.expand(path, possibles, table, stack, max_length, n);
        } else if path.is_empty() {
            let x: FinishedExpr<'src, Expr<'src>> = self.h.try_into().unwrap();
            match table.get(&x) {
                Some(x) => return Some(x),
                None => {
                    let h = Rc::new(x);
                    table.insert(h.clone());
                    return table.get(&h);
                }
            }
        } else {
            panic!("idk");
        }
        None
    }
}

impl<'src, T: LambdaLanguageOfThought + Clone> FinishedExpr<'src, T> {
    fn convert(pool: &RootedLambdaPool<'src, T>, i: LambdaExprRef) -> FinishedExpr<'src, T> {
        let expr = pool.get(i).clone();
        let children = expr
            .get_children()
            .map(|i| Rc::new(FinishedExpr::convert(pool, i)))
            .collect::<Vec<_>>();

        FinishedExpr { expr, children }
    }
}

impl<'src, T: LambdaLanguageOfThought + Clone> HashedExpr<'src, T> {
    fn is_done(&self) -> bool {
        self.children.iter().all(|x| match x {
            FinishedOrType::Expr(_) => true,
            FinishedOrType::PartiallyExpanded(_) | FinishedOrType::Type(_) => false,
        })
    }
}

#[derive(Debug, Error)]
#[error("This HashedExpr isn't done!")]
struct FinishingError;

impl<'src, T: LambdaLanguageOfThought + Clone + Debug + PartialOrd + Ord>
    TryFrom<HashedExpr<'src, T>> for FinishedExpr<'src, T>
{
    type Error = FinishingError;
    fn try_from(value: HashedExpr<'src, T>) -> Result<FinishedExpr<'src, T>, FinishingError> {
        let mut children: Vec<_> = value
            .children
            .into_iter()
            .map(|x| match x {
                FinishedOrType::Expr(e) => Ok(e),
                _ => Err(FinishingError),
            })
            .collect::<Result<_, _>>()?;

        if value.expr.commutative() {
            children.sort();
        }

        Ok(FinishedExpr {
            expr: value.expr,
            children,
        })
    }
}

impl<'src, T: LambdaLanguageOfThought + Clone + Debug> From<LambdaExpr<'src, T>>
    for HashedExpr<'src, T>
{
    fn from(value: LambdaExpr<'src, T>) -> Self {
        let children = match &value {
            LambdaExpr::LanguageOfThoughtExpr(e) => {
                e.get_arguments().map(FinishedOrType::Type).collect()
            }
            LambdaExpr::BoundVariable(..) | LambdaExpr::FreeVariable(..) => vec![],
            LambdaExpr::Lambda(_, t) => {
                //not quite right but we need this here otherwise it will falsely get considered
                //"done"
                vec![FinishedOrType::Type(t.clone())]
            }
            e => {
                println!("{e:?}");
                todo!()
            }
        };

        HashedExpr {
            children,
            expr: value,
        }
    }
}

impl<'src, T: LambdaLanguageOfThought + Clone> From<RootedLambdaPool<'src, T>>
    for FinishedExpr<'src, T>
{
    fn from(value: RootedLambdaPool<'src, T>) -> Self {
        FinishedExpr::convert(&value, value.root)
    }
}

impl<'src, T: LambdaLanguageOfThought + Clone> From<FinishedExpr<'src, T>>
    for RootedLambdaPool<'src, T>
{
    fn from(value: FinishedExpr<'src, T>) -> Self {
        let mut pool = vec![None];
        let mut stack = vec![(Rc::new(value), LambdaExprRef(0))];
        while let Some((x, i)) = stack.pop() {
            for x in x.children.iter().cloned() {
                stack.push((x, LambdaExprRef((pool.len()) as u32)));
                pool.push(None);
            }
            let mut e = x.expr.clone();
            e.change_children(
                (0..e.n_children())
                    .rev()
                    .map(|i| LambdaExprRef((pool.len() - i - 1) as u32)),
            );
            pool[i.0 as usize] = Some(e);
        }

        RootedLambdaPool {
            pool: LambdaPool(pool.into_iter().collect::<Option<_>>().unwrap()),
            root: LambdaExprRef(0),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum ExprOrType<'src, T: LambdaLanguageOfThought> {
    Type {
        lambda_type: LambdaType,
        is_app_subformula: bool,
    },
    Expr(LambdaExpr<'src, T>),
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct PartialExpr<'src, T: LambdaLanguageOfThought> {
    pool: Vec<ExprOrType<'src, T>>,
    edges: Vec<(usize, usize)>,
    position: Option<usize>,
}

impl<'src, T: LambdaLanguageOfThought + Clone + Debug> PartialExpr<'src, T> {
    fn to_pool(&self) -> RootedLambdaPool<'src, T> {
        let mut pool = self
            .pool
            .iter()
            .map(|x| match x {
                ExprOrType::Type { .. } => None,
                ExprOrType::Expr(lambda_expr) => Some(lambda_expr.clone()),
            })
            .collect::<Option<Vec<_>>>()
            .unwrap();

        for (i, x) in pool.iter_mut().enumerate() {
            let children = self.edges.iter().filter_map(|(src, dest)| {
                if *src == i {
                    Some(LambdaExprRef(*dest as u32))
                } else {
                    None
                }
            });
            x.change_children(children);
        }

        RootedLambdaPool {
            pool: LambdaPool(pool),
            root: LambdaExprRef(0),
        }
    }

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
            if let ExprOrType::Expr(lambda_expr) = &self.pool[parent]
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
        filter: impl Fn(&LambdaExpr<'src, T>, Option<&LambdaExpr<'src, T>>) -> bool,
    ) -> impl Iterator<Item = Self> {
        let ExprOrType::Type {
            lambda_type,
            is_app_subformula: _,
        } = &self.pool[self.position.unwrap()]
        else {
            panic!()
        };
        let variables = self.variables(self.position.unwrap(), lambda_type);

        let mut terms = possibles.terms(lambda_type, false, variables);

        let parent = self.parent(self.position.unwrap()).map(|x| {
            let ExprOrType::Expr(lambda_expr) = &self.pool[x] else {
                panic!()
            };
            lambda_expr
        });

        terms.retain(|x| filter(x.expr(), parent));

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
            LambdaExpr::Lambda(_, t) => {
                self.pool.push(ExprOrType::Type {
                    lambda_type: t.clone(),
                    is_app_subformula: false,
                });
                self.edges
                    .push((self.position.unwrap(), self.pool.len() - 1));
            }
            e => {
                println!("{e:?}");
                todo!()
            }
        }
        self.pool[self.position.unwrap()] = ExprOrType::Expr(lambda_expr);

        self.position = self
            .pool
            .iter()
            .position(|x| matches!(x, ExprOrType::Type { .. }));

        self
    }
}

impl<'src> PossibleExpressions<'src, Expr<'src>> {
    ///Enumerate over all possible expressions of type [`t`]
    pub fn enumerate(
        &self,
        t: &LambdaType,
        max_length: usize,
    ) -> Vec<RootedLambdaPool<'src, Expr<'src>>> {
        let x: PartialExpr<'src, Expr<'src>> = PartialExpr::new(t);
        let mut stack = vec![x];
        let mut done = vec![];
        while let Some(s) = stack.pop() {
            if s.pool.len() > max_length {
                continue;
            }
            for x in s.expand_position(self, |x, y| {
                !(matches!(
                    x,
                    LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(MonOp::Not, _))
                ) && matches!(
                    y,
                    Some(LambdaExpr::LanguageOfThoughtExpr(Expr::Unary(
                        MonOp::Not,
                        _
                    )))
                ))
            }) {
                if x.done() {
                    done.push(x.to_pool());
                } else {
                    stack.push(x);
                }
            }
        }
        done
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn convert_to_weak() -> anyhow::Result<()> {
        let x = RootedLambdaPool::parse("lambda a x some_e(e, pe_run(e), AgentOf(x, e))")?;
        let y: FinishedExpr<_> = x.clone().into();
        let x2: RootedLambdaPool<_> = y.into();
        println!("{x2:?}");
        assert_eq!(x.to_string(), x2.to_string());

        Ok(())
    }

    #[test]
    fn new_enumerate() -> anyhow::Result<()> {
        let actors = ["john", "mary", "phil", "sue"];
        let actor_properties = ["a"];
        let event_properties = ["e"];
        let possibles = PossibleExpressions::new(&actors, &actor_properties, &event_properties);
        let t = vec![
            LambdaType::A,
            LambdaType::E,
            LambdaType::T,
            LambdaType::at().clone(),
            LambdaType::et().clone(),
        ];
        for t in t {
            let d = possibles.alt_enumerator(&t, 10).collect::<Vec<_>>();
            for x in d {
                let o = x.get_type()?;
                assert_eq!(o, t);
            }
        }
        Ok(())
    }
}
