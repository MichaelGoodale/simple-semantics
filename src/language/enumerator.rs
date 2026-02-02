use std::{
    collections::BinaryHeap,
    fmt::Debug,
    hash::Hash,
    rc::{Rc, Weak},
};

use ahash::{HashMap, HashMapExt, HashSet};
use itertools::{Either, repeat_n};
use thiserror::Error;
use weak_table::WeakHashSet;

use crate::{
    lambda::{
        LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, LambdaPool, RootedLambdaPool,
        types::LambdaType,
    },
    language::{Expr, MonOp, PossibleExpressions},
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
    constant_function: bool,
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
struct Node<'src>(usize, ExprWrapper<'src, Expr<'src>>);

impl PartialOrd for Node<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Node<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.0.cmp(&self.0)
    }
}

#[derive(Debug, Clone)]
pub struct Enumerator<'a, 'src> {
    max_length: usize,
    stack: BinaryHeap<Node<'src>>,
    table: WeakHashSet<Weak<FinishedExpr<'src, Expr<'src>>>>,
    done: HashSet<Rc<FinishedExpr<'src, Expr<'src>>>>,
    possibles: &'a PossibleExpressions<'src, Expr<'src>>,
}

impl<'src> Iterator for Enumerator<'_, 'src> {
    type Item = RootedLambdaPool<'src, Expr<'src>>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(Node(n, x)) = self.stack.pop() {
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
    pub fn enumerator<'a>(&'a self, t: &LambdaType, max_length: usize) -> Enumerator<'a, 'src> {
        let mut stack: Vec<HashedExpr<_>> = self
            .terms(
                t,
                false,
                std::iter::empty(),
                possible_applications(t, std::iter::empty()),
            )
            .into_iter()
            .map(|x| {
                let (e, a) = x.into_expr();
                let mut h: HashedExpr<_> = e.into();
                if let LambdaExpr::Lambda(_, _) = h.expr {
                    h.children = vec![FinishedOrType::Type(t.rhs().unwrap().clone())];
                } else if let LambdaExpr::Application { .. } = h.expr {
                    let (arg, func) = a.unwrap();
                    h.children = vec![FinishedOrType::Type(arg), FinishedOrType::Type(func)];
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
                Node(
                    1 + h.children.len(),
                    ExprWrapper {
                        variables: std::iter::once(h.expr.var_type().cloned())
                            .flatten()
                            .collect(),
                        h,
                    },
                )
            })
            .collect();

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

fn possible_applications<'a>(
    t: &'a LambdaType,
    variables: impl Iterator<Item = &'a LambdaType>,
) -> impl Iterator<Item = (LambdaType, LambdaType)> + 'a {
    let mut possible_types: HashMap<LambdaType, HashSet<LambdaType>> = HashMap::new();
    let mut new_types: HashSet<(&LambdaType, &LambdaType)> = HashSet::default();
    let mut base_types: HashSet<_> = variables.collect();
    base_types.insert(LambdaType::a());
    base_types.insert(LambdaType::e());
    base_types.insert(LambdaType::t());
    base_types.insert(LambdaType::at());
    base_types.insert(LambdaType::et());

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

    match possible_types.remove(t) {
        Some(x) => Either::Left(
            x.into_iter()
                .map(|x| (LambdaType::compose(x.clone(), t.clone()), x.clone())),
        ),
        None => Either::Right(std::iter::empty()),
    }
}

impl<'src> ExprWrapper<'src, Expr<'src>> {
    fn is_constant(&self) -> bool {
        self.h
            .children
            .iter()
            .filter_map(|x| match x {
                FinishedOrType::Expr(e) => Some(e.constant_function),
                FinishedOrType::PartiallyExpanded(e) => Some(e.is_constant()),
                _ => None,
            })
            .any(|x| x)
    }

    fn expand(
        mut self,
        mut path: Vec<usize>,
        possibles: &PossibleExpressions<'src, Expr<'src>>,
        table: &mut WeakHashSet<Weak<FinishedExpr<'src, Expr<'src>>>>,
        stack: &mut BinaryHeap<Node<'src>>,
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
            let mut terms = possibles.terms(
                typ,
                false,
                this.variables
                    .iter()
                    .rev()
                    .enumerate()
                    .filter(|(_, x)| x == &typ)
                    .map(|(i, x)| LambdaExpr::BoundVariable(i, x.clone())),
                possible_applications(typ, this.variables.iter()),
            );

            terms.retain(|x| {
                (x.expr().n_children() + n
                    - if matches!(x.expr(), LambdaExpr::Application { .. }) {
                        1
                    } else {
                        0
                    })
                    <= max_length
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
                    let (e, a) = x.into_expr();
                    let mut h = HashedExpr::from(e);
                    if let LambdaExpr::Lambda(_, _) = h.expr {
                        h.children = vec![FinishedOrType::Type(typ.rhs().unwrap().clone())];
                    } else if let LambdaExpr::Application { .. } = h.expr {
                        let (arg, func) = a.unwrap();
                        h.children = vec![FinishedOrType::Type(arg), FinishedOrType::Type(func)];
                    }

                    h
                })
                .collect::<Vec<_>>();

            let this_variables = this.variables.clone();
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
                    if !parent.is_constant() {
                        stack.push(Node(n, parent));
                    }
                } else {
                    let mut variables = this_variables.clone();
                    if let Some(t) = h.expr.var_type() {
                        variables.push(t.clone());
                    }

                    let this = get_this(&mut parent, &path);

                    let n = n + h.children.len()
                        - if matches!(h.expr, LambdaExpr::Application { .. }) {
                            1
                        } else {
                            0
                        };
                    let e = ExprWrapper { h, variables };
                    this.h.children[i] = FinishedOrType::PartiallyExpanded(e);

                    if !parent.is_constant() {
                        stack.push(Node(n, parent));
                    }
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
            if !x.constant_function {
                match table.get(&x) {
                    Some(x) => return Some(x),
                    None => {
                        let h = Rc::new(x);
                        table.insert(h.clone());
                        return table.get(&h);
                    }
                }
            }
        } else {
            panic!("this path should never occur");
        }
        None
    }
}

impl<'src, T: LambdaLanguageOfThought + Clone> FinishedExpr<'src, T> {
    fn has_variable(&self, typ: &LambdaType, depth: usize) -> bool {
        if let LambdaExpr::BoundVariable(d, x) = &self.expr
            && d == &depth
            && x == typ
        {
            true
        } else {
            self.children
                .iter()
                .any(|x| x.has_variable(typ, depth + if self.expr.inc_depth() { 1 } else { 0 }))
        }
    }

    fn convert(pool: &RootedLambdaPool<'src, T>, i: LambdaExprRef) -> FinishedExpr<'src, T> {
        let expr = pool.get(i).clone();
        let children = expr
            .get_children()
            .map(|i| Rc::new(FinishedExpr::convert(pool, i)))
            .collect::<Vec<_>>();

        let constant_function = if children.iter().any(|x| x.constant_function) {
            true
        } else if let Some(t) = expr.var_type() {
            !children.iter().any(|x| x.has_variable(t, 0))
        } else {
            false
        };

        FinishedExpr {
            expr,
            children,
            constant_function,
        }
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

        let constant_function = if children.iter().any(|x| x.constant_function) {
            true
        } else if let Some(t) = value.expr.var_type() {
            !children.iter().any(|x| x.has_variable(t, 0))
        } else {
            false
        };

        if value.expr.commutative() {
            children.sort();
        }

        Ok(FinishedExpr {
            expr: value.expr,
            constant_function,
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
            LambdaExpr::Application { .. } => {
                vec![
                    FinishedOrType::Type(LambdaType::A),
                    FinishedOrType::Type(LambdaType::T),
                ]
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
        let actors = ["john"]; //, "mary", "phil", "sue"];
        let actor_properties = ["a"];
        let event_properties = ["e"];
        let possibles = PossibleExpressions::new(&actors, &actor_properties, &event_properties);
        let t = vec![
            LambdaType::A,
            LambdaType::E,
            LambdaType::T,
            LambdaType::at().clone(),
            LambdaType::et().clone(),
            LambdaType::from_string("<<a,t>,t>").unwrap(),
        ];
        for t in t {
            for x in possibles.enumerator(&t, 4) {
                println!("{x}");
                let o = x.get_type()?;
                assert_eq!(o, t);
            }
        }
        Ok(())
    }
}
