#![expect(dead_code)]
use ahash::{HashMap, HashMapExt};
use indexmap::IndexSet;
use itertools::iproduct;
use std::{
    cmp::Reverse,
    collections::{BTreeMap, BTreeSet},
    fmt::Debug,
    hash::Hash,
};

use crate::lambda::{
    Bvar, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, RootedLambdaPool,
    printing::VarContext, types::LambdaType,
};

struct Generator<'src, T> {
    exprs: IndexSet<LambdaExpr<'src, T>>,
    expr_variable_usage: HashMap<ExprId, UsedVars>,
    contexts: IndexSet<Context>,
    types: IndexSet<LambdaType>,
    constants: HashMap<TypeId, Vec<ExprId>>,
    memo: HashMap<(ContextId, TypeId, usize), Vec<Vec<ExprId>>>,
    possible_types_memo: HashMap<BTreeSet<TypeId>, Vec<BTreeSet<TypeId>>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ExprId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct TypeId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ContextId(usize);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Context {
    Empty,
    Context { parent: ContextId, typ: TypeId },
}

impl Context {
    fn variables<'src, T>(&self, typ: TypeId, g: &Generator<'src, T>) -> Vec<Bvar> {
        let mut v = vec![];
        let mut n = 0;

        let mut c = self;
        while let Context::Context {
            parent,
            typ: this_typ,
        } = c
        {
            if &typ == this_typ {
                v.push(n);
            }
            c = g.id_to_context(*parent).unwrap();
            n += 1;
        }

        v
    }
}

///A sorted, unique vector of the variables used in an expression.
#[derive(Default, Debug, Clone, Eq, PartialEq)]
struct UsedVars(Vec<Reverse<Bvar>>);

impl UsedVars {
    fn single(x: Bvar) -> Self {
        UsedVars(vec![Reverse(x)])
    }

    fn insert(&mut self, x: Bvar) {
        let x = Reverse(x);
        if let Err(pos) = self.0.binary_search(&x) {
            self.0.insert(pos, x);
        }
    }

    fn extend(&mut self, other: &Self) {
        let mut result = Vec::with_capacity(self.0.len() + other.0.len());

        let mut left = self.0.drain(..).peekable();
        let mut right = other.0.iter().copied().peekable();

        while let (Some(a), Some(b)) = (left.peek(), right.peek()) {
            if a < b {
                result.push(left.next().unwrap());
            } else if b < a {
                result.push(right.next().unwrap());
            } else {
                result.push(left.next().unwrap());
                right.next();
            }
        }

        result.extend(left);
        result.extend(right);

        self.0 = result;
    }

    ///This changes the variables to pass through a lambda, it removes a zero and reduces Bvars by one.
    fn pass_through_lambda(x: &Self) -> Self {
        let mut x = x.clone();
        if x.has_zero_var() {
            x.0.pop();
        }
        x.0.iter_mut().for_each(|x| x.0 -= 1);
        x
    }

    fn has_zero_var(&self) -> bool {
        self.0.last().is_some_and(|x| x.0 == 0)
    }
}

fn mk_expr<'src, T: Hash + Eq + LambdaLanguageOfThought>(
    g: &mut Generator<'src, T>,
    expr: LambdaExpr<'src, T>,
) -> ExprId {
    let (x, novel) = g.exprs.insert_full(expr);
    if !novel {
        return ExprId(x);
    }

    //This gets all the used variables of the children of the expression, which we don't need to do
    //if the expression already exists.

    let used_vars = match g.exprs.get_index(x).unwrap() {
        LambdaExpr::BoundVariable(bvar, _) => Some(UsedVars::single(*bvar)),
        LambdaExpr::FreeVariable(..) => None,
        LambdaExpr::Lambda(body, _) => g
            .expr_variable_usage
            .get(&ExprId(usize::try_from(body.0).unwrap()))
            .map(UsedVars::pass_through_lambda),
        LambdaExpr::LanguageOfThoughtExpr(
            _,
            super::ExprType::BindVar(_) | super::ExprType::BindVarTwoBodies(..),
        ) => {
            panic!("Syncategorematic terms are not supported in enumeration");
        }
        expr @ (LambdaExpr::Application { .. } | LambdaExpr::LanguageOfThoughtExpr(..)) => expr
            .get_children()
            .filter_map(|child| {
                g.expr_variable_usage
                    .get(&ExprId(usize::try_from(child.0).unwrap()))
            })
            .fold(None, |mut acc: Option<UsedVars>, vars| {
                match &mut acc {
                    Some(used_vars) => used_vars.extend(vars),
                    None => acc = Some(vars.clone()),
                }
                acc
            }),
    };

    //We only store variables if there are any.
    if let Some(used_vars) = used_vars
        && !used_vars.0.is_empty()
    {
        g.expr_variable_usage.insert(ExprId(x), used_vars);
    }

    ExprId(x)
}

fn mk_ctx<'src, T>(g: &mut Generator<'src, T>, parent: ContextId, typ: TypeId) -> ContextId {
    let c = Context::Context { parent, typ };
    let (x, _) = g.contexts.insert_full(c);
    ContextId(x)
}

fn possible_size_table<'src, T>(
    g: &mut Generator<'src, T>,
    ctx: ContextId,
    max_size: usize,
) -> BTreeSet<TypeId> {
    let mut c = g.id_to_context(ctx).unwrap();
    let mut ctx_vars = BTreeSet::new();
    while let Context::Context { typ, parent } = c {
        ctx_vars.insert(*typ);
        c = g.id_to_context(*parent).unwrap();
    }

    let mut start = 1;

    let mut table = if let Some(x) = g.possible_types_memo.get(&ctx_vars) {
        if x.len() < max_size {
            let mut v = g.possible_types_memo.remove(&ctx_vars).unwrap();
            start = v.len();
            v.extend((v.len()..max_size).map(|_| BTreeSet::new()));
            v
        } else {
            return x[max_size - 1].clone();
        }
    } else {
        let mut table = (1..(max_size + 1))
            .map(|_| BTreeSet::new())
            .collect::<Vec<_>>();
        //If there is a constant, then we can make the LHS of an app of that type with 1 expression.
        table[0] = g.constants.keys().copied().collect();
        table
    };

    let types = &mut g.types;

    debug_assert_eq!(table.len(), max_size);

    for current_size in start..max_size {
        let [curr, old] = table
            .get_disjoint_mut([current_size, current_size - 1])
            .unwrap();
        curr.extend(old.iter().copied());

        //apps
        for i in 1..current_size {
            //The size of i and j sum to current_size, so we can make anything of that size;
            let j = current_size - i;
            let bodies = table[i]
                .iter()
                .filter_map(|x| {
                    let t = types.get_index(x.0).unwrap();
                    if let Ok((lhs, rhs)) = t.split() {
                        let rhs = rhs.clone();
                        let lhs = TypeId(types.insert_full(lhs.clone()).0);
                        let rhs = TypeId(types.insert_full(rhs).0);
                        Some((lhs, rhs))
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();

            let [args, current] = table.get_disjoint_mut([j, current_size]).unwrap();

            for (arg, res) in bodies {
                if args.contains(&arg) {
                    current.insert(res);
                }
            }
        }
    }

    let ret = table[max_size - 1].clone();
    g.possible_types_memo.insert(ctx_vars, table.clone());
    ret
}

fn generate<'src, T: Hash + Eq + LambdaLanguageOfThought>(
    g: &mut Generator<'src, T>,
    c: ContextId,
    typ: TypeId,
    size: usize,
) -> Vec<Vec<ExprId>> {
    let arg_key = (c, typ, size);
    if let Some(x) = g.memo.get(&arg_key) {
        return x.clone();
    }

    let mut exprs: Vec<Vec<ExprId>> = (0..size).map(|_| vec![]).collect();

    let vars = g.id_to_context(c).unwrap().variables(typ, g);
    if !vars.is_empty() {
        let t = g.id_to_type(typ).unwrap().clone();
        exprs[0].extend(
            std::iter::repeat_n(t, vars.len())
                .zip(vars)
                .map(|(t, bvar)| mk_expr(g, LambdaExpr::<T>::BoundVariable(bvar, t))),
        );
    };

    if let Some(x) = g.constants.get(&typ) {
        exprs[0].extend(x.iter().copied());
    }

    if size >= 2 {
        //This first part finds any possible types that we can apply with.
        let t_subformulae = possible_size_table(g, c, size - 1);
        let t_args = possible_size_table(g, c, size - 1);

        //Must return typ and its arg must be accessible
        let t_subformulae = t_subformulae
            .into_iter()
            .filter(|subformula_type| {
                if let Some((lhs, rhs)) = g.type_children_or_insert(*subformula_type)
                    && rhs == typ
                    && t_args.contains(&lhs)
                {
                    true
                } else {
                    false
                }
            })
            .collect::<BTreeSet<_>>();

        //We don't need args that aren't used.
        let t_args = t_subformulae
            .iter()
            .map(|x| g.type_children_or_insert(*x).unwrap().0)
            .collect::<BTreeSet<_>>();

        let args = t_args
            .into_iter()
            .map(|k| (k, generate(g, c, k, size - 1)))
            .collect::<BTreeMap<_, _>>();

        let mut formulae = t_subformulae
            .into_iter()
            .map(|k| (k, generate(g, c, k, size - 1)))
            .collect::<BTreeMap<_, _>>();

        //App(Lambda x f(x), y) is a possible beta reduction, so we don't do it.
        formulae
            .values_mut()
            .flatten()
            .for_each(|x| x.retain(|x| !matches!(g.exprs[x.0], LambdaExpr::Lambda(..))));

        //Go over all formulae and argument combos across sizes.
        for (t, formulae) in formulae {
            let (lhs, _) = g.type_children_or_insert(t).unwrap();
            let args = &args[&lhs];

            for formula_j in 0..(size - 1) {
                let formulae = &formulae[formula_j];
                for arg_i in 0..(size - formula_j - 1) {
                    let args = &args[arg_i];

                    exprs[arg_i + formula_j].extend(iproduct!(formulae, args).map(|(f, x)| {
                        mk_expr(
                            g,
                            LambdaExpr::<T>::Application {
                                subformula: LambdaExprRef(u32::try_from(f.0).unwrap()),
                                argument: LambdaExprRef(u32::try_from(x.0).unwrap()),
                            },
                        )
                    }));
                }
            }
        }

        if let Ok((arg_type, res_type)) = g.id_to_type(typ).unwrap().split() {
            let res_type = res_type.clone();
            let arg_type = arg_type.clone();
            let res_type = g.type_id_or_insert(res_type);
            let arg_type_id = g.type_id_or_insert(arg_type.clone());
            let c = mk_ctx(g, c, arg_type_id);
            let mut bodies = generate(g, c, res_type, size - 1);

            bodies
                .iter_mut()
                .for_each(|x| x.retain(|x| !could_be_eta(*x, g)));

            for (i, b) in bodies.into_iter().enumerate() {
                exprs[i + 1].extend(std::iter::repeat_n(arg_type.clone(), b.len()).zip(b).map(
                    |(t, body)| {
                        mk_expr(
                            g,
                            LambdaExpr::<T>::Lambda(
                                LambdaExprRef(u32::try_from(body.0).unwrap()),
                                t,
                            ),
                        )
                    },
                ));
            }
        }
    }

    g.memo.insert(arg_key, exprs.clone());

    exprs
}

///this expression ID, if put inside a lambda, would be the site of an eta reduction.
fn could_be_eta<'src, T>(x: ExprId, g: &Generator<'src, T>) -> bool {
    let x = g.exprs.get_index(x.0).unwrap();
    let LambdaExpr::Application {
        subformula,
        argument,
    } = x
    else {
        return false;
    };

    let argument = g
        .exprs
        .get_index(usize::try_from(argument.0).unwrap())
        .unwrap();

    if !matches!(argument, LambdaExpr::BoundVariable(0, _)) {
        return false;
    }

    let Some(subformula) = g
        .expr_variable_usage
        .get(&ExprId(usize::try_from(subformula.0).unwrap()))
    else {
        return true;
    };

    //If the 0 var is never used, then we can reduce here.
    !subformula.has_zero_var()
}

impl<'src, T> Generator<'src, T> {
    fn id_to_context(&self, c: ContextId) -> Option<&Context> {
        self.contexts.get_index(c.0)
    }

    fn id_to_type(&self, t: TypeId) -> Option<&LambdaType> {
        self.types.get_index(t.0)
    }

    fn type_id(&self, t: &LambdaType) -> Option<TypeId> {
        self.types.get_index_of(t).map(TypeId)
    }

    fn type_children_or_insert(&mut self, t: TypeId) -> Option<(TypeId, TypeId)> {
        let (lhs, rhs) = self.types.get_index(t.0)?.split().ok()?;
        let lhs = lhs.clone();
        let rhs = rhs.clone();
        let lhs = self.types.insert_full(lhs).0;
        let rhs = self.types.insert_full(rhs).0;

        Some((TypeId(lhs), TypeId(rhs)))
    }

    fn type_id_or_insert(&mut self, t: LambdaType) -> TypeId {
        let (id, _) = self.types.insert_full(t);
        TypeId(id)
    }

    fn enumerate(&self, t: &LambdaType, max_size: usize) -> Option<&Vec<Vec<ExprId>>> {
        let t = self.type_id(t)?;
        self.memo.get(&(ContextId(0), t, max_size))
    }
}

impl<'src, T: LambdaLanguageOfThought + Clone> Generator<'src, T> {
    fn to_rooted_lambda_pool(&self, x: ExprId) -> Option<RootedLambdaPool<'src, T>> {
        let mut pool = vec![None];
        //check the root exists
        self.exprs.get_index(x.0)?;
        let mut stack = vec![(0, x)];

        while let Some((pool_id, x)) = stack.pop() {
            let mut expr = self
                .exprs
                .get_index(x.0)
                .expect("Invalid pool built!")
                .clone();

            let n_children = expr.n_children();
            stack.extend(
                expr.get_children()
                    .enumerate()
                    .map(|(i, x)| (pool.len() + i, ExprId(usize::try_from(x.0).unwrap()))),
            );
            expr.change_children(
                (0..n_children).map(|x| LambdaExprRef(u32::try_from(pool.len() + x).unwrap())),
            );
            pool.extend((0..n_children).map(|_| None));
            pool[pool_id] = Some(expr);
        }

        Some(RootedLambdaPool {
            pool: super::LambdaPool(pool.into_iter().collect::<Option<Vec<_>>>().unwrap()),
            root: LambdaExprRef(0),
        })
    }
}

impl<'src, T: LambdaLanguageOfThought + Hash + Eq> Generator<'src, T> {
    fn enumerate_or_generate(&mut self, t: LambdaType, max_size: usize) -> &Vec<Vec<ExprId>> {
        let t = self.type_id_or_insert(t);
        if !self.memo.contains_key(&(ContextId(0), t, max_size)) {
            generate(self, ContextId(0), t, max_size);
        }
        self.memo.get(&(ContextId(0), t, max_size)).unwrap()
    }

    fn new(base_expressions: Vec<T>) -> Generator<'src, T> {
        let mut contexts = IndexSet::new();
        contexts.insert(Context::Empty);
        assert!(contexts.get_index(0).is_some());

        let mut constants: HashMap<_, Vec<_>> = HashMap::new();
        let mut types = IndexSet::new();
        let mut exprs = IndexSet::new();

        for b in base_expressions {
            let t = b.typ();
            let (t, _) = types.insert_full(t.clone());
            let b = LambdaExpr::LanguageOfThoughtExpr(b, crate::lambda::ExprType::NoVar);
            let (b, _) = exprs.insert_full(b);
            constants.entry(TypeId(t)).or_default().push(ExprId(b));
        }

        Generator {
            exprs,
            contexts,
            constants,
            types,
            expr_variable_usage: HashMap::new(),
            memo: HashMap::new(),
            possible_types_memo: HashMap::new(),
        }
    }
}
#[cfg(test)]
mod test {

    use crate::language::{ActorOrEvent, Constant::Property, Expr};

    use super::*;

    #[test]
    fn new_enumerate() -> anyhow::Result<()> {
        let mut expressions = vec![
            Expr::Actor("John"),
            Expr::Constant(Property("a", ActorOrEvent::Actor)),
            Expr::Constant(Property("e", ActorOrEvent::Event)),
        ];
        expressions.extend(Expr::basic_ops());

        let t = vec![
            (LambdaType::A, 19),
            (LambdaType::E, 22),
            (LambdaType::T, 96),
            (LambdaType::at().clone(), 18),
            (LambdaType::et().clone(), 22),
            (LambdaType::from_string("<<a,t>,t>").unwrap(), 37),
        ];

        let mut generator: Generator<Expr> = Generator::new(expressions.to_vec());
        for (t, how_many) in t {
            println!("{t}");
            //let mut pool_set = HashSet::new();
            //let mut reduced_pool_set = HashSet::new();

            let pools = generator.enumerate_or_generate(t.clone(), 5).clone();
            for x in pools.into_iter().flatten() {
                let expr = generator.to_rooted_lambda_pool(x).unwrap();
                println!("\t{expr}");
                assert!(expr.is_reduced(), "{expr} is not fully reduced");
                let o = expr.get_type()?;
                assert_eq!(o, t);
                /*
                count += 1;
                pool_set.insert(x.clone());
                x.reduce()?;
                x.cleanup();
                reduced_pool_set.insert(x);*/
            }
            //assert_eq!(count, how_many);
            //println!("{t} {count}");
            //assert_eq!(pool_set.len(), count);
            //assert_eq!(pool_set.len(), reduced_pool_set.len());
        }
        Ok(())
    }
}
