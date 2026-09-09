//! Allows for enumerating expressions up to a fixed size.

use ahash::{HashMap, HashMapExt};
use indexmap::IndexSet;
use itertools::iproduct;
use std::{cmp::Reverse, collections::BTreeSet, fmt::Debug, hash::Hash};

use crate::lambda::{
    Bvar, LambdaExpr, LambdaExprRef, LambdaLanguageOfThought, RootedLambdaPool, types::LambdaType,
};

///A struct which is used to enumerate all expressions of a given Language of Thought.
///
///It automatically normalizes expressions to their beta-eta normal form as well as simplifying
///repeated involutory expressions (e.g. repeated negation) and avoids degenerate functions
///(constant functions or functions that produce constant functions)
pub struct Generator<'src, T> {
    exprs: IndexSet<LambdaExpr<'src, T>>,
    expr_variable_usage: HashMap<ExprId, UsedVars>,
    contexts: IndexSet<Context>,
    types: IndexSet<LambdaType>,
    constants: HashMap<TypeId, Vec<ExprId>>,
    memo: HashMap<(ContextId, TypeId, usize), Vec<ExprId>>,
    possible_types_memo: HashMap<BTreeSet<TypeId>, Vec<BTreeSet<TypeId>>>,
}

///The ID of an expression in a [`Generator`]. See [`Generator::to_rooted_lambda_pool`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprId(usize);

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
    fn variables<T>(&self, typ: TypeId, g: &Generator<'_, T>) -> Vec<Bvar> {
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

    #[expect(dead_code)]
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

fn mk_ctx<T>(g: &mut Generator<'_, T>, parent: ContextId, typ: TypeId) -> ContextId {
    let c = Context::Context { parent, typ };
    let (x, _) = g.contexts.insert_full(c);
    ContextId(x)
}

fn possible_size_table<T>(
    g: &mut Generator<'_, T>,
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
        let mut table = (1..=max_size).map(|_| BTreeSet::new()).collect::<Vec<_>>();
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

fn single_elements<T: Hash + Eq + LambdaLanguageOfThought>(
    g: &mut Generator<'_, T>,
    c: ContextId,
    typ: TypeId,
) -> Vec<ExprId> {
    let mut exprs: Vec<ExprId> = vec![];
    let vars = g.id_to_context(c).unwrap().variables(typ, g);
    if !vars.is_empty() {
        let t = g.id_to_type(typ).unwrap().clone();
        exprs.extend(
            std::iter::repeat_n(t, vars.len())
                .zip(vars)
                .map(|(t, bvar)| mk_expr(g, LambdaExpr::<T>::BoundVariable(bvar, t))),
        );
    }

    if let Some(x) = g.constants.get(&typ) {
        exprs.extend(x.iter().copied());
    }

    exprs
}

fn applications<T: Hash + Eq + LambdaLanguageOfThought>(
    g: &mut Generator<'_, T>,
    c: ContextId,
    typ: TypeId,
    size: usize,
    exprs: &mut Vec<ExprId>,
) {
    //This first part finds any possible types that we can apply with.
    let types = possible_size_table(g, c, size - 1);

    //Must return typ and its arg must be accessible
    let types = types
        .iter()
        .copied()
        .filter(|subformula_type| {
            if let Some((lhs, rhs)) = g.type_children_or_insert(*subformula_type)
                && rhs == typ
                && types.contains(&lhs)
            {
                true
            } else {
                false
            }
        })
        .collect::<BTreeSet<_>>();

    //Go over all formulae and argument combos across sizes.
    for t in types {
        let (lhs, _) = g.type_children_or_insert(t).unwrap();

        for formula_size in 1..size {
            let arg_size = size - formula_size;
            let mut formulae = generate(g, c, t, formula_size);
            //App(Lambda x f(x), y) is a possible beta reduction, so we don't do it.
            formulae.retain(|x| !matches!(g.exprs[x.0], LambdaExpr::Lambda(..)));

            let args = generate(g, c, lhs, arg_size);

            exprs.extend(iproduct!(formulae, args).filter_map(|(f, x)| {
                if is_involutory(f, x, g) {
                    None
                } else {
                    Some(mk_expr(
                        g,
                        LambdaExpr::<T>::Application {
                            subformula: LambdaExprRef(u32::try_from(f.0).unwrap()),
                            argument: LambdaExprRef(u32::try_from(x.0).unwrap()),
                        },
                    ))
                }
            }));
        }
    }
}

fn lambda_exprs<T: Hash + Eq + LambdaLanguageOfThought>(
    g: &mut Generator<'_, T>,
    c: ContextId,
    typ: (TypeId, TypeId),
    size: usize,
    exprs: &mut Vec<ExprId>,
) {
    let (arg_type, res_type) = typ;
    let c = mk_ctx(g, c, arg_type);
    let mut bodies = generate(g, c, res_type, size - 1);

    bodies.retain(|f_body| uses_its_function(*f_body, g) && !could_be_eta(*f_body, g));

    let arg_type = g.id_to_type(arg_type).unwrap().clone();

    exprs.extend(
        std::iter::repeat_n(arg_type, bodies.len())
            .zip(bodies)
            .map(|(t, body)| {
                mk_expr(
                    g,
                    LambdaExpr::<T>::Lambda(LambdaExprRef(u32::try_from(body.0).unwrap()), t),
                )
            }),
    );
}

fn generate<T: Hash + Eq + LambdaLanguageOfThought>(
    g: &mut Generator<'_, T>,
    c: ContextId,
    typ: TypeId,
    size: usize,
) -> Vec<ExprId> {
    let arg_key = (c, typ, size);
    if let Some(x) = g.memo.get(&arg_key) {
        return x.clone();
    }

    let exprs = if size == 1 {
        single_elements(g, c, typ)
    } else if size >= 2 {
        let mut exprs = vec![];
        applications(g, c, typ, size, &mut exprs);
        if let Some(lhs_rhs) = g.type_children_or_insert(typ) {
            lambda_exprs(g, c, lhs_rhs, size, &mut exprs);
        }
        exprs
    } else {
        vec![]
    };

    g.memo.insert(arg_key, exprs.clone());

    exprs
}

///Checks if `f_body` has a variable to bind.
fn uses_its_function<T>(f_body: ExprId, g: &Generator<'_, T>) -> bool {
    g.expr_variable_usage
        .get(&f_body)
        .is_some_and(UsedVars::has_zero_var)
}

///Checks if this is applying a involutory function to an expression with that involutory function
///as root. E.g. app(f, app(f, x)) where f is involutory (this allows us to simplify !!p to p.
fn is_involutory<T: LambdaLanguageOfThought + PartialEq>(
    f: ExprId,
    x: ExprId,
    g: &Generator<'_, T>,
) -> bool {
    let LambdaExpr::LanguageOfThoughtExpr(outer_expr, _) = g.exprs.get_index(f.0).unwrap() else {
        return false;
    };

    if !outer_expr.involutory() {
        return false;
    }

    let LambdaExpr::Application { subformula, .. } = g.exprs.get_index(x.0).unwrap() else {
        return false;
    };
    let LambdaExpr::LanguageOfThoughtExpr(inner_expr, _) = g
        .exprs
        .get_index(usize::try_from(subformula.0).unwrap())
        .unwrap()
    else {
        return false;
    };

    outer_expr == inner_expr
}

///this expression ID, if put inside a lambda, would be the site of an eta reduction.
fn could_be_eta<T>(f_body: ExprId, g: &Generator<'_, T>) -> bool {
    let x = g.exprs.get_index(f_body.0).unwrap();
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

impl<T> Generator<'_, T> {
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

    ///Gets all expressions of type `t` up to `max_size`, if it has already been computed. Use
    ///[`Generator::enumerate_or_generate`] to actually generate expressions.
    #[must_use]
    pub fn enumerate(&self, t: &LambdaType, max_size: usize) -> Option<Vec<ExprId>> {
        if max_size == 0 {
            return Some(vec![]);
        }
        let t = self.type_id(t)?;
        (1..=max_size)
            .map(|size| self.memo.get(&(ContextId(0), t, size)).cloned())
            .collect::<Option<Vec<_>>>()
            .map(|x| x.into_iter().flatten().collect())
    }
}

impl<'src, T: LambdaLanguageOfThought + Clone> Generator<'src, T> {
    ///Converts an [`ExprId`] in a given [`Generator`] to a [`RootedLambdaPool<'src, T>`].
    ///Will be [`None`] if `x` is undefined.
    #[must_use]
    pub fn to_rooted_lambda_pool(&self, x: ExprId) -> Option<RootedLambdaPool<'src, T>> {
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
    ///Gets all expressions of type `t` up to `max_size`.
    pub fn enumerate_or_generate(&mut self, t: LambdaType, max_size: usize) -> Vec<ExprId> {
        let t = self.type_id_or_insert(t);
        let mut v = vec![];
        for size in (1..=max_size).rev() {
            if let Some(exprs) = self.memo.get(&(ContextId(0), t, size)) {
                v.extend(exprs.iter().rev().cloned());
            } else {
                let exprs = generate(self, ContextId(0), t, size);
                v.extend(exprs.into_iter().rev())
            }
        }
        v.reverse();
        v
    }

    ///Creates a new [`Generator`].
    #[must_use]
    pub fn new(base_expressions: Vec<T>) -> Generator<'src, T> {
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

        let types = vec![
            //(LambdaType::A, 45),
            //(LambdaType::E, 8),
            //(LambdaType::at().clone(), 176),
            (LambdaType::et().clone(), 52),
            // (LambdaType::from_string("<<a,t>,t>").unwrap(), 262),
            // (LambdaType::T, 2068),
        ];

        let mut generator: Generator<Expr> = Generator::new(expressions.to_vec());
        for (ty, count) in types {
            println!("{ty}");
            //let mut pool_set = HashSet::new();
            //let mut reduced_pool_set = HashSet::new();

            let size = 6;
            let pools = generator.enumerate_or_generate(ty.clone(), size);
            //assert_eq!(pools.len(), count);
            for pool in pools {
                let expr = generator.to_rooted_lambda_pool(pool).unwrap();
                println!("\t{expr}");
                assert!(expr.is_reduced(), "{expr} is not fully reduced");
                assert!(expr.appless_len() <= size);
                let o = expr.get_type()?;
                assert_eq!(o, ty);
            }
        }
        Ok(())
    }
}
