//! Allows for enumerating expressions up to a fixed size.

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

#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord)]
enum MetaVariable {
    Known(TypeId),
    Unknown(TypeVar),
    Function(Box<MetaVariable>, Box<MetaVariable>),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
struct TypeVar(u32);

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
struct Substitutions {
    parents: BTreeMap<TypeVar, TypeVar>,
    values: BTreeMap<TypeVar, Option<MetaVariable>>,
}

impl MetaVariable {
    fn used_type_vars(&self) -> MetaVariableReferredVars<'_> {
        MetaVariableReferredVars(vec![self])
    }
}

struct MetaVariableReferredVars<'a>(Vec<&'a MetaVariable>);

impl Iterator for MetaVariableReferredVars<'_> {
    type Item = TypeVar;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(x) = self.0.pop() {
            match x {
                MetaVariable::Known(_) => (),
                MetaVariable::Unknown(t) => return Some(*t),
                MetaVariable::Function(a, b) => self.0.extend([&**a, &**b]),
            }
        }
        None
    }
}

enum DFSStatus {
    Visiting,
    Visited,
}

impl Substitutions {
    fn new() -> Substitutions {
        Substitutions {
            parents: BTreeMap::new(),
            values: BTreeMap::new(),
        }
    }

    fn probe_value(&mut self, x: TypeVar) -> Option<MetaVariable> {
        if !self.parents.contains_key(&x) {
            self.values.insert(x, None);
            self.parents.insert(x, x);
        }
        let x = self.find(x);
        self.values.get(&x).unwrap().clone()
    }

    fn union(mut self, other: Self) -> Result<Self, ()> {
        for (&x, &par) in &other.parents {
            self.unify_var_var(x, par)?;
        }

        for (o_root, x) in other.values {
            let root = self.find(o_root);
            let v = merge(&self.values[&root], &x)?.cloned();
            *self.values.get_mut(&root).unwrap() = v;
        }

        if self.cyclic_values() {
            return Err(());
        }

        Ok(self)
    }

    fn cyclic_values(&self) -> bool {
        let mut status = BTreeMap::new();
        for key in self.values.keys() {
            let mut stack = vec![(*key, true)];
            if status.contains_key(key) {
                continue;
            }

            while let Some((s, new)) = stack.pop() {
                if !new {
                    status.insert(s, DFSStatus::Visited);
                    continue;
                }

                match status.get(&s) {
                    Some(DFSStatus::Visiting) => return true,
                    Some(DFSStatus::Visited) => continue,
                    None => (),
                }

                status.insert(s, DFSStatus::Visiting);
                stack.push((s, false));

                if let Some(v) = self.values.get(&s).unwrap() {
                    for x in v.used_type_vars() {
                        match status.get(&x) {
                            Some(DFSStatus::Visiting) => return true,
                            Some(DFSStatus::Visited) => {}
                            None => stack.push((self.root(x).unwrap(), true)),
                        }
                    }
                }
            }
        }
        false
    }

    fn root(&self, mut x: TypeVar) -> Option<TypeVar> {
        while *self.parents.get(&x)? != x {
            x = self.parents[&x];
        }

        Some(x)
    }

    ///Get root of `x`.
    fn find(&mut self, mut x: TypeVar) -> TypeVar {
        if !self.parents.contains_key(&x) {
            self.values.insert(x, None);
            self.parents.insert(x, x);
            return x;
        }

        let mut root = x;

        while self.parents[&root] != root {
            root = self.parents[&root];
        }

        while self.parents[&x] != x {
            let next = self.parents[&x];
            *self.parents.get_mut(&x).unwrap() = root;
            x = next;
        }
        root
    }

    fn unify_var_var(&mut self, a_id: TypeVar, b_id: TypeVar) -> Result<MetaVariable, ()> {
        let root_a = self.find(a_id);
        let root_b = self.find(b_id);
        if root_a == root_b {
            let v = self.values.get(&root_a).unwrap().clone();
            return Ok(v.unwrap_or(MetaVariable::Unknown(root_a)));
        }

        if self.values[&root_a]
            .as_ref()
            .is_some_and(|x| x.contains_var_mapped_to_root(root_b, self))
            || self.values[&root_b]
                .as_ref()
                .is_some_and(|x| x.contains_var_mapped_to_root(root_a, self))
        {
            return Err(());
        }

        if let Ok(v) = merge(&self.values[&root_a], &self.values[&root_b]) {
            let v = v.cloned();
            let new_root = std::cmp::min(root_a, root_b);
            let child = std::cmp::max(root_a, root_b);
            *self.parents.get_mut(&child).unwrap() = new_root;
            self.values.remove(&child);
            *self.values.get_mut(&new_root).unwrap() = v.clone();
            Ok(v.unwrap_or(MetaVariable::Unknown(new_root)))
        } else {
            Err(())
        }
    }

    fn unify_var_value(&mut self, a_id: TypeVar, b: MetaVariable) -> Result<MetaVariable, ()> {
        let root_a = self.find(a_id);
        if let Ok(v) = merge(&self.values[&root_a], &Some(b)) {
            let v = v.cloned();
            *self.values.get_mut(&root_a).unwrap() = v.clone();
            Ok(v.unwrap_or(MetaVariable::Unknown(root_a)))
        } else {
            Err(())
        }
    }
}

fn merge<'a>(
    a: &'a Option<MetaVariable>,
    b: &'a Option<MetaVariable>,
) -> Result<Option<&'a MetaVariable>, ()> {
    match (a, b) {
        (None, None) => Ok(None),
        (None, Some(x)) | (Some(x), None) => Ok(Some(x)),
        (Some(y), Some(x)) => {
            if x == y {
                Ok(Some(x))
            } else {
                Err(())
            }
        }
    }
}

#[cfg(test)]
fn to_letters(mut n: u32) -> String {
    let mut result = String::new();

    loop {
        result.push((b'A' + (n % 26) as u8) as char);
        n /= 26;

        if n == 0 {
            break;
        }

        n -= 1;
    }

    result.chars().rev().collect()
}

#[cfg(test)]
fn to_string_inner<T>(x: &MetaVariable, g: &Generator<T>, s: &mut String) {
    match x {
        MetaVariable::Known(t) => s.push_str(&g.id_to_type(*t).unwrap().to_string()),
        MetaVariable::Unknown(x) => s.push_str(&to_letters(x.0)),
        MetaVariable::Function(x, y) => {
            s.push('<');
            to_string_inner(x, g, s);
            s.push(',');
            to_string_inner(y, g, s);
            s.push('>');
        }
    }
}

impl MetaVariable {
    #[cfg(test)]
    fn to_string<T>(&self, g: &Generator<T>) -> String {
        let mut s = String::new();
        to_string_inner(self, g, &mut s);
        s
    }

    fn normalize<T>(self, subs: &mut Substitutions, g: &mut Generator<T>) -> MetaVariable {
        match self {
            MetaVariable::Known(type_id) => MetaVariable::Known(type_id),
            MetaVariable::Unknown(x) => match subs.probe_value(x) {
                Some(ty) => ty.normalize(subs, g),
                None => MetaVariable::Unknown(subs.find(x)),
            },
            MetaVariable::Function(x, y) => {
                let x = x.normalize(subs, g);
                let y = y.normalize(subs, g);
                match (x, y) {
                    (MetaVariable::Known(lhs), MetaVariable::Known(rhs)) => {
                        MetaVariable::Known(g.ids_to_function(lhs, rhs))
                    }
                    (x, y) => MetaVariable::Function(
                        Box::new(x.normalize(subs, g)),
                        Box::new(y.normalize(subs, g)),
                    ),
                }
            }
        }
    }

    fn contains_var_mapped_to_root(&self, v: TypeVar, subs: &Substitutions) -> bool {
        match self {
            MetaVariable::Known(_) => false,
            MetaVariable::Unknown(x) => subs.root(*x).unwrap() == v,
            MetaVariable::Function(a, b) => {
                a.contains_var_mapped_to_root(v, subs) || b.contains_var_mapped_to_root(v, subs)
            }
        }
    }

    fn unify<T>(self, other: Self, subs: &mut Substitutions, g: &mut Generator<T>) -> Option<Self> {
        let left = self.normalize(subs, g);
        let right = other.normalize(subs, g);

        let x = match (left, right) {
            (MetaVariable::Known(a), MetaVariable::Known(b)) => {
                (a == b).then_some(MetaVariable::Known(a))
            }
            (MetaVariable::Function(x1, y1), MetaVariable::Function(x2, y2)) => {
                let x = x1.unify(*x2, subs, g)?;
                let y = y1.unify(*y2, subs, g)?;
                Some(MetaVariable::Function(Box::new(x), Box::new(y)))
            }
            (MetaVariable::Unknown(a), MetaVariable::Unknown(b)) => subs.unify_var_var(a, b).ok(),
            (MetaVariable::Unknown(x), y) | (y, MetaVariable::Unknown(x)) => {
                let x = subs.find(x);
                let y = y.normalize(subs, g);
                if y.contains_var_mapped_to_root(x, subs) {
                    return None;
                }
                subs.unify_var_value(x, y).ok()
            }
            (MetaVariable::Known(t), MetaVariable::Function(l1, r1))
            | (MetaVariable::Function(l1, r1), MetaVariable::Known(t)) => {
                let (l2, r2) = g.type_children_or_insert(t)?;
                l1.unify(MetaVariable::Known(l2), subs, g)?;
                r1.unify(MetaVariable::Known(r2), subs, g)?;
                Some(MetaVariable::Known(t))
            }
        };

        x.map(|x| x.normalize(subs, g))
    }

    #[cfg(test)]
    fn can_unify<T>(self, other: Self, g: &mut Generator<T>) -> Option<Self> {
        let mut subs = Substitutions::new();
        self.unify(other, &mut subs, g)
    }

    #[cfg(test)]
    fn biggest_element(&self) -> TypeVar {
        let mut fresh = 0;
        let mut stack = vec![self];
        while let Some(x) = stack.pop() {
            match x {
                MetaVariable::Known(_) => (),
                MetaVariable::Unknown(x) => fresh = std::cmp::max(x.0, fresh),
                MetaVariable::Function(f, a) => stack.extend([&**f, &**a]),
            }
        }
        TypeVar(fresh)
    }

    fn split<T>(&self, g: &mut Generator<T>) -> Option<(MetaVariable, MetaVariable)> {
        match self {
            MetaVariable::Known(type_id) => g
                .type_children_or_insert(*type_id)
                .map(|(lhs, rhs)| (MetaVariable::Known(lhs), MetaVariable::Known(rhs))),
            MetaVariable::Unknown(_type_var) => None,
            MetaVariable::Function(x, y) => Some(((**x).clone(), (**y).clone())),
        }
    }
}

#[cfg(test)]
fn possible_types<T>(
    g: &mut Generator<T>,
    t: MetaVariable,
    c: BTreeSet<MetaVariable>,
    size: usize,
    on_app_lhs: bool,
) -> BTreeSet<MetaVariable> {
    let fresh = std::cmp::max(
        c.iter().map(MetaVariable::biggest_element).max().unwrap().0,
        t.biggest_element().0,
    ) + 1;
    possible_types_inner(g, t, c, size, on_app_lhs, fresh)
        .into_iter()
        .map(|(a, mut subs)| a.normalize(&mut subs, g))
        .collect()
}

//need to modify it so that it returns any substitutions!

fn possible_types_inner<T>(
    g: &mut Generator<T>,
    t: MetaVariable,
    mut c: BTreeSet<MetaVariable>,
    size: usize,
    on_app_lhs: bool,
    fresh: u32,
) -> BTreeSet<(MetaVariable, Substitutions)> {
    if size == 0 {
        BTreeSet::default()
    } else if size == 1 {
        c.iter()
            .cloned()
            .filter_map(|x| {
                let mut subs = Substitutions::new();
                x.unify(t.clone(), &mut subs, g).map(|x| (x, subs))
            })
            .collect()
    } else {
        let mut types = BTreeSet::new();
        for i in 1..size {
            let j = size - 1;
            let arg = MetaVariable::Unknown(TypeVar(fresh));
            let f = MetaVariable::Function(Box::new(arg.clone()), Box::new(t.clone()));

            //get any possible types of form <A, t> of w/ size i
            let functions = possible_types_inner(g, f.clone(), c.clone(), i, true, fresh + 1);
            let args = possible_types_inner(g, arg.clone(), c.clone(), j, false, fresh + 1);

            types.extend(iproduct!(&functions, &args).filter_map(
                |((f, f_subs), (a, arg_subs))| {
                    let mut subs = f_subs.clone().union(arg_subs.clone()).ok()?;
                    let f = f.clone().normalize(&mut subs, g);
                    let a = a.clone().normalize(&mut subs, g);
                    let function_with_arg =
                        MetaVariable::Function(Box::new(a.clone()), Box::new(t.clone()));
                    f.unify(function_with_arg, &mut subs, g)
                        .and_then(|x| x.split(g))
                        .map(|(_, y)| (y, subs))
                },
            ));
        }

        if let MetaVariable::Unknown(_) = &t
            && !on_app_lhs
        {
            let body = MetaVariable::Unknown(TypeVar(fresh));
            let arg = MetaVariable::Unknown(TypeVar(fresh + 1));
            let mut c = c.clone();
            c.insert(arg.clone());
            let new_types =
                possible_types_inner(g, body.clone(), c, size - 1, on_app_lhs, fresh + 2);
            types.extend(new_types.into_iter().filter_map(|(found_body, mut subs)| {
                let f = MetaVariable::Function(Box::new(arg.clone()), Box::new(found_body));
                f.unify(t.clone(), &mut subs, g).map(|x| (x, subs))
            }));
        }

        //check if under app_lhs to remove App(lambda x, y) since that's a beta reducible thing.
        if let MetaVariable::Function(arg, rhs) = &t
            && !on_app_lhs
        {
            c.insert(*arg.clone());
            //lhs should be added to c, but not sure how to handle meta variables where lambda x x
            let new_types =
                possible_types_inner(g, *rhs.clone(), c.clone(), size - 1, on_app_lhs, fresh);
            types.extend(new_types.into_iter().filter_map(|(found_body, mut subs)| {
                let x = MetaVariable::Function(arg.clone(), Box::new(found_body));
                x.unify(t.clone(), &mut subs, g).map(|x| (x, subs))
            }));
        }

        types
    }
}

fn possible_application_types<T>(
    g: &mut Generator<'_, T>,
    c: ContextId,
    typ: TypeId,
    formula_size: usize,
    arg_size: usize,
) -> BTreeSet<(TypeId, TypeId)> {
    let mut c = g.id_to_context(c).unwrap();
    let mut vars = BTreeSet::new();
    while let Context::Context {
        parent,
        typ: this_typ,
    } = c
    {
        vars.insert(MetaVariable::Known(*this_typ));
        c = g.id_to_context(*parent).unwrap();
    }
    vars.extend(g.constants.keys().map(|x| MetaVariable::Known(*x)));
    let arg = MetaVariable::Unknown(TypeVar(0));
    let f = MetaVariable::Function(Box::new(arg.clone()), Box::new(MetaVariable::Known(typ)));

    let function_types = possible_types_inner(g, f, vars.clone(), formula_size, true, 1);
    let arg_types = possible_types_inner(g, arg, vars, arg_size, true, 1);

    let mut combos = BTreeSet::new();

    for (f, f_subs) in &function_types {
        for (arg, a_subs) in &arg_types {
            let Ok(mut subs) = f_subs.clone().union(a_subs.clone()) else {
                continue;
            };

            let other_f =
                MetaVariable::Function(Box::new(arg.clone()), Box::new(MetaVariable::Known(typ)));
            let Some(f) = f.clone().unify(other_f, &mut subs, g) else {
                continue;
            };

            if let MetaVariable::Known(t) = f {
                let (lhs, _) = g.type_children_or_insert(t).unwrap();
                combos.insert((t, lhs));
            } else {
                panic!("Idk what to do if a meta variable is returned here")
            }
        }
    }

    combos
}

fn applications<T: Hash + Eq + LambdaLanguageOfThought>(
    g: &mut Generator<'_, T>,
    c: ContextId,
    typ: TypeId,
    size: usize,
    exprs: &mut Vec<ExprId>,
) {
    for formula_size in 1..size {
        let arg_size = size - formula_size;

        for (formula_t, arg_t) in possible_application_types(g, c, typ, formula_size, arg_size) {
            let mut formulae = generate(g, c, formula_t, formula_size);
            //App(Lambda x f(x), y) is a possible beta reduction, so we don't do it.
            formulae.retain(|x| !matches!(g.exprs[x.0], LambdaExpr::Lambda(..)));

            let args = generate(g, c, arg_t, arg_size);

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

    fn ids_to_function(&mut self, lhs: TypeId, rhs: TypeId) -> TypeId {
        let lhs = self.types.get_index(lhs.0).unwrap().clone();
        let rhs = self.types.get_index(rhs.0).unwrap().clone();
        let f = LambdaType::compose(lhs, rhs);
        self.type_id_or_insert(f)
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
                v.extend(exprs.iter().rev().copied());
            } else {
                let exprs = generate(self, ContextId(0), t, size);
                v.extend(exprs.into_iter().rev());
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
        }
    }
}
#[cfg(test)]
mod test {

    use crate::language::{ActorOrEvent, Constant::Property, Expr};

    use super::*;
    #[test]
    fn test_possible_types() -> anyhow::Result<()> {
        let expressions = vec![
            Expr::Actor("John"),
            Expr::Constant(Property("a", ActorOrEvent::Actor)),
            Expr::Constant(Property("e", ActorOrEvent::Event)),
        ];
        let mut g: Generator<Expr> = Generator::new(expressions);

        for t in [
            MetaVariable::Unknown(TypeVar(0)),
            MetaVariable::Function(
                Box::new(MetaVariable::Unknown(TypeVar(0))),
                Box::new(MetaVariable::Unknown(TypeVar(0))),
            ),
            MetaVariable::Function(
                Box::new(MetaVariable::Unknown(TypeVar(0))),
                Box::new(MetaVariable::Unknown(TypeVar(1))),
            ),
        ] {
            for size in 1..=4 {
                print!("size={size}\ttype={}\t", t.to_string(&g));
                let c = g
                    .constants
                    .keys()
                    .map(|x| MetaVariable::Known(*x))
                    .collect::<BTreeSet<_>>();
                let types = possible_types(&mut g, t.clone(), c, size, false);
                let t = types.iter().map(|x| x.to_string(&g)).collect::<Vec<_>>();
                println!("{t:?}");
            }
        }

        Ok(())
    }

    #[test]
    fn test_unification() -> anyhow::Result<()> {
        let mut g: Generator<Expr> = Generator::new(vec![]);

        let a_to_a = MetaVariable::Function(
            Box::new(MetaVariable::Unknown(TypeVar(0))),
            Box::new(MetaVariable::Unknown(TypeVar(0))),
        );

        let u = a_to_a
            .clone()
            .can_unify(
                MetaVariable::Function(
                    Box::new(MetaVariable::Unknown(TypeVar(0))),
                    Box::new(MetaVariable::Known(g.type_id_or_insert(LambdaType::A))),
                ),
                &mut g,
            )
            .unwrap();

        assert_eq!(
            MetaVariable::Known(g.type_id_or_insert(LambdaType::from_string("<a,a>")?)),
            u,
            "{} didn't unify fully to <a,a>",
            u.to_string(&g)
        );

        let meta = MetaVariable::Function(
            Box::new(MetaVariable::Unknown(TypeVar(0))),
            Box::new(MetaVariable::Unknown(TypeVar(1))),
        );

        let types =
            ["e", "a", "t", "<e,t>", "<<e,t>, t>"].map(|s| LambdaType::from_string(s).unwrap());

        for t in types {
            let id = g.type_id_or_insert(t);
            let u = meta.clone().can_unify(MetaVariable::Known(id), &mut g);
            let t = g.id_to_type(id).unwrap();

            println!("{t}: {:?}", u.as_ref().map(|x| x.to_string(&g)));
            match t.is_function() {
                true => assert!(u.as_ref().is_some_and(|u| match u {
                    MetaVariable::Known(u) => *u == id,
                    MetaVariable::Unknown(_) | MetaVariable::Function(..) => false,
                })),
                false => assert!(u.is_none()),
            }
        }

        let a_to_a_to_b = MetaVariable::Function(
            Box::new(MetaVariable::Unknown(TypeVar(0))),
            Box::new(MetaVariable::Function(
                Box::new(MetaVariable::Unknown(TypeVar(0))),
                Box::new(MetaVariable::Unknown(TypeVar(1))),
            )),
        );

        for (meta, s, expected) in [
            (&a_to_a, "<e,e>", true),
            (&a_to_a, "<a,a>", true),
            (&a_to_a, "<e,a>", false),
            (&a_to_a, "<e,t>", false),
            (&a_to_a_to_b, "<e,<e,t>>", true),
            (&a_to_a_to_b, "<a,<a,e>>", true),
            (&a_to_a_to_b, "<e,<a,t>>", false),
            (&a_to_a_to_b, "<e,t>", false),
        ] {
            let id = g.type_id_or_insert(LambdaType::from_string(s).unwrap());
            let unified = meta
                .clone()
                .can_unify(MetaVariable::Known(id), &mut g)
                .and_then(|x| match x {
                    MetaVariable::Known(type_id) => Some(type_id),
                    MetaVariable::Unknown(_) | MetaVariable::Function(..) => None,
                });
            assert_eq!(unified, if expected { Some(id) } else { None }, "{s}");
        }

        //self reference
        let meta = MetaVariable::Unknown(TypeVar(0));
        let other = MetaVariable::Function(
            Box::new(MetaVariable::Unknown(TypeVar(0))),
            Box::new(MetaVariable::Known(
                g.type_id_or_insert(LambdaType::from_string("e").unwrap()),
            )),
        );

        assert!(meta.can_unify(other, &mut g).is_none());

        Ok(())
    }

    #[test]
    fn new_enumerate() -> anyhow::Result<()> {
        let mut expressions = vec![
            Expr::Actor("John"),
            Expr::Constant(Property("a", ActorOrEvent::Actor)),
            Expr::Constant(Property("e", ActorOrEvent::Event)),
        ];
        expressions.extend(Expr::basic_ops());

        let types = vec![
            (LambdaType::A, 45),
            (LambdaType::E, 8),
            (LambdaType::at().clone(), 176),
            (LambdaType::et().clone(), 52),
            (LambdaType::from_string("<<a,t>,t>").unwrap(), 262),
            (LambdaType::T, 2068),
        ];

        let mut generator: Generator<Expr> = Generator::new(expressions.to_vec());
        for (ty, _) in types {
            println!("{ty}");
            //let mut pool_set = HashSet::new();
            //let mut reduced_pool_set = HashSet::new();

            let size = 6;
            let pools = generator.enumerate_or_generate(ty.clone(), size);
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
