use ahash::HashMap;
use std::{borrow::Cow, collections::hash_map::Entry};

use super::*;
use crate::{Actor, PropertyLabel, lambda::types::LambdaType};

///A struct which defines a HashMap of all types and expressions.
///The outer HashMap is for the return types of expressions and the inner HashMap is for their
///arguments. Then there is a vector of all possible lambda expressions with that output type and
///input arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PossibleExpressions<'src, T> {
    expressions: HashMap<LambdaType, HashMap<Vec<LambdaType>, Vec<LambdaExpr<'src, T>>>>,
}

impl<'src, T> From<HashMap<LambdaType, HashMap<Vec<LambdaType>, Vec<LambdaExpr<'src, T>>>>>
    for PossibleExpressions<'src, T>
{
    fn from(
        value: HashMap<LambdaType, HashMap<Vec<LambdaType>, Vec<LambdaExpr<'src, T>>>>,
    ) -> Self {
        PossibleExpressions { expressions: value }
    }
}

impl<'src> PossibleExpressions<'src, Expr<'src>> {
    ///Create a new [`PossibleExpressions`] for [`Expr`].
    pub fn new(
        actors: &[Actor<'src>],
        actor_properties: &[PropertyLabel<'src>],
        event_properties: &[PropertyLabel<'src>],
    ) -> Self {
        let bad_ref = ExprRef(0);
        let mut all_expressions: Vec<_> = [
            //Expr::Constant(Constant::Everyone),
            //Expr::Constant(Constant::EveryEvent),
            Expr::Unary(MonOp::Not, bad_ref),
            Expr::Binary(BinOp::And, bad_ref, bad_ref),
            Expr::Binary(BinOp::Or, bad_ref, bad_ref),
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var_type: ActorOrEvent::Actor,
                subformula: bad_ref,
                restrictor: bad_ref,
            },
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var_type: ActorOrEvent::Actor,
                subformula: bad_ref,
                restrictor: bad_ref,
            },
            Expr::Quantifier {
                quantifier: Quantifier::Existential,
                var_type: ActorOrEvent::Event,
                subformula: bad_ref,
                restrictor: bad_ref,
            },
            Expr::Quantifier {
                quantifier: Quantifier::Universal,
                var_type: ActorOrEvent::Event,
                subformula: bad_ref,
                restrictor: bad_ref,
            },
            Expr::Binary(BinOp::AgentOf, bad_ref, bad_ref),
            Expr::Binary(BinOp::PatientOf, bad_ref, bad_ref),
        ]
        .to_vec();

        all_expressions.extend(actors.iter().map(|x| Expr::Actor(x)));

        all_expressions.extend(actor_properties.iter().flat_map(|i| {
            [
                Expr::Unary(MonOp::Property(i, ActorOrEvent::Actor), bad_ref),
                //Expr::Constant(Constant::Property(i, ActorOrEvent::Actor)),
            ]
        }));
        all_expressions.extend(event_properties.iter().flat_map(|i| {
            [
                Expr::Unary(MonOp::Property(i, ActorOrEvent::Event), bad_ref),
                //Expr::Constant(Constant::Property(i, ActorOrEvent::Event)),
            ]
        }));

        let mut expressions: HashMap<LambdaType, HashMap<_, Vec<_>>> = HashMap::default();
        for expr in all_expressions.into_iter() {
            let output = expr.get_type();
            let arguments = expr.get_arguments().collect();
            let expr = LambdaExpr::LanguageOfThoughtExpr(expr);
            //Annoying match to avoid cloning arguments
            match expressions.entry(output.clone()) {
                Entry::Occupied(mut occupied) => {
                    let inner_h: &mut HashMap<_, _> = occupied.get_mut();
                    match inner_h.entry(arguments) {
                        Entry::Occupied(mut occupied) => occupied.get_mut().push(expr),
                        Entry::Vacant(vacant) => {
                            vacant.insert(vec![expr]);
                        }
                    }
                }
                Entry::Vacant(vacant) => {
                    vacant.insert([(arguments, vec![expr])].into_iter().collect());
                }
            }
        }

        PossibleExpressions { expressions }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct PossibleExpr<'a, 'src, T: LambdaLanguageOfThought + Clone> {
    expr: Cow<'a, LambdaExpr<'src, T>>,
    app_details: Option<(LambdaType, LambdaType)>,
}

impl<'a, 'src, T: LambdaLanguageOfThought + Clone> PossibleExpr<'a, 'src, T> {
    pub fn into_expr(self) -> (LambdaExpr<'src, T>, Option<(LambdaType, LambdaType)>) {
        (self.expr.into_owned(), self.app_details)
    }

    fn new_borrowed(expr: &'a LambdaExpr<'src, T>) -> Self {
        PossibleExpr {
            expr: Cow::Borrowed(expr),
            app_details: None,
        }
    }

    fn new_owned(expr: LambdaExpr<'src, T>) -> Self {
        PossibleExpr {
            expr: Cow::Owned(expr),
            app_details: None,
        }
    }

    fn new_application(subformula: LambdaType, argument: LambdaType) -> Self {
        PossibleExpr {
            expr: Cow::Owned(LambdaExpr::Application {
                subformula: LambdaExprRef(0),
                argument: LambdaExprRef(0),
            }),
            app_details: Some((subformula, argument)),
        }
    }
}

impl<'src, T: LambdaLanguageOfThought + Clone> PossibleExpressions<'src, T> {
    pub(super) fn possibilities<'a>(
        &'a self,
        lambda_type: &LambdaType,
        is_subformula: bool,
        context: &Context,
    ) -> Vec<PossibleExpr<'a, 'src, T>> {
        let mut possibilities = vec![];
        if !is_subformula {
            if let Some(x) = self.expressions.get(lambda_type).map(|x| {
                x.iter()
                    .filter(|(k, _)| !has_e_argument(k) || context.can_sample_event())
                    .flat_map(|(_, v)| v.iter().map(PossibleExpr::new_borrowed))
            }) {
                possibilities.extend(x);
            }

            if let Ok((lhs, _)) = lambda_type.split() {
                let e = PossibleExpr::new_owned(LambdaExpr::Lambda(LambdaExprRef(0), lhs.clone()));
                possibilities.push(e);
            }
        }

        possibilities.extend(context.variables(lambda_type).map(PossibleExpr::new_owned));
        possibilities.extend(
            context
                .applications(lambda_type)
                .map(|(subformula, argument)| PossibleExpr::new_application(subformula, argument)),
        );

        possibilities
    }

    pub(super) fn possiblities_fixed_children<'a>(
        &'a self,
        lambda_type: &LambdaType,
        arguments: &[LambdaType],
        var_type: Option<&LambdaType>,
        context: &Context,
    ) -> Vec<Cow<'a, LambdaExpr<'src, T>>> {
        let mut possibilities: Vec<Cow<'a, LambdaExpr<'src, T>>> = self
            .expressions
            .get(lambda_type)
            .map(|x| {
                x.get(arguments)
                    .map(|x| x.iter().map(Cow::Borrowed).collect::<Vec<_>>())
                    .unwrap_or_default()
            })
            .unwrap_or_default();

        if arguments.len() == 2
            && let Ok((arg_type, return_type)) = arguments.first().unwrap().split()
            && return_type == lambda_type
            && arg_type == arguments.last().unwrap()
        {
            possibilities.push(Cow::Owned(LambdaExpr::Application {
                subformula: LambdaExprRef(0),
                argument: LambdaExprRef(0),
            }))
        } else if arguments.len() == 1
            && let Ok((lhs, rhs)) = lambda_type.split()
            && rhs == arguments.first().unwrap()
        {
            possibilities.push(Cow::Owned(LambdaExpr::Lambda(
                LambdaExprRef(0),
                lhs.clone(),
            )));
        } else if arguments.is_empty() {
            possibilities.extend(context.variables(lambda_type).map(Cow::Owned));
        }

        if var_type.is_some() {
            possibilities.retain(|x| x.var_type() == var_type);
        }

        possibilities
    }
}

fn has_e_argument(v: &[LambdaType]) -> bool {
    v.iter().any(|v| v == LambdaType::e())
}
