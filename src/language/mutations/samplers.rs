use super::UnbuiltExpr;
use ahash::HashMap;
use rand::seq::IndexedRandom;
use std::{borrow::Cow, collections::hash_map::Entry};

use super::*;
use crate::{
    Actor, PropertyLabel,
    lambda::{ExpressionType, types::LambdaType},
};

#[derive(Debug, Copy, Clone)]
pub enum SampleDetails {
    LambdaExpr,
    LambdaVar(usize),
    QuantifierVar(Variable),
    Other(usize),
}

impl SampleDetails {
    fn new(e: &UnbuiltExpr) -> Self {
        match e {
            UnbuiltExpr::Variable(variable) => SampleDetails::QuantifierVar(*variable),
            UnbuiltExpr::Lambda(..) => SampleDetails::LambdaExpr,
            UnbuiltExpr::BoundVariable(n, _) => SampleDetails::LambdaVar(*n),
            _ => panic!(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct RandomExprConfig {
    lambda_weight: f64,
    variable_weight: f64,
    depth_rapidness: f64,
}

impl RandomExprConfig {
    fn new(lambda_weight: f64, variable_weight: f64, depth_weight: f64) -> Self {
        Self {
            lambda_weight,
            variable_weight,
            depth_rapidness: depth_weight,
        }
    }
}

impl Default for RandomExprConfig {
    fn default() -> Self {
        Self {
            lambda_weight: 1.0,
            variable_weight: 1.0,
            depth_rapidness: 4.0,
        }
    }
}
pub enum ExprDistribution<'a, 'src, 'typ, 'conf> {
    KnownChildren {
        exprs: Vec<Cow<'a, UnbuiltExpr<'src, 'typ>>>,
    },
    UnknownChildren {
        exprs: Vec<(Cow<'a, UnbuiltExpr<'src, 'typ>>, SampleDetails)>,
        depth: usize,
        config: &'conf RandomExprConfig,
    },
}

impl<'src, 'typ> ExprDistribution<'_, 'src, 'typ, '_> {
    pub fn choose(self, rng: &mut impl Rng) -> UnbuiltExpr<'src, 'typ> {
        match self {
            ExprDistribution::KnownChildren { exprs } => {
                let e = exprs.choose(rng).unwrap();
                e.clone().into_owned()
            }
            ExprDistribution::UnknownChildren {
                exprs,
                config,
                depth,
            } => {
                if depth == 0 {
                    let e = exprs.choose(rng).unwrap().clone().0;
                    e.into_owned()
                } else {
                    let depth = depth as f64;
                    let e = &exprs
                        .choose_weighted(rng, |(_, e)| match e {
                            SampleDetails::LambdaExpr => {
                                let pareto =
                                    (2.0) / (((depth / config.depth_rapidness) + 1.5).powf(3.0));
                                config.lambda_weight * pareto
                            }
                            SampleDetails::LambdaVar(_) | SampleDetails::QuantifierVar(_) => {
                                let pareto =
                                    (1.0) / (((depth / config.depth_rapidness) + 1.5).powf(2.0));
                                config.variable_weight * pareto
                            }
                            SampleDetails::Other(n_args) => {
                                //This is the pareto PDF with x_m=1 and alpha=(n_args+1)
                                //scaled by depth_rapidness and shifted to the right by 1
                                let n_args = *n_args as f64;
                                (n_args + 1.0)
                                    / (((depth / config.depth_rapidness) + 1.5).powf(n_args + 2.0))
                            }
                        })
                        .unwrap()
                        .0;
                    e.clone().into_owned()
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct PossibleExpressions<'src, 'typ, 'conf> {
    expressions: HashMap<LambdaType, HashMap<Vec<LambdaType>, Vec<UnbuiltExpr<'src, 'typ>>>>,
    config: &'conf RandomExprConfig,
}

impl<'src, 'typ, 'conf> PossibleExpressions<'src, 'typ, 'conf> {
    pub fn new(
        actors: &[Actor<'src>],
        actor_properties: &[PropertyLabel<'src>],
        event_properties: &[PropertyLabel<'src>],
        config: &'conf RandomExprConfig,
    ) -> Self {
        let mut all_expressions: Vec<UnbuiltExpr> = vec![
            UnbuiltExpr::Constant(Constant::Everyone),
            UnbuiltExpr::Constant(Constant::EveryEvent),
            UnbuiltExpr::Unary(MonOp::Not),
            UnbuiltExpr::Binary(BinOp::And),
            UnbuiltExpr::Binary(BinOp::Or),
            UnbuiltExpr::Quantifier(Quantifier::Existential, ActorOrEvent::Actor),
            UnbuiltExpr::Quantifier(Quantifier::Universal, ActorOrEvent::Actor),
            UnbuiltExpr::Quantifier(Quantifier::Existential, ActorOrEvent::Event),
            UnbuiltExpr::Quantifier(Quantifier::Universal, ActorOrEvent::Event),
            UnbuiltExpr::Binary(BinOp::AgentOf),
            UnbuiltExpr::Binary(BinOp::PatientOf),
        ];

        all_expressions.extend(actors.iter().map(|x| UnbuiltExpr::Actor(*x)));

        all_expressions.extend(actor_properties.iter().flat_map(|i| {
            [
                UnbuiltExpr::Unary(MonOp::Property(*i, ActorOrEvent::Actor)),
                UnbuiltExpr::Constant(Constant::Property(*i, ActorOrEvent::Actor)),
            ]
        }));
        all_expressions.extend(event_properties.iter().flat_map(|i| {
            [
                UnbuiltExpr::Unary(MonOp::Property(*i, ActorOrEvent::Event)),
                UnbuiltExpr::Constant(Constant::Property(*i, ActorOrEvent::Event)),
            ]
        }));

        let mut expressions: HashMap<LambdaType, HashMap<_, Vec<_>>> = HashMap::default();
        for expr in all_expressions {
            let ExpressionType { output, arguments } = expr.get_expression_type();

            //Annoying match to avoid cloning arguments
            match expressions.entry(output) {
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

        PossibleExpressions {
            expressions,
            config,
        }
    }

    pub fn possiblities_fixed_children<'a>(
        &'a self,
        lambda_type: &'typ LambdaType,
        arguments: &'typ [LambdaType],
        context: &Context<'typ>,
    ) -> ExprDistribution<'a, 'src, 'typ, 'conf> {
        let mut possibilities: Vec<Cow<'a, UnbuiltExpr<'src, 'typ>>> = self
            .expressions
            .get(lambda_type)
            .map(|x| {
                x.get(arguments)
                    .map(|x| x.iter().map(Cow::Borrowed).collect::<Vec<_>>())
                    .unwrap_or_default()
            })
            .unwrap_or_default();

        if arguments.len() == 1 {
            if let Ok((lhs, rhs)) = lambda_type.split() {
                if rhs == arguments.first().unwrap() {
                    possibilities.push(Cow::Owned(UnbuiltExpr::Lambda(lhs, rhs)));
                }
            }
        } else if arguments.is_empty() {
            possibilities.extend(context.lambda_variables(lambda_type).map(Cow::Owned));
            if lambda_type == LambdaType::a() {
                possibilities.extend(context.actor_variables().map(Cow::Owned));
            } else if lambda_type == LambdaType::e() {
                possibilities.extend(context.event_variables().map(Cow::Owned));
            }
        }

        ExprDistribution::KnownChildren {
            exprs: possibilities,
        }
    }

    pub fn possibilities<'a>(
        &'a self,
        lambda_type: &'typ LambdaType,
        context: &Context<'typ>,
    ) -> ExprDistribution<'a, 'src, 'typ, 'conf> {
        let mut possibilities: Vec<_> = self
            .expressions
            .get(lambda_type)
            .map(|x| {
                x.iter()
                    .filter(|(k, _)| !has_e_argument(k) || context.can_sample_event())
                    .flat_map(|(k, v)| {
                        v.iter()
                            .map(|x| (Cow::Borrowed(x), SampleDetails::Other(k.len())))
                    })
                    .collect()
            })
            .unwrap_or_default();

        if let Ok((lhs, rhs)) = lambda_type.split() {
            let e = Cow::Owned(UnbuiltExpr::Lambda(lhs, rhs));
            let det = SampleDetails::new(&e);
            possibilities.push((e, det));
        }

        possibilities.extend(context.lambda_variables(lambda_type).map(|e| {
            let d = SampleDetails::new(&e);
            (Cow::Owned(e), d)
        }));

        if lambda_type == LambdaType::a() {
            possibilities.extend(context.actor_variables().map(|e| {
                let d = SampleDetails::new(&e);
                (Cow::Owned(e), d)
            }));
        } else if lambda_type == LambdaType::e() {
            possibilities.extend(context.event_variables().map(|e| {
                let d = SampleDetails::new(&e);
                (Cow::Owned(e), d)
            }));
        }

        ExprDistribution::UnknownChildren {
            exprs: possibilities,
            config: self.config,
            depth: context.depth(),
        }
    }
}

fn has_e_argument(v: &[LambdaType]) -> bool {
    v.iter().any(|v| v == LambdaType::e())
}
