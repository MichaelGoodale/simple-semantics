use super::UnbuiltExpr;
use ahash::HashMap;
use rand::seq::{IndexedRandom, WeightError};
use std::{borrow::Cow, collections::hash_map::Entry};

use super::*;
use crate::{
    Actor, PropertyLabel,
    lambda::{ExpressionType, types::LambdaType},
};

#[derive(Debug, Copy, Clone)]
pub(super) enum SampleDetails {
    LambdaExpr,
    Other(usize),
}

#[derive(Debug, Clone, Copy)]
pub struct RandomExprConfig {
    lambda_weight: f64,
    depth_rapidness: f64,
}

impl RandomExprConfig {
    pub fn new(lambda_weight: f64, depth_weight: f64) -> Self {
        Self {
            lambda_weight,
            depth_rapidness: depth_weight,
        }
    }
}

impl Default for RandomExprConfig {
    fn default() -> Self {
        Self {
            lambda_weight: 1.0,
            depth_rapidness: 4.0,
        }
    }
}
pub enum ExprDistribution<'a, 'src, 'typ, 'conf> {
    KnownChildren {
        exprs: Vec<Cow<'a, UnbuiltExpr<'src, 'typ>>>,
        context: &'a Context<'typ>,
    },
    UnknownChildren {
        exprs: Vec<Cow<'a, UnbuiltExpr<'src, 'typ>>>,
        depth: usize,
        config: &'conf RandomExprConfig,
        context: &'a Context<'typ>,
    },
}

#[derive(Debug, Clone, Error)]
pub enum SamplingError {
    #[error("Can't find an expr of type {0}!")]
    CantFindExpr(LambdaType),
    #[error("Can't find an expr of type {t} with args {}!", args.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "))]
    CantFindExprWithArgs {
        t: LambdaType,
        args: Vec<LambdaType>,
    },
    #[error("Issue with sampling: {0}!")]
    DistributionError(#[from] WeightError),
}

impl<'src, 'typ> ExprDistribution<'_, 'src, 'typ, '_> {
    pub fn choose(self, rng: &mut impl Rng) -> Result<UnbuiltExpr<'src, 'typ>, SamplingError> {
        match self {
            ExprDistribution::KnownChildren { exprs, context } => {
                let e = exprs
                    .choose_weighted(rng, |e| e.can_satisfy(context).to_f64())
                    .unwrap();
                Ok(e.clone().into_owned())
            }
            ExprDistribution::UnknownChildren {
                exprs,
                config,
                depth,
                context,
            } => {
                if depth == 0 {
                    let e = exprs
                        .choose_weighted(rng, |e| e.can_satisfy(context).to_f64())
                        .unwrap()
                        .clone();
                    Ok(e.into_owned())
                } else {
                    let depth = depth as f64;
                    let e = exprs.choose_weighted(rng, |e| {
                        //This is the pareto PDF with x_m=1 and alpha=(n_args+1)
                        //scaled by depth_rapidness and shifted to the right by 1
                        let n_args = e.n_children() as f64;

                        let score = ((n_args + 1.0)
                            / (((depth / config.depth_rapidness) + 1.5).powf(n_args + 2.0)))
                        .abs();
                        score + e.can_satisfy(context).to_f64()
                    })?;
                    Ok((*e).clone().into_owned())
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum Satisfaction {
    ImmediatelySatisfy,
    DirectlySatisfy,
    IndirectlySatify,
    CantSatify,
}

impl Satisfaction {
    fn to_f64(self) -> f64 {
        match self {
            Satisfaction::ImmediatelySatisfy => 8000.0,
            Satisfaction::DirectlySatisfy => 3000.0,
            Satisfaction::IndirectlySatify => 2.0,
            Satisfaction::CantSatify => 1.0,
        }
    }
}

impl<'src, 'typ> UnbuiltExpr<'src, 'typ> {
    ///Whether a given expr can lead to a variable being satified
    fn can_satisfy(&self, context: &Context<'typ>) -> Satisfaction {
        let s = Satisfaction::CantSatify;
        if let UnbuiltExpr::BoundVariable(k, b) = self {
            if context
                .all_variables()
                .filter(|(_, d, _)| !d)
                .any(|(t, _, id)| id == *k && t == *b)
            {
                Satisfaction::ImmediatelySatisfy
            } else {
                Satisfaction::CantSatify
            }
        } else {
            if self.n_children() == 0 {
                return Satisfaction::CantSatify;
            }
            let ExpressionType { arguments, .. } = self.get_expression_type();

            let arguments: Vec<_> = arguments.into_iter().map(Some).collect();
            let mut nothing_to_satisfy = true;
            let mut has_all = true;
            for t in context
                .all_variables()
                .filter_map(|(t, used, _)| if used { None } else { Some(t) })
            {
                nothing_to_satisfy = false;

                ///check if an argument has been used somehow
                if !arguments.contains(t) {
                    has_all = false;
                }
            }

            if nothing_to_satisfy {
                return Satisfaction::CantSatify;
            } else if has_all {
                return Satisfaction::DirectlySatisfy;
            }

            if arguments.contains(LambdaType::t()) {
                Satisfaction::IndirectlySatify
            } else {
                Satisfaction::CantSatify
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

        all_expressions.extend(actors.iter().map(|x| UnbuiltExpr::Actor(x)));

        all_expressions.extend(actor_properties.iter().flat_map(|i| {
            [
                UnbuiltExpr::Unary(MonOp::Property(i, ActorOrEvent::Actor)),
                UnbuiltExpr::Constant(Constant::Property(i, ActorOrEvent::Actor)),
            ]
        }));
        all_expressions.extend(event_properties.iter().flat_map(|i| {
            [
                UnbuiltExpr::Unary(MonOp::Property(i, ActorOrEvent::Event)),
                UnbuiltExpr::Constant(Constant::Property(i, ActorOrEvent::Event)),
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
        context: &'a Context<'typ>,
    ) -> Result<ExprDistribution<'a, 'src, 'typ, 'conf>, SamplingError> {
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
            possibilities.extend(context.variables(lambda_type).map(Cow::Owned));
        }

        if possibilities.is_empty() {
            return Err(SamplingError::CantFindExprWithArgs {
                t: lambda_type.clone(),
                args: arguments.to_vec(),
            });
        }

        Ok(ExprDistribution::KnownChildren {
            exprs: possibilities,
            context,
        })
    }

    pub fn possibilities<'a>(
        &'a self,
        lambda_type: &'typ LambdaType,
        context: &'a Context<'typ>,
    ) -> Result<ExprDistribution<'a, 'src, 'typ, 'conf>, SamplingError> {
        let mut possibilities: Vec<_> = self
            .expressions
            .get(lambda_type)
            .map(|x| {
                x.iter()
                    .filter(|(k, _)| !has_e_argument(k) || context.can_sample_event())
                    .flat_map(|(_, v)| v.iter().map(Cow::Borrowed))
                    .collect()
            })
            .unwrap_or_default();

        if let Ok((lhs, rhs)) = lambda_type.split() {
            let e = Cow::Owned(UnbuiltExpr::Lambda(lhs, rhs));
            possibilities.push(e);
        }

        possibilities.extend(context.variables(lambda_type).map(Cow::Owned));

        if possibilities.is_empty() {
            return Err(SamplingError::CantFindExpr(lambda_type.clone()));
        }

        Ok(ExprDistribution::UnknownChildren {
            exprs: possibilities,
            config: self.config,
            depth: context.depth(),
            context,
        })
    }
}

fn has_e_argument(v: &[LambdaType]) -> bool {
    v.iter().any(|v| v == LambdaType::e())
}
