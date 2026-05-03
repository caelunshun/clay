use crate::{
    base::ErrorGuaranteed,
    semantic::{
        analysis::{ClauseCx, ClauseObligation, HrtbUniverse, ObligeCause},
        syntax::{
            InferTyVar, PrettyUniversalTyVar, Re, RelationDirection, SimpleTySet, TraitClauseList,
            TraitParam, TraitSpec, Ty, UniversalReVar, UniversalTyVar,
        },
    },
    utils::lang::{AND_LIST_GLUE, format_list},
};

// === Errors === //

macro_rules! clause_error {
    ($($name:ident),*$(,)?) => {
        #[derive(Debug, Clone)]
        pub enum ClauseError {
            $($name($name),)*
        }

        $(
            impl From<$name> for ClauseError {
                fn from(inner: $name) -> Self {
                    Self::$name(inner)
                }
            }
        )*

        impl ClauseError {
            pub fn report(&self, ccx: &ClauseCx<'_>) -> Option<ErrorGuaranteed> {
                match self {
                    $(Self::$name(err) => err.report(ccx),)*
                }
            }
        }
    };
}

clause_error! {
    RecursionLimitReached,
    ObligationUnfulfilled,
    NoTraitImplError,
    NotCoveredError,
    ReAndReUnifyError,
    TyAndTyUnifyError,
    TyAndSimpleTySetUnifyError,
}

#[derive(Debug, Clone)]
pub struct RecursionLimitReached {
    pub cause: ObligeCause,
}

impl RecursionLimitReached {
    pub fn report(&self, ccx: &ClauseCx<'_>) -> Option<ErrorGuaranteed> {
        self.cause
            .report(ccx, || "recursion limit reached".to_string())
    }
}

#[derive(Debug, Clone)]
pub struct ObligationUnfulfilled {
    pub obligation: ClauseObligation,
}

impl ObligationUnfulfilled {
    pub fn report(&self, ccx: &ClauseCx<'_>) -> Option<ErrorGuaranteed> {
        match self.obligation.clone() {
            ClauseObligation::TyUnifiesTy(_cause, _lhs, _rhs, _mode) => unreachable!(),
            ClauseObligation::TyMeetsTrait(cause, _universe, lhs, rhs) => cause.report(ccx, || {
                format!(
                    "could not make necessary inferences to show that `{lhs}` implements `{rhs}`",
                )
            }),
            ClauseObligation::TyOutlivesRe(cause, lhs, rhs, dir) => {
                cause.report(ccx, || match dir {
                    RelationDirection::LhsOntoRhs => {
                        format!(
                            "could not make necessary inferences to show that `{lhs}` outlives `{rhs}`",
                        )
                    }
                    RelationDirection::RhsOntoLhs => {
                        format!(
                            "could not make necessary inferences to show that `{rhs}` outlives `{lhs}`",
                        )
                    }
                })
            }
            ClauseObligation::UnifyReifiedElaboratedClauses(
                cause,
                univ,
                _clauses,
                _reification_state,
            ) => cause.report(ccx, || {
                format!(
                    "could not make necessary inferences to elaborate the generic clauses of `{}`",
                    PrettyUniversalTyVar(univ),
                )
            }),
            ClauseObligation::Covered(oblige_cause, hash_map, intern, trait_spec) => {
                todo!();
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct NoTraitImplError {
    pub cause: ObligeCause,
    pub target: Ty,
    pub spec: TraitSpec,
}

impl NoTraitImplError {
    pub fn report(&self, ccx: &ClauseCx<'_>) -> Option<ErrorGuaranteed> {
        self.cause.report(ccx, || {
            format!("type `{}` does not implement `{}`", self.target, self.spec)
        })
    }
}

#[derive(Debug, Clone)]
pub struct NotCoveredError {
    pub cause: ObligeCause,
    pub missing_mentions: Vec<UniversalTyVar>,
    pub in_trait: Option<TraitSpec>,
    pub in_type: Option<Ty>,
}

impl NotCoveredError {
    pub fn report(&self, ccx: &ClauseCx<'_>) -> Option<ErrorGuaranteed> {
        self.cause.report(ccx, || {
            let covered = format_list(
                self.missing_mentions
                    .iter()
                    .map(|&mention| format!("`{}`", PrettyUniversalTyVar(mention))),
                AND_LIST_GLUE,
            );

            match (self.in_trait, self.in_type) {
                (None, None) => unreachable!(),
                (None, Some(in_type)) => {
                    format!(
                        "universal type{} {covered} not covered by type `{in_type}`",
                        if self.missing_mentions.len() == 1 {
                            ""
                        } else {
                            "s"
                        },
                    )
                }
                (Some(in_trait), None) => {
                    format!(
                        "universal type{} {covered} not covered by trait `{in_trait}`",
                        if self.missing_mentions.len() == 1 {
                            ""
                        } else {
                            "s"
                        },
                    )
                }
                (Some(in_trait), Some(in_type)) => {
                    format!(
                        "universal type{} {covered} not covered by trait `{in_trait}` and type `{in_type}`",
                        if self.missing_mentions.len() == 1 {
                            ""
                        } else {
                            "s"
                        },
                    )
                }
            }
        })
    }
}

#[derive(Debug, Clone)]
pub struct ReAndReUnifyError {
    pub cause: ObligeCause,
    pub lhs: Re,
    pub rhs: Re,
    pub requires_var: UniversalReVar,
    pub to_outlive: Re,
}

impl ReAndReUnifyError {
    pub fn report(&self, ccx: &ClauseCx<'_>) -> Option<ErrorGuaranteed> {
        self.cause.report(ccx, || {
            format!(
                "cannot force `{}` to outlive `{}` without requiring universal `{}` to outlive `{}`",
                self.lhs,
                self.rhs,
                Re::UniversalVar(self.requires_var),
                self.to_outlive,
            )
        })
    }
}

#[derive(Debug, Clone)]
pub struct TyAndTyUnifyError {
    pub cause: ObligeCause,
    pub origin_lhs: Ty,
    pub origin_rhs: Ty,
    pub culprits: Vec<TyAndTyUnifyCulprit>,
}

impl TyAndTyUnifyError {
    pub fn report(&self, ccx: &ClauseCx<'_>) -> Option<ErrorGuaranteed> {
        self.cause.report(ccx, || {
            format!(
                "cannot unify types `{}` and `{}`",
                self.origin_lhs, self.origin_rhs,
            )
        })
    }
}

#[derive(Debug, Clone)]
pub enum TyAndTyUnifyCulprit {
    Types(Ty, Ty),
    ClauseLists(TraitClauseList, TraitClauseList),
    Params(TraitParam, TraitParam),
    Occurs(InferTyOccursError),
    LeaksUniversal(InferTyLeaksUniversalError),
    LeaksHrtbVar(InferTyLeaksHrtbVarError),
    NotPermittedSolid(SimpleTySet, Ty),
    NotPermittedFloating(SimpleTySet, SimpleTySet),
    UnifyDenied,
}

#[derive(Debug, Clone)]
pub struct InferTyOccursError {
    pub var: InferTyVar,
    pub occurs_in: Ty,
}

#[derive(Debug, Clone)]
pub struct InferTyLeaksUniversalError {
    pub var: InferTyVar,
    pub max_universe: HrtbUniverse,
    pub leaks_universal: UniversalTyVar,
}

#[derive(Debug, Clone)]
pub struct InferTyLeaksHrtbVarError {
    pub var: InferTyVar,
}

#[derive(Debug, Clone)]
pub struct TyAndSimpleTySetUnifyError {
    pub cause: ObligeCause,
    pub lhs: Ty,
    pub rhs: SimpleTySet,
}

impl TyAndSimpleTySetUnifyError {
    pub fn report(&self, ccx: &ClauseCx<'_>) -> Option<ErrorGuaranteed> {
        self.cause.report(ccx, || {
            format!("cannot unify types `{}` and `{:?}`", self.lhs, self.rhs)
        })
    }
}
