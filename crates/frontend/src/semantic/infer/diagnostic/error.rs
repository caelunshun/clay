use crate::semantic::{
    infer::HrtbUniverse,
    syntax::{
        InferTyVar, Re, RelationMode, SimpleTySet, TraitClauseList, TraitParam, TraitSpec, Ty,
        UniversalReVar, UniversalTyVar,
    },
};

#[derive(Debug, Clone)]
pub struct RecursionLimitReached;

#[derive(Debug, Clone)]
pub struct NoTraitImplError {
    pub target: Ty,
    pub spec: TraitSpec,
}

#[derive(Debug, Clone)]
pub struct NotCoveredError {
    pub missing_mentions: Vec<UniversalTyVar>,
    pub in_trait: Option<TraitSpec>,
    pub in_type: Option<Ty>,
}

// === Re Unification Errors === //

#[derive(Debug, Clone)]
pub struct TyAndTyReUnifyError {
    pub lhs: Ty,
    pub rhs: Ty,
    pub mode: RelationMode,
    pub regions: Vec<ReAndReUnifyError>,
}

#[derive(Debug, Clone)]
pub struct ReAndReUnifyError {
    pub lhs: Re,
    pub rhs: Re,
    pub requires_var: UniversalReVar,
    pub to_outlive: Re,
}

// === TyAndTyUnifyError === //

#[derive(Debug, Clone)]
pub struct TyAndTyUnifyError {
    pub origin_lhs: Ty,
    pub origin_rhs: Ty,
    pub culprits: Vec<TyAndTyUnifyCulprit>,
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
    pub lhs: Ty,
    pub rhs: SimpleTySet,
}

// === Obligation Errors === //

pub type ObligationResult<T = ()> = Result<T, ObligationNotReady>;

#[derive(Debug, Clone)]
pub enum ObligationNotReady {
    UnresolvedInfer(InferTyVar),
    ElabStillResolving,
    MultipleApplicableImpls,
    ElaborationHasInferForInherentSelection,
    CoverMissingInfer,
}
