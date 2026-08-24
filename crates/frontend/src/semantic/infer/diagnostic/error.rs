use crate::{
    base::{arena::Obj, syntax::Span},
    semantic::{
        infer::HrtbUniverse,
        syntax::{
            HrtbBinder, ImplItem, InferTyVar, Re, RelationMode, SigTy, SigTyList, SigTyOrReList,
            SimpleTySet, TraitClauseList, TraitParam, TraitSpec, Ty, UniversalReVar,
            UniversalTyVar,
        },
    },
};

// === NotCoveredError === //

#[derive(Debug, Clone)]
pub struct NotCoveredError {
    pub missing_mentions: Vec<UniversalTyVar>,
    pub in_trait: Option<TraitSpec>,
    pub in_type: Option<Ty>,
}

// === TraitImplError === //

#[derive(Debug, Clone)]
pub enum TraitClauseError {
    Outlives(GeneralOutlivesError),
    Trait(UninstantiatedTraitImplError),
}

#[derive(Debug, Clone)]
pub struct UninstantiatedTraitImplError {
    pub lhs: Ty,
    pub rhs: HrtbBinder,
    pub rhs_instantiated: TraitSpec,
    pub spec_not_met: Option<InstantiatedTraitImplErrorKind>,
}

#[derive(Debug, Clone)]
pub struct InstantiatedTraitImplError {
    pub lhs: Ty,
    pub rhs: TraitSpec,
    pub kind: InstantiatedTraitImplErrorKind,
}

#[derive(Debug, Clone)]
pub enum InstantiatedTraitImplErrorKind {
    RecursionLimit,
    NoSuitableImpl,
    InherentUnsatisfied(InherentImplUnsatisfiedError),
    ImplBlockUnsatisfied(BlockImplUnsatisfiedError),
}

#[derive(Debug, Clone)]
pub struct InherentImplUnsatisfiedError {
    pub lhs: HrtbBinder,
    pub rhs: TraitSpec,
    pub culprits: Vec<InherentImplErrorImplCulprit>,
}

#[derive(Debug, Clone)]
pub enum InherentImplErrorImplCulprit {
    RegionEquate(u32, ReAndReUnifyError),
    TyEquateRegion(u32, TyAndTyRegionUnifyError),
    TyEquate(u32, TyAndTyUnifyError),
}

#[derive(Debug, Clone)]
pub struct BlockImplUnsatisfiedError {
    pub block: Obj<ImplItem>,
    pub culprits: Vec<BlockImplUnsatisfiedErrorCulprit>,
}

#[derive(Debug, Clone)]
pub enum BlockImplUnsatisfiedErrorCulprit {
    AssocMismatch,
    AssocNotSatisfied,
}

// === Outlives Error === //

#[derive(Debug, Clone)]
pub enum GeneralOutlivesError {
    TyAndTy(TyOutlivesTyError),
    TyAndRe(TyOutlivesReError),
    ReAndRe(ReAndReUnifyError),
}

impl From<TyOutlivesTyError> for GeneralOutlivesError {
    fn from(error: TyOutlivesTyError) -> Self {
        GeneralOutlivesError::TyAndTy(error)
    }
}

impl From<TyOutlivesReError> for GeneralOutlivesError {
    fn from(error: TyOutlivesReError) -> Self {
        GeneralOutlivesError::TyAndRe(error)
    }
}

impl From<ReAndReUnifyError> for GeneralOutlivesError {
    fn from(error: ReAndReUnifyError) -> Self {
        GeneralOutlivesError::ReAndRe(error)
    }
}

#[derive(Debug, Clone)]
pub struct TyOutlivesTyError {
    pub lhs: Ty,
    pub rhs: Ty,
    pub joiner: Re,
    pub errors: Vec<ReAndReUnifyError>,
}

#[derive(Debug, Clone)]
pub struct TyOutlivesReError {
    pub lhs: Ty,
    pub rhs: Re,
    pub errors: Vec<ReAndReUnifyError>,
}

// === Unification Promises === //

#[derive(Debug, Clone)]
pub struct TyAndTyUnifyError {
    pub lhs: Ty,
    pub rhs: Ty,
    pub mode: RelationMode,
    pub kind: TyAndTyUnifyErrorKind,
}

#[derive(Debug, Clone)]
pub enum TyAndTyUnifyErrorKind {
    Structural(Vec<TyAndTyUnifyCulprit>),
    Region(Vec<ReAndReUnifyError>),
}

#[derive(Debug, Clone)]
pub struct TyAndTyRegionUnifyError {
    pub lhs: Ty,
    pub rhs: Ty,
    pub mode: RelationMode,
    pub regions: Vec<ReAndReUnifyError>,
}

#[derive(Debug, Clone)]
pub struct ReAndReUnifyError {
    pub lhs: Re,
    pub rhs: Re,
    pub mode: RelationMode,
    pub causes: Vec<ReAndReUnifyErrorCause>,
}

#[derive(Debug, Clone)]
pub struct ReAndReUnifyErrorCause {
    pub requires_var: UniversalReVar,
    pub to_outlive: Re,
}

// === Unification structural errors === //

#[derive(Debug, Clone)]
pub struct TyAndTyStructuralUnifyError {
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

// === Import errors === //

#[derive(Debug, Clone)]
pub struct ImportTyOrReListError {
    pub input: SigTyOrReList,
    pub errors: Vec<Option<ImportTyOrReError>>,
}

#[derive(Debug, Clone)]
pub struct ImportTyListError {
    pub input: SigTyList,
    pub errors: Vec<Option<ImportTyError>>,
}

#[derive(Debug, Clone)]
pub enum ImportTyOrReError {
    Ty(ImportTyError),
    Re(ImportReError),
}

#[derive(Debug, Clone)]
pub struct ImportTyError {
    pub input: SigTy,
    pub culprits: Vec<ImportTyErrorCulprit>,
}

#[derive(Debug, Clone)]
pub enum ImportTyErrorCulprit {
    InAliasBody(Box<ImportTyError>),
    InRefLt(Box<ImportReError>),
    InRefPointee(Box<ImportTyError>),
}

#[derive(Debug, Clone)]
pub struct ImportReError {}

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
