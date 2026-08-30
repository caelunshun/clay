use crate::{
    base::arena::Obj,
    semantic::{
        infer::{ClauseImportEnv, HrtbUniverse},
        syntax::{
            FnInstance, FnOwnerInherent, FnOwnerTrait, GenericBinder, HrtbBinder, ImplItem,
            InferTyVar, Re, RelationMode, SigGenericList, SigHrtbBinder, SigProjectType,
            SigTraitSpec, SigTy, SimpleTySet, TraitClauseList, TraitItem, TraitParam, TraitSpec,
            Ty, TyOrReList, UniversalReVar, UniversalTyVar,
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
    pub rhs_hrtb_error: Option<InstantiateHrtbUniversalError>,
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
    FnDefImplUnsatisfied(FnImplUnsatisfiedError),
}

#[derive(Debug, Clone)]
pub struct InherentImplUnsatisfiedError {
    pub lhs: HrtbBinder,
    pub rhs: TraitSpec,
    pub lhs_instantiated: TraitSpec,
    pub lhs_instantiate_error: Option<InstantiateHrtbInferError>,
    pub culprits: Vec<InherentImplErrorImplCulprit>,
}

#[derive(Debug, Clone)]
pub enum InherentImplErrorImplCulprit {
    RegionEquate(u32, ReAndReUnifyError),
    TyEquateRegion(u32, TyAndTyRegionUnifyError),
    TyEquate(u32, TyAndTyUnifyError),
    RegionMeets(u32, Vec<GeneralOutlivesError>),
    TyMeets(u32, Vec<TraitClauseError>),
}

#[derive(Debug, Clone)]
pub struct BlockImplUnsatisfiedError {
    pub block: Obj<ImplItem>,
    pub culprits: Vec<BlockImplUnsatisfiedErrorCulprit>,
}

#[derive(Debug, Clone)]
pub enum BlockImplUnsatisfiedErrorCulprit {
    BlockUnsatisfied(Box<ImplBlockSatisfyError>),
    SelfTyUnify(Box<TyAndTyRegionUnifyError>),
    GenericReUnify(u32, Box<ReAndReUnifyError>),
    GenericTyUnify(u32, Box<TyAndTyRegionUnifyError>),
    AssocTyUnify(u32, Box<TyAndTyUnifyError>),
    AssocSpecMet(u32, Box<Vec<TraitClauseError>>),
}

#[derive(Debug, Clone)]
pub struct FnImplUnsatisfiedError {
    pub resolve_fn: Option<Box<FnInstanceResolutionError>>,
    pub unify_args: Option<Box<TyAndTyRegionUnifyError>>,
    pub unify_output: Option<Box<TyAndTyRegionUnifyError>>,
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

// === Import errors === //

#[derive(Debug, Clone)]
pub enum ImportError {
    Projection {
        ty: SigProjectType,
        error: Box<TraitSpecResolutionError>,
    },
    TraitFnOwner {
        owner: FnOwnerTrait,
        error: Box<TraitSpecResolutionError>,
    },
    InherentBlockEnv {
        owner: FnOwnerInherent,
        error: Box<InherentImplBlockSatisfyError>,
    },
    NoShadowImpl {
        error: Box<TraitSpecResolutionError>,
    },
    BadRefPointee {
        ty: SigTy,
        error: Box<TyOutlivesReError>,
    },
    BadGenerics {
        binder: Obj<GenericBinder>,
        env: ClauseImportEnv,
        args: SigGenericList,
        error: Box<BinderParamWfBinderError>,
    },
    BadTraitSpec {
        spec: SigTraitSpec,
        error: Box<BinderParamWfBinderError>,
    },
    HrtbNotCovered {
        binder: SigHrtbBinder,
        error: Box<NotCoveredError>,
    },
}

// === HRTB errors === //

#[derive(Debug, Clone)]
pub struct InstantiateHrtbUniversalError {
    pub value: HrtbBinder,
    pub normalize_errors: Vec<TraitSpecResolutionError>,
}

#[derive(Debug, Clone)]
pub struct InstantiateHrtbInferError {
    pub value: HrtbBinder,
    pub param_not_valid: Vec<HrtbInferParamNotValid>,
    pub normalize_errors: Vec<TraitSpecResolutionError>,
}

#[derive(Debug, Clone)]
pub struct HrtbInferParamNotValid {
    pub idx: u32,
    pub kind: HrtbInferParamNotValidKind,
}

#[derive(Debug, Clone)]
pub enum HrtbInferParamNotValidKind {
    RegionNotMet(Vec<GeneralOutlivesError>),
    TyNotMet(Vec<TraitClauseError>),
}

// === Infer instantiation errors === //

#[derive(Debug, Clone)]
pub struct BinderParamWfBinderError {
    pub binder: Obj<GenericBinder>,
    pub params: TyOrReList,
    pub errors: Vec<BinderParamWfParamError>,
}

#[derive(Debug, Clone)]
pub struct BinderParamWfParamError {
    pub idx: u32,
    pub kind: BinderParamWfParamErrorKind,
}

#[derive(Debug, Clone)]
pub enum BinderParamWfParamErrorKind {
    ClauseCannotImport(Vec<ImportError>),
    OutlivesNotMet(GeneralOutlivesError),
    ImplNotMet(UninstantiatedTraitImplError),
}

#[derive(Debug, Clone)]
pub struct TraitSpecResolutionError {
    pub self_ty: Ty,
    pub spec: TraitSpec,
    pub culprits: Vec<TraitSpecResolutionErrorCulprit>,
}

#[derive(Debug, Clone)]
pub enum TraitSpecResolutionErrorCulprit {
    AssocParaNotMet {
        idx: u32,
        error: Vec<TraitClauseError>,
    },
    ImplRejected(InstantiatedTraitImplError),
}

#[derive(Debug, Clone)]
pub struct InherentImplBlockSatisfyError {
    pub block_clauses: Option<Box<ImplBlockSatisfyError>>,
    pub self_ty_unify: Option<Box<TyAndTyUnifyError>>,
}

#[derive(Debug, Clone)]
pub struct ImplBlockSatisfyError {
    pub block: Obj<ImplItem>,
    pub culprits: Vec<ImplBlockSatisfyErrorCulprit>,
}

#[derive(Debug, Clone)]
pub enum ImplBlockSatisfyErrorCulprit {
    SelfTyImportError(Vec<ImportError>),
    TargetTraitImportError(Vec<ImportError>),
    GenericsUnsatisfied(BinderParamWfBinderError),
}

#[derive(Debug, Clone)]
pub struct FnInstanceResolutionError {
    pub instance: FnInstance,
    pub kind: FnInstanceResolutionErrorKind,
}

#[derive(Debug, Clone)]
pub enum FnInstanceResolutionErrorKind {
    Item {
        early_args_err: Option<Box<BinderParamWfBinderError>>,
        sig_import_err: Option<Vec<ImportError>>,
    },
    Trait {
        resolve_instance_err: Option<Box<TraitSpecResolutionError>>,
        early_args_err: Option<Box<BinderParamWfBinderError>>,
        sig_import_err: Option<Vec<ImportError>>,
    },
    Inherent {
        resolve_block_err: Option<Box<InherentImplBlockSatisfyError>>,
        early_args_err: Option<Box<BinderParamWfBinderError>>,
        sig_import_err: Option<Vec<ImportError>>,
    },
    AdtCtor {
        early_args_err: Option<Box<BinderParamWfBinderError>>,
        sig_import_err: Option<Vec<ImportError>>,
    },
}

#[derive(Debug, Clone)]
pub enum TypeRelativeFnDefToOwnerError {
    Trait {
        item: Obj<TraitItem>,
        method_idx: u32,
        self_ty: Ty,
        error: Box<InstantiatedTraitImplError>,
    },
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

// === Obligation errors === //

pub type ObligationResult<T = ()> = Result<T, ObligationNotReady>;

#[derive(Debug, Clone)]
pub enum ObligationNotReady {
    UnresolvedInfer(InferTyVar),
    ElabStillResolving,
    MultipleApplicableImpls,
    ElaborationHasInferForInherentSelection,
    CoverMissingInfer,
}
