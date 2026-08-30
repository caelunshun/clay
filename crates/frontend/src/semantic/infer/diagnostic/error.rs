use crate::{
    base::{arena::Obj, syntax::Span},
    semantic::{
        infer::{ClauseFuelKillId, ClauseImportEnv, HrtbUniverse, PrettyFmtCx},
        syntax::{
            FnInstance, FnOwnerInherent, FnOwnerTrait, GenericBinder, HrtbBinder, ImplItem,
            InferTyVar, Re, RelationMode, SigGenericList, SigHrtbBinder, SigProjectType,
            SigTraitSpec, SigTy, SimpleTySet, TraitClauseList, TraitItem, TraitParam, TraitSpec,
            Ty, TyOrReList, UniversalReVar, UniversalTyVar,
        },
    },
};
use std::fmt::{self, Write};

// === Formatting === //

pub trait ToDebugTree: Sized {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree;
}

impl<T: ToDebugTree> ToDebugTree for Vec<T> {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        DebugTree::new().with_sublists(self.iter().map(|v| v.to_debug_tree(pretty)))
    }
}

#[derive(Debug, Clone, Default)]
pub struct DebugTree {
    parts: Vec<DebugTreePart>,
}

#[derive(Debug, Clone)]
enum DebugTreePart {
    Prose(String),
    Sublist(DebugTree),
}

impl DebugTree {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.parts.is_empty()
    }

    pub fn push_prose(&mut self, text: impl Into<String>) {
        self.parts.push(DebugTreePart::Prose(text.into()))
    }

    pub fn push_sublist(&mut self, list: impl Into<DebugTree>) {
        let list = list.into();

        if list.is_empty() {
            return;
        }

        self.parts.push(DebugTreePart::Sublist(list));
    }

    pub fn push_sublists(&mut self, lists: impl IntoIterator<Item = DebugTree>) {
        for list in lists {
            self.push_sublist(list);
        }
    }

    pub fn push_flat_sublist(&mut self, list: impl Into<DebugTree>) {
        self.parts.extend(list.into().parts);
    }

    pub fn push_flat_sublists(&mut self, lists: impl IntoIterator<Item = DebugTree>) {
        for list in lists {
            self.push_flat_sublist(list);
        }
    }

    pub fn with_prose(mut self, text: impl Into<String>) -> Self {
        self.push_prose(text);
        self
    }

    pub fn with_sublist(mut self, list: impl Into<DebugTree>) -> Self {
        self.push_sublist(list);
        self
    }

    pub fn with_sublists(mut self, lists: impl IntoIterator<Item = DebugTree>) -> Self {
        self.push_sublists(lists);
        self
    }

    pub fn with_flat_sublist(mut self, list: impl Into<DebugTree>) -> Self {
        self.push_flat_sublist(list);
        self
    }

    pub fn with_flat_sublists(mut self, lists: impl IntoIterator<Item = DebugTree>) -> Self {
        self.push_flat_sublists(lists);
        self
    }

    pub fn with(mut self, f: impl FnOnce(&mut Self)) -> Self {
        f(&mut self);
        self
    }
}

struct IndentedFmt<'a, 'b> {
    f: &'a mut fmt::Formatter<'b>,
    state: IndentedFmtState,
    level: u32,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum IndentedFmtState {
    AtStart,
    Writing,
    NewlineRequested,
    NewlineImplicit,
}

impl<'a, 'b> IndentedFmt<'a, 'b> {
    fn new(f: &'a mut fmt::Formatter<'b>) -> Self {
        Self {
            f,
            state: IndentedFmtState::AtStart,
            level: 0,
        }
    }

    fn level(&self) -> u32 {
        self.level
    }

    fn set_level_now(&mut self, level: u32) -> fmt::Result {
        self.state = IndentedFmtState::NewlineImplicit;
        self.level = level;
        Ok(())
    }

    fn change_level_now(&mut self, by: i32) -> fmt::Result {
        self.set_level_now(self.level().saturating_add_signed(by))
    }

    fn set_level_subsequent(&mut self, level: u32) {
        self.level = level;
    }

    fn change_level_subsequent(&mut self, level: i32) {
        self.set_level_subsequent(self.level().saturating_add_signed(level));
    }
}

impl fmt::Write for IndentedFmt<'_, '_> {
    fn write_str(&mut self, mut s: &str) -> fmt::Result {
        while !s.is_empty() {
            // Obtain single-line payload
            let nl = s.find('\n').unwrap_or(s.len());

            let (payload, remaining_s) = s.split_at(nl);

            if !remaining_s.is_empty() {
                s = &remaining_s[1..];

                // A newline was previously queued up. Honor the request because nothing was
                // written.
                if self.state == IndentedFmtState::NewlineRequested {
                    self.f.write_char('\n')?;
                }

                self.state = IndentedFmtState::NewlineRequested;
            } else {
                s = "";
            }

            // Process state
            if payload.is_empty() {
                continue;
            }

            if matches!(
                self.state,
                IndentedFmtState::NewlineRequested | IndentedFmtState::NewlineImplicit
            ) {
                self.f.write_char('\n')?;
                self.state = IndentedFmtState::AtStart;
            }

            if self.state == IndentedFmtState::AtStart {
                for _ in 0..self.level {
                    self.f.write_str(" ")?;
                }

                self.state = IndentedFmtState::Writing;
            }

            self.f.write_str(payload)?;
        }

        Ok(())
    }
}

impl DebugTree {
    fn format(&self, f: &mut IndentedFmt) -> fmt::Result {
        f.write_str("- ")?;
        f.change_level_subsequent(2);

        for part in &self.parts {
            match part {
                DebugTreePart::Prose(line) => {
                    f.write_str(line)?;
                    f.write_char('\n')?;
                }
                DebugTreePart::Sublist(sublist) => {
                    f.change_level_now(2)?;
                    sublist.format(f)?;
                }
            }
        }

        f.change_level_now(-2)?;

        Ok(())
    }
}

impl fmt::Display for DebugTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format(&mut IndentedFmt::new(f))
    }
}

// === Spanned === //

#[derive(Debug, Clone)]
pub struct SpannedError<T>(pub Span, pub T);

impl<T: ToDebugTree> ToDebugTree for SpannedError<T> {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        DebugTree::new()
            .with_prose(format!("span: {}", self.0))
            .with_flat_sublist(self.1.to_debug_tree(pretty))
    }
}

// === NotCoveredError === //

#[derive(Debug, Clone)]
pub struct NotCoveredError {
    pub missing_mentions: Vec<UniversalTyVar>,
    pub in_trait: Option<TraitSpec>,
    pub in_type: Option<Ty>,
}

impl ToDebugTree for NotCoveredError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        DebugTree::new()
            .with_prose("missing coverings")
            .with(|cx| {
                let Some(in_trait) = self.in_trait else {
                    return;
                };

                cx.push_prose(format!("in {}", pretty.wrap(in_trait)));
            })
            .with(|cx| {
                let Some(in_type) = self.in_type else {
                    return;
                };

                cx.push_prose(format!("in {}", pretty.wrap(in_type)));
            })
            .with_prose("of...")
            .with_sublists(
                self.missing_mentions
                    .iter()
                    .map(|var| DebugTree::new().with_prose(format!("{}", pretty.wrap(var)))),
            )
    }
}

// === TraitImplError === //

#[derive(Debug, Clone)]
pub enum TraitClauseError {
    Outlives(GeneralOutlivesError),
    Trait(UninstantiatedTraitImplError),
}

impl ToDebugTree for TraitClauseError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        match self {
            TraitClauseError::Outlives(error) => error.to_debug_tree(pretty),
            TraitClauseError::Trait(error) => error.to_debug_tree(pretty),
        }
    }
}

#[derive(Debug, Clone)]
pub struct UninstantiatedTraitImplError {
    pub lhs: Ty,
    pub rhs: HrtbBinder,
    pub rhs_instantiated: TraitSpec,
    pub spec_not_met: Option<InstantiatedTraitImplErrorKind>,
    pub rhs_hrtb_error: Option<InstantiateHrtbUniversalError>,
}

impl ToDebugTree for UninstantiatedTraitImplError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        DebugTree::new()
            .with_prose("trait not implemented")
            .with_prose(format!("LHS: {}", pretty.wrap(self.lhs)))
            .with_prose(format!("RHS: {}", pretty.wrap(self.rhs)))
            .with_prose(format!(
                "RHS instance: {}",
                pretty.wrap(self.rhs_instantiated)
            ))
            .with(|cx| {
                let Some(spec_not_met) = &self.spec_not_met else {
                    return;
                };

                cx.push_prose("spec not met:");
                cx.push_sublist(spec_not_met.to_debug_tree(pretty));
            })
            .with(|cx| {
                let Some(rhs_hrtb_error) = &self.rhs_hrtb_error else {
                    return;
                };

                cx.push_prose("RHS HRTB error:");
                cx.push_sublist(rhs_hrtb_error.to_debug_tree(pretty));
            })
    }
}

#[derive(Debug, Clone)]
pub struct InstantiatedTraitImplError {
    pub lhs: Ty,
    pub rhs: TraitSpec,
    pub kind: InstantiatedTraitImplErrorKind,
}

impl ToDebugTree for InstantiatedTraitImplError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        DebugTree::new()
            .with_prose("trait not implemented")
            .with_prose(format!("LHS: {}", pretty.wrap(self.lhs)))
            .with_prose(format!("RHS: {}", pretty.wrap(self.rhs)))
            .with_sublist(self.kind.to_debug_tree(pretty))
    }
}

#[derive(Debug, Clone)]
pub enum InstantiatedTraitImplErrorKind {
    RecursionLimit,
    NoSuitableImpl,
    InherentUnsatisfied(InherentImplUnsatisfiedError),
    ImplBlockUnsatisfied(BlockImplUnsatisfiedError),
    FnDefImplUnsatisfied(FnImplUnsatisfiedError),
}

impl ToDebugTree for InstantiatedTraitImplErrorKind {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        match self {
            InstantiatedTraitImplErrorKind::RecursionLimit => {
                DebugTree::new().with_prose("recursion limit met")
            }
            InstantiatedTraitImplErrorKind::NoSuitableImpl => {
                DebugTree::new().with_prose("no suitable impl met")
            }
            InstantiatedTraitImplErrorKind::InherentUnsatisfied(error) => {
                error.to_debug_tree(pretty)
            }
            InstantiatedTraitImplErrorKind::ImplBlockUnsatisfied(error) => {
                error.to_debug_tree(pretty)
            }
            InstantiatedTraitImplErrorKind::FnDefImplUnsatisfied(error) => {
                error.to_debug_tree(pretty)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct InherentImplUnsatisfiedError {
    pub lhs: HrtbBinder,
    pub rhs: TraitSpec,
    pub lhs_instantiated: TraitSpec,
    pub lhs_instantiate_error: Option<InstantiateHrtbInferError>,
    pub culprits: Vec<InherentImplErrorImplCulprit>,
}

impl ToDebugTree for InherentImplUnsatisfiedError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        DebugTree::new()
            .with_prose("inherent unsatisfied")
            .with_prose(format!("LHS: {}", pretty.wrap(self.lhs)))
            .with_prose(format!("RHS: {}", pretty.wrap(self.rhs)))
            .with_prose(format!(
                "LHS instantiated: {}",
                pretty.wrap(self.lhs_instantiated)
            ))
            .with(|cx| {
                let Some(lhs_instantiate_error) = &self.lhs_instantiate_error else {
                    return;
                };

                cx.push_prose("LHS instantiate error:");
                cx.push_sublist(lhs_instantiate_error.to_debug_tree(pretty));
            })
            .with(|cx| {
                if self.culprits.is_empty() {
                    return;
                }

                cx.push_prose("Culprits:");
                cx.push_sublist(self.culprits.to_debug_tree(pretty));
            })
    }
}

#[derive(Debug, Clone)]
pub enum InherentImplErrorImplCulprit {
    RegionEquate(u32, ReAndReUnifyError),
    TyEquateRegion(u32, TyAndTyRegionUnifyError),
    TyEquate(u32, TyAndTyUnifyError),
    RegionMeets(u32, Vec<GeneralOutlivesError>),
    TyMeets(u32, Vec<TraitClauseError>),
}

impl ToDebugTree for InherentImplErrorImplCulprit {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        match self {
            InherentImplErrorImplCulprit::RegionEquate(idx, error) => DebugTree::new()
                .with_prose(format!("idx: {idx}"))
                .with_sublist(error.to_debug_tree(pretty)),
            InherentImplErrorImplCulprit::TyEquateRegion(idx, error) => DebugTree::new()
                .with_prose(format!("idx: {idx}"))
                .with_sublist(error.to_debug_tree(pretty)),
            InherentImplErrorImplCulprit::TyEquate(idx, error) => DebugTree::new()
                .with_prose(format!("idx: {idx}"))
                .with_sublist(error.to_debug_tree(pretty)),
            InherentImplErrorImplCulprit::RegionMeets(idx, error) => DebugTree::new()
                .with_prose(format!("idx: {idx}"))
                .with_sublist(error.to_debug_tree(pretty)),
            InherentImplErrorImplCulprit::TyMeets(idx, error) => DebugTree::new()
                .with_prose(format!("idx: {idx}"))
                .with_sublist(error.to_debug_tree(pretty)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct BlockImplUnsatisfiedError {
    pub block: Obj<ImplItem>,
    pub culprits: Vec<BlockImplUnsatisfiedErrorCulprit>,
}

impl ToDebugTree for BlockImplUnsatisfiedError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        let s = pretty.session();

        DebugTree::new()
            .with_prose("block impl unsatisfied")
            .with_prose(format!("block: {}", self.block.r(s).target.r(s).span))
            .with_sublist(self.culprits.to_debug_tree(pretty))
    }
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

impl ToDebugTree for BlockImplUnsatisfiedErrorCulprit {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        match self {
            BlockImplUnsatisfiedErrorCulprit::BlockUnsatisfied(error) => {
                error.to_debug_tree(pretty)
            }
            BlockImplUnsatisfiedErrorCulprit::SelfTyUnify(error) => error.to_debug_tree(pretty),
            BlockImplUnsatisfiedErrorCulprit::GenericReUnify(idx, error) => DebugTree::new()
                .with_prose(format!("idx: {idx}"))
                .with_sublist(error.to_debug_tree(pretty)),
            BlockImplUnsatisfiedErrorCulprit::GenericTyUnify(idx, error) => DebugTree::new()
                .with_prose(format!("idx: {idx}"))
                .with_sublist(error.to_debug_tree(pretty)),
            BlockImplUnsatisfiedErrorCulprit::AssocTyUnify(idx, error) => DebugTree::new()
                .with_prose(format!("idx: {idx}"))
                .with_sublist(error.to_debug_tree(pretty)),
            BlockImplUnsatisfiedErrorCulprit::AssocSpecMet(idx, error) => DebugTree::new()
                .with_prose(format!("idx: {idx}"))
                .with_sublist(error.to_debug_tree(pretty)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FnImplUnsatisfiedError {
    pub resolve_fn: Option<Box<FnInstanceResolutionError>>,
    pub unify_args: Option<Box<TyAndTyRegionUnifyError>>,
    pub unify_output: Option<Box<TyAndTyRegionUnifyError>>,
}

impl ToDebugTree for FnImplUnsatisfiedError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        DebugTree::new()
            .with_prose("fn impl unsatisfied")
            .with(|cx| {
                let Some(resolve_fn) = &self.resolve_fn else {
                    return;
                };

                cx.push_prose("resolve fn:");
                cx.push_sublist(resolve_fn.to_debug_tree(pretty));
            })
            .with(|cx| {
                let Some(unify_args) = &self.unify_args else {
                    return;
                };

                cx.push_prose("unify args:");
                cx.push_sublist(unify_args.to_debug_tree(pretty));
            })
            .with(|cx| {
                let Some(unify_output) = &self.unify_output else {
                    return;
                };

                cx.push_prose("unify output:");
                cx.push_sublist(unify_output.to_debug_tree(pretty));
            })
    }
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

impl ToDebugTree for GeneralOutlivesError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        match self {
            GeneralOutlivesError::TyAndTy(error) => error.to_debug_tree(pretty),
            GeneralOutlivesError::TyAndRe(error) => error.to_debug_tree(pretty),
            GeneralOutlivesError::ReAndRe(error) => error.to_debug_tree(pretty),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TyOutlivesTyError {
    pub lhs: Ty,
    pub rhs: Ty,
    pub joiner: Re,
    pub errors: Vec<ReAndReUnifyError>,
}

impl ToDebugTree for TyOutlivesTyError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        DebugTree::new()
            .with_prose("ty outlives ty")
            .with_prose(format!("LHS: {}", pretty.wrap(self.lhs)))
            .with_prose(format!("RHS: {}", pretty.wrap(self.rhs)))
            .with_prose(format!("Joiner: {}", pretty.wrap(self.joiner)))
            .with_prose(format!("Errors:"))
            .with_sublist(self.errors.to_debug_tree(pretty))
    }
}

#[derive(Debug, Clone)]
pub struct TyOutlivesReError {
    pub lhs: Ty,
    pub rhs: Re,
    pub errors: Vec<ReAndReUnifyError>,
}

impl ToDebugTree for TyOutlivesReError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        DebugTree::new()
            .with_prose("ty outlives region")
            .with_prose(format!("LHS: {}", pretty.wrap(self.lhs)))
            .with_prose(format!("RHS: {}", pretty.wrap(self.rhs)))
            .with_prose(format!("Errors:"))
            .with_sublist(self.errors.to_debug_tree(pretty))
    }
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

impl ToDebugTree for ImportError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        let s = pretty.session();

        match self {
            ImportError::Projection { ty, error } => DebugTree::new()
                .with_prose("projection failed")
                .with_prose(format!("span: {}", ty.spec.span))
                .with_sublist(error.to_debug_tree(pretty)),
            ImportError::TraitFnOwner { owner: _, error } => DebugTree::new()
                .with_prose("trait fn owner not WF")
                .with_sublist(error.to_debug_tree(pretty)),
            ImportError::InherentBlockEnv { owner: _, error } => DebugTree::new()
                .with_prose("inherent block env not WF")
                .with_sublist(error.to_debug_tree(pretty)),
            ImportError::NoShadowImpl { error } => DebugTree::new()
                .with_prose("no shadow impl")
                .with_sublist(error.to_debug_tree(pretty)),
            ImportError::BadRefPointee { ty, error } => DebugTree::new()
                .with_prose("bad ref pointee")
                .with_prose(format!("span: {}", ty.r(s).span))
                .with_sublist(error.to_debug_tree(pretty)),
            ImportError::BadGenerics {
                binder: _,
                env: _,
                args,
                error,
            } => DebugTree::new()
                .with_prose("bad generics")
                .with_prose(format!("span: {}", {
                    if let [unique] = args.elems.r(s) {
                        unique.span(s)
                    } else if let [first, .., last] = args.elems.r(s) {
                        first.span(s).to(last.span(s))
                    } else {
                        Span::DUMMY
                    }
                }))
                .with_sublist(error.to_debug_tree(pretty)),
            ImportError::BadTraitSpec { spec, error } => DebugTree::new()
                .with_prose("bad trait spec")
                .with_prose(format!("span: {}", spec.span))
                .with_sublist(error.to_debug_tree(pretty)),
            ImportError::HrtbNotCovered { binder, error } => DebugTree::new()
                .with_prose("HRTB not covered")
                .with_prose(format!("span: {}", binder.inner.span))
                .with_sublist(error.to_debug_tree(pretty)),
        }
    }
}

// === HRTB errors === //

#[derive(Debug, Clone)]
pub struct InstantiateHrtbUniversalError {
    pub value: HrtbBinder,
    pub normalize_errors: Vec<TraitSpecResolutionError>,
}

impl ToDebugTree for InstantiateHrtbUniversalError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        DebugTree::new()
            .with_prose("instantiate HRTB universal")
            .with_prose(format!("binder: {}", pretty.wrap(self.value)))
            .with_sublists(
                self.normalize_errors
                    .iter()
                    .map(|v| v.to_debug_tree(pretty)),
            )
    }
}

#[derive(Debug, Clone)]
pub struct InstantiateHrtbInferError {
    pub value: HrtbBinder,
    pub param_not_valid: Vec<HrtbInferParamNotValid>,
    pub normalize_errors: Vec<TraitSpecResolutionError>,
}

impl ToDebugTree for InstantiateHrtbInferError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct HrtbInferParamNotValid {
    pub idx: u32,
    pub kind: HrtbInferParamNotValidKind,
}

impl ToDebugTree for HrtbInferParamNotValid {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub enum HrtbInferParamNotValidKind {
    RegionNotMet(Vec<GeneralOutlivesError>),
    TyNotMet(Vec<TraitClauseError>),
}

impl ToDebugTree for HrtbInferParamNotValidKind {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

// === Infer instantiation errors === //

#[derive(Debug, Clone)]
pub struct BinderParamWfBinderError {
    pub binder: Obj<GenericBinder>,
    pub params: TyOrReList,
    pub errors: Vec<BinderParamWfParamError>,
}

impl ToDebugTree for BinderParamWfBinderError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct BinderParamWfParamError {
    pub idx: u32,
    pub kind: BinderParamWfParamErrorKind,
}

impl ToDebugTree for BinderParamWfParamError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub enum BinderParamWfParamErrorKind {
    ClauseCannotImport(Vec<ImportError>),
    OutlivesNotMet(GeneralOutlivesError),
    ImplNotMet(UninstantiatedTraitImplError),
}

impl ToDebugTree for BinderParamWfParamErrorKind {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct TraitSpecResolutionError {
    pub self_ty: Ty,
    pub spec: TraitSpec,
    pub culprits: Vec<TraitSpecResolutionErrorCulprit>,
}

impl ToDebugTree for TraitSpecResolutionError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub enum TraitSpecResolutionErrorCulprit {
    AssocParaNotMet {
        idx: u32,
        error: Vec<TraitClauseError>,
    },
    ImplRejected(InstantiatedTraitImplError),
}

impl ToDebugTree for TraitSpecResolutionErrorCulprit {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct InherentImplBlockSatisfyError {
    pub block_clauses: Option<Box<ImplBlockSatisfyError>>,
    pub self_ty_unify: Option<Box<TyAndTyUnifyError>>,
}

impl ToDebugTree for InherentImplBlockSatisfyError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct ImplBlockSatisfyError {
    pub block: Obj<ImplItem>,
    pub culprits: Vec<ImplBlockSatisfyErrorCulprit>,
}

impl ToDebugTree for ImplBlockSatisfyError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub enum ImplBlockSatisfyErrorCulprit {
    SelfTyImportError(Vec<ImportError>),
    TargetTraitImportError(Vec<ImportError>),
    GenericsUnsatisfied(BinderParamWfBinderError),
}

impl ToDebugTree for ImplBlockSatisfyErrorCulprit {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct FnInstanceResolutionError {
    pub instance: FnInstance,
    pub kind: FnInstanceResolutionErrorKind,
}

impl ToDebugTree for FnInstanceResolutionError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
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

impl ToDebugTree for FnInstanceResolutionErrorKind {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
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

impl ToDebugTree for TypeRelativeFnDefToOwnerError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

// === Unification Promises === //

#[derive(Debug, Clone)]
pub struct TyAndTyUnifyError {
    pub lhs: Ty,
    pub rhs: Ty,
    pub mode: RelationMode,
    pub kind: TyAndTyUnifyErrorKind,
}

impl ToDebugTree for TyAndTyUnifyError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub enum TyAndTyUnifyErrorKind {
    Structural(Vec<TyAndTyUnifyCulprit>),
    Region(Vec<ReAndReUnifyError>),
}

impl ToDebugTree for TyAndTyUnifyErrorKind {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct TyAndTyRegionUnifyError {
    pub lhs: Ty,
    pub rhs: Ty,
    pub mode: RelationMode,
    pub regions: Vec<ReAndReUnifyError>,
}

impl ToDebugTree for TyAndTyRegionUnifyError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct ReAndReUnifyError {
    pub lhs: Re,
    pub rhs: Re,
    pub mode: RelationMode,
    pub causes: Vec<ReAndReUnifyErrorCause>,
}

impl ToDebugTree for ReAndReUnifyError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct ReAndReUnifyErrorCause {
    pub requires_var: UniversalReVar,
    pub to_outlive: Re,
}

impl ToDebugTree for ReAndReUnifyErrorCause {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

// === Unification structural errors === //

#[derive(Debug, Clone)]
pub struct TyAndTyStructuralUnifyError {
    pub origin_lhs: Ty,
    pub origin_rhs: Ty,
    pub culprits: Vec<TyAndTyUnifyCulprit>,
}

impl ToDebugTree for TyAndTyStructuralUnifyError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
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

impl ToDebugTree for TyAndTyUnifyCulprit {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct InferTyOccursError {
    pub var: InferTyVar,
    pub occurs_in: Ty,
}

impl ToDebugTree for InferTyOccursError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct InferTyLeaksUniversalError {
    pub var: InferTyVar,
    pub max_universe: HrtbUniverse,
    pub leaks_universal: UniversalTyVar,
}

impl ToDebugTree for InferTyLeaksUniversalError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct InferTyLeaksHrtbVarError {
    pub var: InferTyVar,
}

impl ToDebugTree for InferTyLeaksHrtbVarError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct TyAndSimpleTySetUnifyError {
    pub lhs: Ty,
    pub rhs: SimpleTySet,
}

impl ToDebugTree for TyAndSimpleTySetUnifyError {
    fn to_debug_tree(&self, pretty: &PrettyFmtCx<'_, '_>) -> DebugTree {
        todo!()
    }
}

// === Obligation errors === //

pub type ObligationResult<T = ObligationTermination> = Result<T, ObligationNotReady>;

#[derive(Debug)]
pub enum ObligationTermination {
    Regular,
    FuelExhausted(ClauseFuelKillId),
}

#[derive(Debug, Clone)]
pub enum ObligationNotReady {
    UnresolvedInfer(InferTyVar),
    ElabStillResolving,
    MultipleApplicableImpls,
    ElaborationHasInferForInherentSelection,
    CoverMissingInfer,
}
