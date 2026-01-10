use crate::{
    base::{ErrorGuaranteed, HardDiag, Session, arena::HasInterner},
    semantic::{
        analysis::{
            TyCtxt, TyFolder, TyFolderExt, TyFolderInfallibleExt, TyVisitor, TyVisitorExt,
            infer::unify::{regions::ReUnifyTracker, types::TyUnifyTracker},
        },
        syntax::{
            HrtbBinderKind, InferTyVar, Mutability, Re, ReVariance, RelationDirection,
            RelationMode, SpannedTy, SpannedTyView, TraitClause, TraitClauseList, TraitParam, Ty,
            TyKind, TyOrRe, UniversalReVar, UniversalReVarSourceInfo,
        },
    },
    utils::hash::FxHashSet,
};
use index_vec::define_index_type;
use std::{convert::Infallible, ops::ControlFlow};

// === Errors === //

#[derive(Debug, Clone)]
pub struct TyAndTyUnifyError {
    pub origin_lhs: Ty,
    pub origin_rhs: Ty,
    pub culprits: Vec<TyAndTyUnifyCulprit>,
}

impl TyAndTyUnifyError {
    // TODO
    pub fn to_diag(self) -> HardDiag {
        HardDiag::anon_err(format_args!(
            "could not unify types {:?} and {:?}",
            self.origin_lhs, self.origin_rhs,
        ))
    }
}

#[derive(Debug, Clone)]
pub enum TyAndTyUnifyCulprit {
    Types(Ty, Ty),
    ClauseLists(TraitClauseList, TraitClauseList),
    Params(TraitParam, TraitParam),
    RecursiveType(InferTyOccursError),
}

#[derive(Debug, Clone)]
pub struct InferTyOccursError {
    pub var: InferTyVar,
    pub occurs_in: Ty,
}

// === UnifyCx === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum UnifyCxMode {
    RegionBlind,
    RegionAware,
}

/// A type inference context for solving type obligations of the form...
///
/// - `Region: Region`
/// - `Type = Type`
///
/// No operations performed by this context depend on the order in which prior operations have been
/// performed and, as such, all operations can be performed and checked for correctness immediately.
/// This property is not true for more complex `Ty: Clause` and `Ty: 're` obligations. To perform
/// those obligations, you'll need an [`ClauseCx`](super::ClauseCx), which uses the deferred-solving
/// functionality of a [`ObligationCx`](super::ObligationCx) internally to solve these obligations.
#[derive(Debug, Clone)]
pub struct UnifyCx<'tcx> {
    tcx: &'tcx TyCtxt,
    types: TyUnifyTracker,
    regions: Option<ReUnifyTracker>,
}

define_index_type! {
    pub struct ObservedTyInferVar = u32;
}

#[derive(Debug, Copy, Clone)]
pub struct FloatingInferVar<'a> {
    pub root: InferTyVar,
    pub observed_equivalent: &'a [ObservedTyInferVar],
}

impl<'tcx> UnifyCx<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, mode: UnifyCxMode) -> Self {
        Self {
            tcx,
            types: TyUnifyTracker::default(),
            regions: match mode {
                UnifyCxMode::RegionBlind => None,
                UnifyCxMode::RegionAware => Some(ReUnifyTracker::default()),
            },
        }
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    pub fn session(&self) -> &'tcx Session {
        &self.tcx.session
    }

    pub fn mode(&self) -> UnifyCxMode {
        if self.regions.is_some() {
            UnifyCxMode::RegionAware
        } else {
            UnifyCxMode::RegionBlind
        }
    }

    pub fn verify(&mut self) {
        if let Some(re) = &mut self.regions {
            _ = re.verify();
        }
    }

    pub fn substitutor(&self, mode: UnboundVarHandlingMode) -> InferTySubstitutor<'_, 'tcx> {
        InferTySubstitutor { ucx: self, mode }
    }

    pub fn start_tracing(&mut self) {
        self.types.start_tracing();
    }

    pub fn finish_tracing(&mut self) -> FxHashSet<InferTyVar> {
        self.types.finish_tracing()
    }

    pub fn mention_var_for_tracing(&self, var: InferTyVar) {
        self.types.mention_var_for_tracing(var);
    }

    pub fn fresh_ty_infer_var(&mut self) -> InferTyVar {
        self.types.fresh()
    }

    pub fn fresh_ty_infer(&mut self) -> Ty {
        self.tcx()
            .intern(TyKind::InferVar(self.fresh_ty_infer_var()))
    }

    pub fn observe_ty_infer_var(&mut self, var: InferTyVar) -> ObservedTyInferVar {
        self.types.observe(var)
    }

    pub fn observed_infer_reveal_order(&self) -> &[ObservedTyInferVar] {
        self.types.observed_reveal_order()
    }

    pub fn lookup_ty_infer_var(&self, var: InferTyVar) -> Result<Ty, FloatingInferVar<'_>> {
        self.types.lookup(var)
    }

    pub fn peel_ty_infer_var(&self, ty: Ty) -> Ty {
        let s = self.session();

        match *ty.r(s) {
            TyKind::InferVar(var) => {
                if let Ok(var) = self.types.lookup(var) {
                    var
                } else {
                    ty
                }
            }
            _ => ty,
        }
    }

    pub fn fresh_re_universal(&mut self, src_info: UniversalReVarSourceInfo) -> Re {
        if let Some(regions) = &mut self.regions {
            Re::UniversalVar(regions.fresh_universal(src_info))
        } else {
            Re::Erased
        }
    }

    pub fn lookup_universal_re_src_info(&self, var: UniversalReVar) -> UniversalReVarSourceInfo {
        self.regions
            .as_ref()
            .expect("cannot `lookup_universal_re_src_info` in a region-blind context")
            .lookup_universal_src_info(var)
    }

    pub fn permit_re_universal_outlives(
        &mut self,
        universal: Re,
        other: Re,
        dir: RelationDirection,
    ) {
        let Some(regions) = &mut self.regions else {
            debug_assert!(matches!(universal, Re::Erased));
            debug_assert!(matches!(other, Re::Erased));

            return;
        };

        let Re::UniversalVar(universal) = universal else {
            unreachable!()
        };

        regions.permit(universal, other, dir);
    }

    pub fn fresh_re_infer(&mut self) -> Re {
        if let Some(regions) = &mut self.regions {
            Re::InferVar(regions.fresh_infer())
        } else {
            Re::Erased
        }
    }

    pub fn unify_re_and_re(&mut self, lhs: Re, rhs: Re, mode: RelationMode) {
        let Some(regions) = &mut self.regions else {
            debug_assert!(matches!(lhs, Re::Erased));
            debug_assert!(matches!(rhs, Re::Erased));

            return;
        };

        for (lhs, rhs) in mode.enumerate(lhs, rhs) {
            regions.constrain(lhs, rhs);
        }
    }

    /// Unifies two types such that they match. The `mode` specifies how the regions inside the
    /// types should be unified. For example, if it is `RelationMode::LhsOntoRhs`, relating
    /// `&'0 u32` and `&'1 u32` will result in the region relation `'0: '1`.
    pub fn unify_ty_and_ty(
        &mut self,
        lhs: Ty,
        rhs: Ty,
        mode: RelationMode,
    ) -> Result<(), Box<TyAndTyUnifyError>> {
        let mut fork = self.clone();
        let mut culprits = Vec::new();

        fork.unify_ty_and_ty_inner(lhs, rhs, &mut culprits, mode);

        if !culprits.is_empty() {
            return Err(Box::new(TyAndTyUnifyError {
                origin_lhs: lhs,
                origin_rhs: rhs,
                culprits,
            }));
        }

        *self = fork;

        Ok(())
    }

    fn unify_ty_and_ty_inner(
        &mut self,
        lhs: Ty,
        rhs: Ty,
        culprits: &mut Vec<TyAndTyUnifyCulprit>,
        mode: RelationMode,
    ) {
        let s = self.session();

        if lhs == rhs {
            // The types are compatible!
            return;
        }

        match (*lhs.r(s), *rhs.r(s)) {
            (TyKind::SigThis, _)
            | (_, TyKind::SigThis)
            | (TyKind::SigInfer, _)
            | (_, TyKind::SigInfer)
            | (TyKind::SigGeneric(_), _)
            | (_, TyKind::SigGeneric(_))
            | (TyKind::SigProject(_), _)
            | (_, TyKind::SigProject(_)) => {
                unreachable!()
            }
            (
                TyKind::Reference(lhs_re, lhs_muta, lhs_pointee),
                TyKind::Reference(rhs_re, rhs_muta, rhs_pointee),
            ) if lhs_muta == rhs_muta => {
                self.unify_re_and_re(lhs_re, rhs_re, mode);

                let variance = match lhs_muta {
                    Mutability::Mut => ReVariance::Invariant,
                    Mutability::Not => ReVariance::Covariant,
                };

                self.unify_ty_and_ty_inner(
                    lhs_pointee,
                    rhs_pointee,
                    culprits,
                    mode.with_variance(variance),
                );
            }
            (TyKind::Adt(lhs), TyKind::Adt(rhs)) if lhs.def == rhs.def => {
                // TODO: variance

                for (&lhs, &rhs) in lhs.params.r(s).iter().zip(rhs.params.r(s)) {
                    match (lhs, rhs) {
                        (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                            self.unify_re_and_re(lhs, rhs, mode);
                        }
                        (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                            self.unify_ty_and_ty_inner(lhs, rhs, culprits, mode);
                        }
                        _ => unreachable!(),
                    }
                }
            }
            (TyKind::Trait(lhs), TyKind::Trait(rhs)) => {
                self.unify_dyn_trait_clauses_inner(lhs, rhs, culprits, mode);
            }
            (TyKind::FnDef(lhs, Some(lhs_generics)), TyKind::FnDef(rhs, Some(rhs_generics)))
                if lhs == rhs =>
            {
                for (&lhs, &rhs) in lhs_generics.r(s).iter().zip(rhs_generics.r(s)) {
                    // TODO: The variance rules for these are a bit more complicated.
                    let mode = RelationMode::Equate;

                    match (lhs, rhs) {
                        (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                            self.unify_re_and_re(lhs, rhs, mode);
                        }
                        (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                            self.unify_ty_and_ty_inner(lhs, rhs, culprits, mode);
                        }
                        _ => unreachable!(),
                    }
                }
            }
            (TyKind::FnDef(lhs, None), TyKind::FnDef(rhs, None)) if lhs == rhs => {
                // (accepted)
            }
            (TyKind::Tuple(lhs), TyKind::Tuple(rhs)) if lhs.r(s).len() == rhs.r(s).len() => {
                for (&lhs, &rhs) in lhs.r(s).iter().zip(rhs.r(s)) {
                    self.unify_ty_and_ty_inner(lhs, rhs, culprits, mode);
                }
            }
            (TyKind::InferVar(lhs_var), TyKind::InferVar(rhs_var)) => {
                match (self.types.lookup(lhs_var), self.types.lookup(rhs_var)) {
                    (Ok(lhs_ty), Ok(rhs_ty)) => {
                        self.unify_ty_and_ty_inner(lhs_ty, rhs_ty, culprits, mode);
                    }
                    (Ok(lhs_ty), Err(rhs_floating)) => {
                        if let Err(err) = self.unify_var_and_non_var_ty(rhs_floating.root, lhs_ty) {
                            culprits.push(TyAndTyUnifyCulprit::RecursiveType(err));
                        }
                    }
                    (Err(lhs_floating), Ok(rhs_ty)) => {
                        if let Err(err) = self.unify_var_and_non_var_ty(lhs_floating.root, rhs_ty) {
                            culprits.push(TyAndTyUnifyCulprit::RecursiveType(err));
                        }
                    }
                    (Err(_), Err(_)) => {
                        // Cannot fail occurs check because neither type structurally includes the
                        // other.
                        self.types.union_unrelated_floating(lhs_var, rhs_var);
                    }
                }
            }
            (TyKind::InferVar(lhs_var), _) => match self.types.lookup(lhs_var) {
                Ok(known_lhs) => {
                    self.unify_ty_and_ty_inner(known_lhs, rhs, culprits, mode);
                }
                Err(lhs_var) => {
                    if let Err(err) = self.unify_var_and_non_var_ty(lhs_var.root, rhs) {
                        culprits.push(TyAndTyUnifyCulprit::RecursiveType(err));
                    }
                }
            },
            (_, TyKind::InferVar(rhs_var)) => match self.types.lookup(rhs_var) {
                Ok(known_rhs) => {
                    self.unify_ty_and_ty_inner(lhs, known_rhs, culprits, mode);
                }
                Err(rhs_var) => {
                    if let Err(err) = self.unify_var_and_non_var_ty(rhs_var.root, lhs) {
                        culprits.push(TyAndTyUnifyCulprit::RecursiveType(err));
                    }
                }
            },
            // Omissions okay because of intern equality fast-path:
            //
            // - `(Simple, Simple)`
            // - `(UniversalVar, UniversalVar)`
            // - `(HrtbVar, HrtbVar)`
            //
            // TODO: Check exhaustiveness automatically.
            _ => {
                culprits.push(TyAndTyUnifyCulprit::Types(lhs, rhs));
            }
        }
    }

    fn unify_var_and_non_var_ty(
        &mut self,
        lhs_var_root: InferTyVar,
        rhs_ty: Ty,
    ) -> Result<(), InferTyOccursError> {
        debug_assert_eq!(
            self.types.lookup(lhs_var_root).map_err(|v| v.root),
            Err(lhs_var_root),
        );

        struct OccursVisitor<'a, 'tcx> {
            ucx: &'a UnifyCx<'tcx>,
            reject: InferTyVar,
        }

        impl<'tcx> TyVisitor<'tcx> for OccursVisitor<'_, 'tcx> {
            type Break = ();

            fn tcx(&self) -> &'tcx TyCtxt {
                self.ucx.tcx()
            }

            fn visit_ty(&mut self, ty: SpannedTy) -> ControlFlow<Self::Break> {
                if let SpannedTyView::InferVar(var) = ty.view(self.tcx()) {
                    match self.ucx.types.lookup(var) {
                        Ok(resolved) => self.visit_fallible(resolved),
                        Err(other_floating) => {
                            if self.reject == other_floating.root {
                                ControlFlow::Break(())
                            } else {
                                ControlFlow::Continue(())
                            }
                        }
                    }
                } else {
                    self.walk_spanned_fallible(ty)
                }
            }
        }

        let does_occur = OccursVisitor {
            ucx: self,
            reject: lhs_var_root,
        }
        .visit_fallible(rhs_ty)
        .is_break();

        if does_occur {
            let occurs_in = self
                .substitutor(UnboundVarHandlingMode::NormalizeToRoot)
                .fold(rhs_ty);

            return Err(InferTyOccursError {
                var: lhs_var_root,
                occurs_in,
            });
        }

        self.types.assign_floating_to_non_var(lhs_var_root, rhs_ty);

        Ok(())
    }

    fn unify_dyn_trait_clauses_inner(
        &mut self,
        lhs_root: TraitClauseList,
        rhs_root: TraitClauseList,
        culprits: &mut Vec<TyAndTyUnifyCulprit>,
        mode: RelationMode,
    ) {
        let s = self.session();

        if lhs_root.r(s).len() != rhs_root.r(s).len() {
            culprits.push(TyAndTyUnifyCulprit::ClauseLists(lhs_root, rhs_root));
            return;
        }

        for (&lhs_clause, &rhs_clause) in lhs_root.r(s).iter().zip(rhs_root.r(s)) {
            match (lhs_clause, rhs_clause) {
                (TraitClause::Outlives(lhs), TraitClause::Outlives(rhs)) => {
                    // Technically, `MyTrait + 'a + 'b: 'c` could imply either `'a: 'c` or
                    // `'b: 'c`, meaning that relating both would be unnecessary but this
                    // logic will produce constraints for both. This isn't a problem because
                    // we only ever lower trait objects with *exactly one* outlives
                    // constraint.
                    self.unify_re_and_re(lhs, rhs, mode);
                }
                (TraitClause::Trait(lhs), TraitClause::Trait(rhs))
                    if lhs.inner.def == rhs.inner.def =>
                {
                    // Ensure that the binders are compatible.
                    let (
                        HrtbBinderKind::Imported(lhs_binder),
                        HrtbBinderKind::Imported(rhs_binder),
                    ) = (lhs.kind, rhs.kind)
                    else {
                        unreachable!()
                    };

                    if lhs_binder.r(s).len() != rhs_binder.r(s).len() {
                        culprits.push(TyAndTyUnifyCulprit::ClauseLists(lhs_root, rhs_root));
                        return;
                    }

                    for (&lhs, &rhs) in lhs_binder.r(s).iter().zip(rhs_binder.r(s)) {
                        if lhs.kind != rhs.kind {
                            culprits.push(TyAndTyUnifyCulprit::ClauseLists(lhs_root, rhs_root));
                            return;
                        }

                        self.unify_dyn_trait_clauses_inner(
                            lhs.clauses,
                            rhs.clauses,
                            culprits,
                            RelationMode::Equate,
                        );
                    }

                    // Ensure that the inner values are compatible. HRTBs are debruijn indexed so
                    // this properly checks for alpha-equivalence w.r.t the binders.
                    for (&lhs, &rhs) in lhs.inner.params.r(s).iter().zip(rhs.inner.params.r(s)) {
                        match (lhs, rhs) {
                            (TraitParam::Equals(lhs), TraitParam::Equals(rhs)) => {
                                match (lhs, rhs) {
                                    (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                                        self.unify_re_and_re(lhs, rhs, RelationMode::Equate);
                                    }
                                    (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                                        self.unify_ty_and_ty_inner(
                                            lhs,
                                            rhs,
                                            culprits,
                                            RelationMode::Equate,
                                        );
                                    }
                                    _ => unreachable!(),
                                }
                            }
                            (TraitParam::Unspecified(lhs), TraitParam::Unspecified(rhs)) => {
                                self.unify_dyn_trait_clauses_inner(
                                    lhs,
                                    rhs,
                                    culprits,
                                    RelationMode::Equate,
                                );
                            }
                            _ => {
                                culprits.push(TyAndTyUnifyCulprit::Params(lhs, rhs));
                            }
                        }
                    }
                }
                _ => {
                    culprits.push(TyAndTyUnifyCulprit::ClauseLists(lhs_root, rhs_root));
                    return;
                }
            }
        }
    }
}

// === InfTySubstitutor === //

#[derive(Debug, Copy, Clone)]
pub struct InferTySubstitutor<'a, 'tcx> {
    pub ucx: &'a UnifyCx<'tcx>,
    pub mode: UnboundVarHandlingMode,
}

#[derive(Debug, Copy, Clone)]
pub enum UnboundVarHandlingMode {
    Error(ErrorGuaranteed),
    NormalizeToRoot,
    EraseToSigInfer,
    Panic,
}

impl<'tcx> TyFolder<'tcx> for InferTySubstitutor<'_, 'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ucx.tcx()
    }

    fn fold_ty(&mut self, ty: SpannedTy) -> Result<Ty, Self::Error> {
        let TyKind::InferVar(var) = *ty.value.r(self.session()) else {
            return self.super_spanned_fallible(ty);
        };

        match self.ucx.lookup_ty_infer_var(var) {
            Ok(v) => self.fold_fallible(v),
            Err(floating) => Ok(match self.mode {
                UnboundVarHandlingMode::Error(error) => self.tcx().intern(TyKind::Error(error)),
                UnboundVarHandlingMode::NormalizeToRoot => {
                    self.tcx().intern(TyKind::InferVar(floating.root))
                }
                UnboundVarHandlingMode::EraseToSigInfer => self.tcx().intern(TyKind::SigInfer),
                UnboundVarHandlingMode::Panic => {
                    unreachable!("unexpected ambiguous inference variable")
                }
            }),
        }
    }
}
