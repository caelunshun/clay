use crate::{
    base::{ErrorGuaranteed, Session, arena::HasInterner},
    semantic::{
        analysis::{
            ClauseCx, ClauseOrigin, InferTyLeaksError, InferTyOccursError, InferTyUnifyError,
            TyAndTyUnifyCulprit, TyAndTyUnifyError, TyCtxt, TyFolder, TyFolderExt,
            TyFolderInfallibleExt, TyVisitor, TyVisitorExt, TyVisitorInfallibleExt,
            infer::unify::{regions::ReUnifyTracker, types::TyUnifyTracker},
        },
        syntax::{
            FnInstanceInner, FnOwner, HrtbBinderKind, HrtbUniverse, InferTyVar, Mutability, Re,
            ReVariance, RelationDirection, RelationMode, SpannedTy, SpannedTyView, TraitClause,
            TraitClauseList, TraitParam, TraitParamList, Ty, TyKind, TyOrRe, UniversalReVar,
            UniversalReVarSourceInfo, UniversalTyVar, UniversalTyVarSourceInfo,
        },
    },
    utils::hash::FxHashSet,
};
use index_vec::define_index_type;
use std::{convert::Infallible, ops::ControlFlow};

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
/// those obligations, you'll need an [`ClauseCx`](super::super::ClauseCx), which uses the
/// deferred-solving functionality of a [`ObligationCx`](super::super::ObligationCx) internally to
/// solve these obligations.
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
    pub max_universe: &'a HrtbUniverse,
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

    pub fn verify(&self, ccx: &ClauseCx<'_>) {
        if let Some(re) = &self.regions {
            re.verify(ccx);
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

    pub fn fresh_ty_infer_var(&mut self, max_universe: HrtbUniverse) -> InferTyVar {
        self.types.fresh_infer(max_universe)
    }

    pub fn fresh_ty_infer(&mut self, max_universe: HrtbUniverse) -> Ty {
        self.tcx()
            .intern(TyKind::InferVar(self.fresh_ty_infer_var(max_universe)))
    }

    pub fn fresh_ty_universal_var(
        &mut self,
        src_info: UniversalTyVarSourceInfo,
        in_universe: HrtbUniverse,
    ) -> UniversalTyVar {
        self.types.fresh_universal(src_info, in_universe)
    }

    pub fn fresh_ty_universal(
        &mut self,
        src_info: UniversalTyVarSourceInfo,
        in_universe: HrtbUniverse,
    ) -> Ty {
        self.tcx().intern(TyKind::UniversalVar(
            self.fresh_ty_universal_var(src_info, in_universe),
        ))
    }

    pub fn observe_ty_infer_var(&mut self, var: InferTyVar) -> ObservedTyInferVar {
        self.types.observe_infer(var)
    }

    pub fn observed_infer_reveal_order(&self) -> &[ObservedTyInferVar] {
        self.types.observed_infer_reveal_order()
    }

    pub fn lookup_ty_infer_var(&self, var: InferTyVar) -> Result<Ty, FloatingInferVar<'_>> {
        self.types.lookup_infer(var)
    }

    pub fn lookup_universal_ty_src_info(&self, var: UniversalTyVar) -> UniversalTyVarSourceInfo {
        self.types.lookup_universal_src_info(var)
    }

    pub fn lookup_universal_ty_hrtb_universe(&self, var: UniversalTyVar) -> &HrtbUniverse {
        self.types.lookup_universal_hrtb_universe(var)
    }

    pub fn peel_ty_infer_var(&self, ty: Ty) -> Ty {
        let s = self.session();

        match *ty.r(s) {
            TyKind::InferVar(var) => {
                if let Ok(var) = self.types.lookup_infer(var) {
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

    pub fn permit_universe_re_outlives_re(
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

    pub fn unify_re_and_re(&mut self, origin: &ClauseOrigin, lhs: Re, rhs: Re, mode: RelationMode) {
        let Some(regions) = &mut self.regions else {
            debug_assert!(matches!(lhs, Re::Erased));
            debug_assert!(matches!(rhs, Re::Erased));

            return;
        };

        for (lhs, rhs) in mode.enumerate(lhs, rhs) {
            regions.constrain(origin.clone(), lhs, rhs);
        }
    }

    /// Unifies two types such that they match. The `mode` specifies how the regions inside the
    /// types should be unified. For example, if it is `RelationMode::LhsOntoRhs`, relating
    /// `&'0 u32` and `&'1 u32` will result in the region relation `'0: '1`.
    pub fn unify_ty_and_ty(
        &mut self,
        origin: &ClauseOrigin,
        lhs: Ty,
        rhs: Ty,
        mode: RelationMode,
    ) -> Result<(), Box<TyAndTyUnifyError>> {
        let mut fork = self.clone();
        let mut culprits = Vec::new();

        fork.unify_ty_and_ty_inner(origin, lhs, rhs, &mut culprits, mode);

        if !culprits.is_empty() {
            return Err(Box::new(TyAndTyUnifyError {
                origin: origin.clone(),
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
        origin: &ClauseOrigin,
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
                self.unify_re_and_re(origin, lhs_re, rhs_re, mode);

                let variance = match lhs_muta {
                    Mutability::Mut => ReVariance::Invariant,
                    Mutability::Not => ReVariance::Covariant,
                };

                self.unify_ty_and_ty_inner(
                    origin,
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
                            self.unify_re_and_re(origin, lhs, rhs, mode);
                        }
                        (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                            self.unify_ty_and_ty_inner(origin, lhs, rhs, culprits, mode);
                        }
                        _ => unreachable!(),
                    }
                }
            }
            (TyKind::Trait(lhs_re, lhs_muta, lhs), TyKind::Trait(rhs_re, rhs_muta, rhs))
                if lhs_muta == rhs_muta =>
            {
                self.unify_re_and_re(origin, lhs_re, rhs_re, mode);

                let variance = match lhs_muta {
                    Mutability::Mut => ReVariance::Invariant,
                    Mutability::Not => ReVariance::Covariant,
                };

                self.unify_dyn_trait_clauses_inner(
                    origin,
                    lhs,
                    rhs,
                    culprits,
                    mode.with_variance(variance),
                );
            }
            (TyKind::FnDef(lhs_inst), TyKind::FnDef(rhs_inst)) => 'func: {
                let FnInstanceInner {
                    owner: lhs_owner,
                    early_args: lhs_early_args,
                } = *lhs_inst.r(s);

                let FnInstanceInner {
                    owner: rhs_owner,
                    early_args: rhs_early_args,
                } = *rhs_inst.r(s);

                match (lhs_owner, rhs_owner) {
                    (FnOwner::Item(lhs_def), FnOwner::Item(rhs_def)) => {
                        if lhs_def != rhs_def {
                            culprits.push(TyAndTyUnifyCulprit::Types(lhs, rhs));
                            break 'func;
                        }
                    }
                    (
                        FnOwner::Trait {
                            instance: lhs_instance,
                            self_ty: lhs_self_ty,
                            method_idx: lhs_method_idx,
                        },
                        FnOwner::Trait {
                            instance: rhs_instance,
                            self_ty: rhs_self_ty,
                            method_idx: rhs_method_idx,
                        },
                    ) => {
                        if lhs_instance.def != rhs_instance.def || lhs_method_idx != rhs_method_idx
                        {
                            culprits.push(TyAndTyUnifyCulprit::Types(lhs, rhs));
                            break 'func;
                        }

                        self.unify_trait_spec_params_inner(
                            origin,
                            lhs_instance.params,
                            rhs_instance.params,
                            culprits,
                        );

                        self.unify_ty_and_ty_inner(
                            origin,
                            lhs_self_ty,
                            rhs_self_ty,
                            culprits,
                            RelationMode::Equate,
                        );
                    }
                    (
                        FnOwner::Inherent {
                            self_ty: lhs_self_ty,
                            block: lhs_block,
                            method_idx: lhs_method_idx,
                        },
                        FnOwner::Inherent {
                            self_ty: rhs_self_ty,
                            block: rhs_block,
                            method_idx: rhs_method_idx,
                        },
                    ) => {
                        if lhs_block != rhs_block || lhs_method_idx != rhs_method_idx {
                            culprits.push(TyAndTyUnifyCulprit::Types(lhs, rhs));
                            break 'func;
                        }

                        self.unify_ty_and_ty_inner(
                            origin,
                            lhs_self_ty,
                            rhs_self_ty,
                            culprits,
                            RelationMode::Equate,
                        );
                    }
                    _ => unreachable!(),
                }

                match (lhs_early_args, rhs_early_args) {
                    (Some(lhs_generics), Some(rhs_generics)) => {
                        for (&lhs, &rhs) in lhs_generics.r(s).iter().zip(rhs_generics.r(s)) {
                            match (lhs, rhs) {
                                (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                                    self.unify_re_and_re(origin, lhs, rhs, RelationMode::Equate);
                                }
                                (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                                    self.unify_ty_and_ty_inner(
                                        origin,
                                        lhs,
                                        rhs,
                                        culprits,
                                        RelationMode::Equate,
                                    );
                                }
                                _ => unreachable!(),
                            }
                        }
                    }
                    (None, None) => {
                        // (trivially compatible)
                    }
                    _ => {
                        culprits.push(TyAndTyUnifyCulprit::Types(lhs, rhs));
                        break 'func;
                    }
                }
            }
            (TyKind::Tuple(lhs), TyKind::Tuple(rhs)) if lhs.r(s).len() == rhs.r(s).len() => {
                for (&lhs, &rhs) in lhs.r(s).iter().zip(rhs.r(s)) {
                    self.unify_ty_and_ty_inner(origin, lhs, rhs, culprits, mode);
                }
            }
            (TyKind::InferVar(lhs_var), TyKind::InferVar(rhs_var)) => {
                match (
                    self.types.lookup_infer(lhs_var),
                    self.types.lookup_infer(rhs_var),
                ) {
                    (Ok(lhs_ty), Ok(rhs_ty)) => {
                        self.unify_ty_and_ty_inner(origin, lhs_ty, rhs_ty, culprits, mode);
                    }
                    (Ok(lhs_ty), Err(rhs_floating)) => {
                        if let Err(err) = self.unify_var_and_non_var_ty(rhs_floating.root, lhs_ty) {
                            culprits.push(TyAndTyUnifyCulprit::InferTyUnify(err));
                        }
                    }
                    (Err(lhs_floating), Ok(rhs_ty)) => {
                        if let Err(err) = self.unify_var_and_non_var_ty(lhs_floating.root, rhs_ty) {
                            culprits.push(TyAndTyUnifyCulprit::InferTyUnify(err));
                        }
                    }
                    (Err(_), Err(_)) => {
                        // Cannot fail occurs check because neither type structurally includes the
                        // other.
                        self.types.union_unrelated_infer_floating(lhs_var, rhs_var);
                    }
                }
            }
            (TyKind::InferVar(lhs_var), _) => match self.types.lookup_infer(lhs_var) {
                Ok(known_lhs) => {
                    self.unify_ty_and_ty_inner(origin, known_lhs, rhs, culprits, mode);
                }
                Err(lhs_var) => {
                    if let Err(err) = self.unify_var_and_non_var_ty(lhs_var.root, rhs) {
                        culprits.push(TyAndTyUnifyCulprit::InferTyUnify(err));
                    }
                }
            },
            (_, TyKind::InferVar(rhs_var)) => match self.types.lookup_infer(rhs_var) {
                Ok(known_rhs) => {
                    self.unify_ty_and_ty_inner(origin, lhs, known_rhs, culprits, mode);
                }
                Err(rhs_var) => {
                    if let Err(err) = self.unify_var_and_non_var_ty(rhs_var.root, lhs) {
                        culprits.push(TyAndTyUnifyCulprit::InferTyUnify(err));
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
    ) -> Result<(), InferTyUnifyError> {
        let Err(FloatingInferVar {
            root: actual_root,
            observed_equivalent: _,
            max_universe: lhs_max_universe,
        }) = self.types.lookup_infer(lhs_var_root)
        else {
            unreachable!()
        };

        debug_assert_eq!(actual_root, lhs_var_root);

        let lhs_max_universe = lhs_max_universe.clone();

        // Perform occurs check
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
                    match self.ucx.types.lookup_infer(var) {
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

            return Err(InferTyUnifyError::Occurs(InferTyOccursError {
                var: lhs_var_root,
                occurs_in,
            }));
        }

        // Perform HRTB universe check. First, let's ensure that the root isn't being unified with
        // a type beyond its maximum universe.
        struct HrtbLeakVisitor<'a, 'tcx> {
            ucx: &'a UnifyCx<'tcx>,
            max_universe: &'a HrtbUniverse,
        }

        impl<'tcx> TyVisitor<'tcx> for HrtbLeakVisitor<'_, 'tcx> {
            type Break = UniversalTyVar;

            fn tcx(&self) -> &'tcx TyCtxt {
                self.ucx.tcx()
            }

            fn visit_ty(&mut self, ty: SpannedTy) -> ControlFlow<Self::Break> {
                match ty.view(self.tcx()) {
                    SpannedTyView::InferVar(var) => match self.ucx.types.lookup_infer(var) {
                        Ok(resolved) => self.visit_fallible(resolved)?,
                        Err(_) => {
                            // (don't constrain yet)
                        }
                    },
                    SpannedTyView::UniversalVar(var) => {
                        if !self
                            .max_universe
                            .is_leq_than(self.ucx.lookup_universal_ty_hrtb_universe(var))
                        {
                            return ControlFlow::Break(var);
                        }
                    }
                    _ => self.walk_spanned_fallible(ty)?,
                }

                ControlFlow::Continue(())
            }
        }

        let leak_result = HrtbLeakVisitor {
            ucx: self,
            max_universe: &lhs_max_universe,
        }
        .visit_fallible(rhs_ty);

        if let ControlFlow::Break(leaks_universal) = leak_result {
            return Err(InferTyUnifyError::Leaks(InferTyLeaksError {
                var: lhs_var_root,
                max_universe: lhs_max_universe,
                leaks_universal,
            }));
        }

        // The operation is valid. Perform it!
        self.types
            .assign_floating_infer_to_non_var(lhs_var_root, rhs_ty);

        // This is the second part of the HRTB universe check. Now that we know the operation is
        // valid, we need to ensure that any unbound inference variables in our concrete type are
        // constrained to our universe as well to avoid late-bound violations.
        struct InferUniverseConstrainVisitor<'a, 'tcx> {
            ucx: &'a mut UnifyCx<'tcx>,
            max_universe: &'a HrtbUniverse,
        }

        impl<'tcx> TyVisitor<'tcx> for InferUniverseConstrainVisitor<'_, 'tcx> {
            type Break = Infallible;

            fn tcx(&self) -> &'tcx TyCtxt {
                self.ucx.tcx()
            }

            fn visit_ty(&mut self, ty: SpannedTy) -> ControlFlow<Self::Break> {
                match ty.view(self.tcx()) {
                    SpannedTyView::InferVar(var) => match self.ucx.types.lookup_infer(var) {
                        Ok(resolved) => self.visit_fallible(resolved)?,
                        Err(_) => {
                            self.ucx
                                .types
                                .constrain_infer_max_universe(var, self.max_universe);
                        }
                    },
                    _ => self.walk_spanned_fallible(ty)?,
                }

                ControlFlow::Continue(())
            }
        }

        InferUniverseConstrainVisitor {
            ucx: self,
            max_universe: &lhs_max_universe,
        }
        .visit(rhs_ty);

        Ok(())
    }

    fn unify_dyn_trait_clauses_inner(
        &mut self,
        origin: &ClauseOrigin,
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
                (TraitClause::Outlives(lhs_dir, lhs), TraitClause::Outlives(rhs_dir, rhs))
                    if lhs_dir == rhs_dir =>
                {
                    match (lhs, rhs) {
                        (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                            self.unify_re_and_re(origin, lhs, rhs, mode);
                        }
                        (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                            self.unify_ty_and_ty_inner(origin, lhs, rhs, culprits, mode);
                        }
                        _ => unreachable!(),
                    }
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
                            origin,
                            lhs.clauses,
                            rhs.clauses,
                            culprits,
                            RelationMode::Equate,
                        );
                    }

                    // Ensure that the inner values are compatible. HRTBs are debruijn indexed so
                    // this properly checks for alpha-equivalence w.r.t the binders.
                    self.unify_trait_spec_params_inner(
                        origin,
                        lhs.inner.params,
                        rhs.inner.params,
                        culprits,
                    );
                }
                _ => {
                    culprits.push(TyAndTyUnifyCulprit::ClauseLists(lhs_root, rhs_root));
                    return;
                }
            }
        }
    }

    fn unify_trait_spec_params_inner(
        &mut self,
        origin: &ClauseOrigin,
        lhs: TraitParamList,
        rhs: TraitParamList,
        culprits: &mut Vec<TyAndTyUnifyCulprit>,
    ) {
        let s = self.session();

        for (&lhs, &rhs) in lhs.r(s).iter().zip(rhs.r(s)) {
            match (lhs, rhs) {
                (TraitParam::Equals(lhs), TraitParam::Equals(rhs)) => match (lhs, rhs) {
                    (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                        self.unify_re_and_re(origin, lhs, rhs, RelationMode::Equate);
                    }
                    (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                        self.unify_ty_and_ty_inner(
                            origin,
                            lhs,
                            rhs,
                            culprits,
                            RelationMode::Equate,
                        );
                    }
                    _ => unreachable!(),
                },
                (TraitParam::Unspecified(lhs), TraitParam::Unspecified(rhs)) => {
                    self.unify_dyn_trait_clauses_inner(
                        origin,
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
