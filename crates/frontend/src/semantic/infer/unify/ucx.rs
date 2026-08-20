use super::{regions::ReUnifyTracker, types::TyUnifyTracker};
use crate::{
    base::{ErrorGuaranteed, Session, analysis::DebruijnTop, arena::HasInterner},
    semantic::{
        infer::{
            ClauseCx, HrtbUniverse, InferTyLeaksHrtbVarError, InferTyLeaksUniversalError,
            InferTyOccursError, MultiPromiseBuilder, Promise, ReAndReUnifyError,
            TyAndSimpleTySetUnifyError, TyAndTyRegionUnifyError, TyAndTyStructuralUnifyError,
            TyAndTyUnifyCulprit,
        },
        syntax::{
            FnInstanceInner, FnOwner, FnOwnerInherent, FnOwnerTrait, HrtbBinder, InferTyVar,
            InferTyVarSourceInfo, Mutability, Re, ReVariance, RelationDirection, RelationMode,
            SimpleTySet, TraitClause, TraitClauseList, TraitParam, TraitParamList, Ty, TyCtxt,
            TyFolder, TyFolderExt, TyFolderInfallibleExt, TyKind, TyOrRe, TyVisitor, TyVisitorExt,
            TyVisitorInfallibleExt, UniversalReVar, UniversalReVarSourceInfo, UniversalTyVar,
            UniversalTyVarSourceInfo,
        },
    },
};
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
    regions: Option<ReUnifyTracker<'tcx>>,
}

#[derive(Debug, Copy, Clone)]
pub struct FloatingInferVar<'a> {
    pub root: InferTyVar,
    pub max_universe: &'a HrtbUniverse,
    pub perm_set: SimpleTySet,
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

    pub fn verify(&self, ccx: &ClauseCx<'tcx>) {
        if let Some(re) = &self.regions {
            re.verify(ccx);
        }
    }

    pub fn substitutor(&self, mode: UnboundVarHandlingMode) -> InferTySubstitutor<'_, 'tcx> {
        InferTySubstitutor { ucx: self, mode }
    }

    pub fn fresh_ty_infer_var(
        &mut self,
        max_universe: HrtbUniverse,
        source_info: InferTyVarSourceInfo,
        perm_set: SimpleTySet,
    ) -> InferTyVar {
        self.types.fresh_infer(max_universe, source_info, perm_set)
    }

    pub fn next_ty_infer_var(&self) -> InferTyVar {
        self.types.next_infer()
    }

    pub fn fresh_ty_universal_var(
        &mut self,
        in_universe: HrtbUniverse,
        src_info: UniversalTyVarSourceInfo,
    ) -> UniversalTyVar {
        self.types.fresh_universal(in_universe, src_info)
    }

    pub fn lookup_ty_infer_var(&self, var: InferTyVar) -> Result<Ty, FloatingInferVar<'_>> {
        self.types.lookup_infer(var)
    }

    pub fn force_update_permissions_of_ty_var(&mut self, var: InferTyVar, perms: SimpleTySet) {
        self.types.force_update_permissions_of_ty_var(var, perms);
    }

    pub fn lookup_universal_ty_src_info(&self, var: UniversalTyVar) -> UniversalTyVarSourceInfo {
        self.types.lookup_universal_src_info(var)
    }

    pub fn lookup_infer_ty_src_info(&self, var: InferTyVar) -> InferTyVarSourceInfo {
        self.types.lookup_infer_src_info(var)
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

    pub fn unify_re_and_re(
        &mut self,
        lhs: Re,
        rhs: Re,
        mode: RelationMode,
    ) -> Promise<'tcx, ReAndReUnifyError> {
        let Some(regions) = &mut self.regions else {
            debug_assert!(matches!(lhs, Re::Erased));
            debug_assert!(matches!(rhs, Re::Erased));

            return Promise::trivial();
        };

        let mut collector = MultiPromiseBuilder::default();

        for (lhs, rhs) in mode.enumerate(lhs, rhs) {
            regions.constrain(lhs, rhs).join(&mut collector);
        }

        collector
            .finish()
            .map(move |_ccx, causes| ReAndReUnifyError {
                lhs,
                rhs,
                mode,
                causes,
            })
    }

    /// Unifies two types such that they match. The `mode` specifies how the regions inside the
    /// types should be unified. For example, if it is `RelationMode::LhsOntoRhs`, relating
    /// `&'0 u32` and `&'1 u32` will result in the region relation `'0: '1`.
    pub fn unify_ty_and_ty(
        &mut self,
        lhs: Ty,
        rhs: Ty,
        mode: RelationMode,
    ) -> Result<Promise<'tcx, TyAndTyRegionUnifyError>, Box<TyAndTyStructuralUnifyError>> {
        let mut re_collector = MultiPromiseBuilder::new();

        let mut fork = self.clone();
        let mut ty_culprits = Vec::new();

        fork.unify_ty_and_ty_inner(lhs, rhs, &mut ty_culprits, &mut re_collector, mode);

        if !ty_culprits.is_empty() {
            return Err(Box::new(TyAndTyStructuralUnifyError {
                origin_lhs: lhs,
                origin_rhs: rhs,
                culprits: ty_culprits,
            }));
        }

        *self = fork;

        Ok(re_collector
            .finish()
            .map(move |_ccx, regions| TyAndTyRegionUnifyError {
                lhs,
                rhs,
                mode,
                regions,
            }))
    }

    fn unify_ty_and_ty_inner(
        &mut self,
        lhs: Ty,
        rhs: Ty,
        ty_culprits: &mut Vec<TyAndTyUnifyCulprit>,
        re_collector: &mut MultiPromiseBuilder<'tcx, ReAndReUnifyError>,
        mode: RelationMode,
    ) {
        let tcx = self.tcx();
        let s = self.session();

        if lhs == rhs {
            // The types are compatible!
            return;
        }

        match (*lhs.r(s), *rhs.r(s)) {
            (TyKind::Error(error), _) | (_, TyKind::Error(error)) => {
                // This is accepted regardless of the other side.

                // We do, however, wish to propagate inference errors.
                if let (TyKind::InferVar(var), _) | (_, TyKind::InferVar(var)) =
                    (*lhs.r(s), *rhs.r(s))
                    && let Err(FloatingInferVar { root, .. }) = self.lookup_ty_infer_var(var)
                {
                    // Ignore errors if permissions prevent the propagation.
                    _ = self.unify_var_and_non_var_ty(root, tcx.intern(TyKind::Error(error)));
                }
            }
            (
                TyKind::Reference(lhs_re, lhs_muta, lhs_pointee),
                TyKind::Reference(rhs_re, rhs_muta, rhs_pointee),
            ) if lhs_muta == rhs_muta => {
                self.unify_re_and_re(lhs_re, rhs_re, mode)
                    .join(re_collector);

                let variance = match lhs_muta {
                    Mutability::Mut => ReVariance::Invariant,
                    Mutability::Not => ReVariance::Covariant,
                };

                self.unify_ty_and_ty_inner(
                    lhs_pointee,
                    rhs_pointee,
                    ty_culprits,
                    re_collector,
                    mode.with_variance(variance),
                );
            }
            (TyKind::Adt(lhs), TyKind::Adt(rhs)) if lhs.def == rhs.def => {
                // TODO: variance

                for (&lhs, &rhs) in lhs.params.r(s).iter().zip(rhs.params.r(s)) {
                    match (lhs, rhs) {
                        (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                            self.unify_re_and_re(lhs, rhs, mode).join(re_collector);
                        }
                        (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                            self.unify_ty_and_ty_inner(lhs, rhs, ty_culprits, re_collector, mode);
                        }
                        _ => unreachable!(),
                    }
                }
            }
            (TyKind::HrtbProjection(lhs), TyKind::HrtbProjection(rhs))
                if lhs.spec.def == rhs.spec.def && lhs.assoc_idx == rhs.assoc_idx =>
            {
                self.unify_ty_and_ty_inner(
                    lhs.target,
                    rhs.target,
                    ty_culprits,
                    re_collector,
                    RelationMode::Equate,
                );

                self.unify_trait_spec_params_inner(
                    lhs.spec.params,
                    rhs.spec.params,
                    ty_culprits,
                    re_collector,
                );
            }
            (TyKind::Trait(lhs_re, lhs_muta, lhs), TyKind::Trait(rhs_re, rhs_muta, rhs))
                if lhs_muta == rhs_muta =>
            {
                self.unify_re_and_re(lhs_re, rhs_re, mode)
                    .join(re_collector);

                let variance = match lhs_muta {
                    Mutability::Mut => ReVariance::Invariant,
                    Mutability::Not => ReVariance::Covariant,
                };

                self.unify_dyn_trait_clauses_inner(
                    lhs,
                    rhs,
                    ty_culprits,
                    re_collector,
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

                // TODO: Check exhaustiveness automatically.
                match (lhs_owner, rhs_owner) {
                    (FnOwner::Item(lhs_def), FnOwner::Item(rhs_def)) => {
                        if lhs_def != rhs_def {
                            ty_culprits.push(TyAndTyUnifyCulprit::Types(lhs, rhs));
                            break 'func;
                        }
                    }
                    (
                        FnOwner::Trait(FnOwnerTrait {
                            instance: lhs_instance,
                            self_ty: lhs_self_ty,
                            method_idx: lhs_method_idx,
                        }),
                        FnOwner::Trait(FnOwnerTrait {
                            instance: rhs_instance,
                            self_ty: rhs_self_ty,
                            method_idx: rhs_method_idx,
                        }),
                    ) => {
                        if lhs_instance.def != rhs_instance.def || lhs_method_idx != rhs_method_idx
                        {
                            ty_culprits.push(TyAndTyUnifyCulprit::Types(lhs, rhs));
                            break 'func;
                        }

                        self.unify_trait_spec_params_inner(
                            lhs_instance.params,
                            rhs_instance.params,
                            ty_culprits,
                            re_collector,
                        );

                        self.unify_ty_and_ty_inner(
                            lhs_self_ty,
                            rhs_self_ty,
                            ty_culprits,
                            re_collector,
                            RelationMode::Equate,
                        );
                    }
                    (
                        FnOwner::Inherent(FnOwnerInherent {
                            self_ty: lhs_self_ty,
                            block: lhs_block,
                            method_idx: lhs_method_idx,
                        }),
                        FnOwner::Inherent(FnOwnerInherent {
                            self_ty: rhs_self_ty,
                            block: rhs_block,
                            method_idx: rhs_method_idx,
                        }),
                    ) => {
                        if lhs_block != rhs_block || lhs_method_idx != rhs_method_idx {
                            ty_culprits.push(TyAndTyUnifyCulprit::Types(lhs, rhs));
                            break 'func;
                        }

                        self.unify_ty_and_ty_inner(
                            lhs_self_ty,
                            rhs_self_ty,
                            ty_culprits,
                            re_collector,
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
                                    self.unify_re_and_re(lhs, rhs, RelationMode::Equate)
                                        .join(re_collector);
                                }
                                (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                                    self.unify_ty_and_ty_inner(
                                        lhs,
                                        rhs,
                                        ty_culprits,
                                        re_collector,
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
                        ty_culprits.push(TyAndTyUnifyCulprit::Types(lhs, rhs));
                        break 'func;
                    }
                }
            }
            (TyKind::Tuple(lhs), TyKind::Tuple(rhs)) if lhs.r(s).len() == rhs.r(s).len() => {
                for (&lhs, &rhs) in lhs.r(s).iter().zip(rhs.r(s)) {
                    self.unify_ty_and_ty_inner(lhs, rhs, ty_culprits, re_collector, mode);
                }
            }
            (TyKind::InferVar(lhs_var), TyKind::InferVar(rhs_var)) => {
                match (
                    self.types.lookup_infer(lhs_var),
                    self.types.lookup_infer(rhs_var),
                ) {
                    (Ok(lhs_ty), Ok(rhs_ty)) => {
                        self.unify_ty_and_ty_inner(lhs_ty, rhs_ty, ty_culprits, re_collector, mode);
                    }
                    (Ok(lhs_ty), Err(rhs_floating)) => {
                        if let Err(err) = self.unify_var_and_non_var_ty(rhs_floating.root, lhs_ty) {
                            ty_culprits.push(err);
                        }
                    }
                    (Err(lhs_floating), Ok(rhs_ty)) => {
                        if let Err(err) = self.unify_var_and_non_var_ty(lhs_floating.root, rhs_ty) {
                            ty_culprits.push(err);
                        }
                    }
                    (
                        Err(FloatingInferVar {
                            perm_set: lhs_perm_set,
                            ..
                        }),
                        Err(FloatingInferVar {
                            perm_set: rhs_perm_set,
                            ..
                        }),
                    ) => {
                        // Cannot fail occurs check because neither type structurally includes the
                        // other.
                        if !lhs_perm_set.intersection(rhs_perm_set).is_empty() {
                            self.types
                                .union_unrelated_infer_floating(self.tcx, lhs_var, rhs_var);
                        } else {
                            ty_culprits.push(TyAndTyUnifyCulprit::NotPermittedFloating(
                                lhs_perm_set,
                                rhs_perm_set,
                            ));
                        }
                    }
                }
            }
            (TyKind::InferVar(lhs_var), _) => match self.types.lookup_infer(lhs_var) {
                Ok(known_lhs) => {
                    self.unify_ty_and_ty_inner(known_lhs, rhs, ty_culprits, re_collector, mode);
                }
                Err(lhs_var) => {
                    if let Err(err) = self.unify_var_and_non_var_ty(lhs_var.root, rhs) {
                        ty_culprits.push(err);
                    }
                }
            },
            (_, TyKind::InferVar(rhs_var)) => match self.types.lookup_infer(rhs_var) {
                Ok(known_rhs) => {
                    self.unify_ty_and_ty_inner(lhs, known_rhs, ty_culprits, re_collector, mode);
                }
                Err(rhs_var) => {
                    if let Err(err) = self.unify_var_and_non_var_ty(rhs_var.root, lhs) {
                        ty_culprits.push(err);
                    }
                }
            },
            // Omissions okay because of intern equality fast-path:
            //
            // - `(Simple, Simple)`
            // - `(UniversalVar, UniversalVar)`
            // - `(HrtbVar, HrtbVar)`
            // - `(FnDef(FnDefAdtCtor), FnDef(FnDefAdtCtor))`
            //
            // TODO: Check exhaustiveness automatically.
            _ => {
                ty_culprits.push(TyAndTyUnifyCulprit::Types(lhs, rhs));
            }
        }
    }

    fn unify_var_and_non_var_ty(
        &mut self,
        lhs_var_root: InferTyVar,
        rhs_ty: Ty,
    ) -> Result<(), TyAndTyUnifyCulprit> {
        let s = self.session();

        let Err(FloatingInferVar {
            root: actual_root,
            max_universe: lhs_max_universe,
            perm_set: lhs_perm_set,
        }) = self.types.lookup_infer(lhs_var_root)
        else {
            unreachable!()
        };

        debug_assert_eq!(actual_root, lhs_var_root);

        let lhs_max_universe = lhs_max_universe.clone();

        // Check permissions
        if !lhs_perm_set.can_accept_type(rhs_ty, s) {
            return Err(TyAndTyUnifyCulprit::NotPermittedSolid(lhs_perm_set, rhs_ty));
        }

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

            fn visit_ty(&mut self, ty: Ty) -> ControlFlow<Self::Break> {
                if let TyKind::InferVar(var) = *ty.r(self.session()) {
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
                    self.walk_fallible(ty)
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

            return Err(TyAndTyUnifyCulprit::Occurs(InferTyOccursError {
                var: lhs_var_root,
                occurs_in,
            }));
        }

        // Perform HRTB universe check. First, let's ensure that the root isn't being unified with
        // a type beyond its maximum universe.
        struct HrtbLeakUniversalVisitor<'a, 'tcx> {
            ucx: &'a UnifyCx<'tcx>,
            max_universe: &'a HrtbUniverse,
        }

        impl<'tcx> TyVisitor<'tcx> for HrtbLeakUniversalVisitor<'_, 'tcx> {
            type Break = UniversalTyVar;

            fn tcx(&self) -> &'tcx TyCtxt {
                self.ucx.tcx()
            }

            fn visit_ty(&mut self, ty: Ty) -> ControlFlow<Self::Break> {
                match *ty.r(self.session()) {
                    TyKind::InferVar(var) => match self.ucx.types.lookup_infer(var) {
                        Ok(resolved) => self.visit_fallible(resolved)?,
                        Err(_) => {
                            // (don't constrain yet)
                        }
                    },
                    TyKind::UniversalVar(var) => {
                        if !self
                            .ucx
                            .lookup_universal_ty_hrtb_universe(var)
                            .is_leq_than(self.max_universe)
                        {
                            return ControlFlow::Break(var);
                        }
                    }
                    _ => self.walk_fallible(ty)?,
                }

                ControlFlow::Continue(())
            }
        }

        let leak_universal_result = HrtbLeakUniversalVisitor {
            ucx: self,
            max_universe: &lhs_max_universe,
        }
        .visit_fallible(rhs_ty);

        if let ControlFlow::Break(leaks_universal) = leak_universal_result {
            return Err(TyAndTyUnifyCulprit::LeaksUniversal(
                InferTyLeaksUniversalError {
                    var: lhs_var_root,
                    max_universe: lhs_max_universe,
                    leaks_universal,
                },
            ));
        }

        // We should also ensure that inference variables never have unbound HRTB variables. This is
        // an acceptable restriction which doesn't have to take universes into account because we
        // will only ever get into this scenario if we attempt to unify two `Trait` objects. All
        // inference variables in such a unification will necessarily be outside of the binder and
        // so we can treat them identically to a leaked universal.
        struct HrtbLeakHrtbVarVisitor<'a, 'tcx> {
            ucx: &'a UnifyCx<'tcx>,
            debruijn: DebruijnTop,
        }

        impl<'tcx> TyVisitor<'tcx> for HrtbLeakHrtbVarVisitor<'_, 'tcx> {
            type Break = ();

            fn tcx(&self) -> &'tcx TyCtxt {
                self.ucx.tcx()
            }

            fn visit_hrtb_binder(&mut self, binder: HrtbBinder) -> ControlFlow<Self::Break> {
                let s = self.session();

                self.debruijn.move_inwards_by(binder.defs.r(s).len());
                self.visit_fallible(binder.inner)?;
                self.debruijn.move_outwards_by(binder.defs.r(s).len());
                ControlFlow::Continue(())
            }

            fn visit_ty(&mut self, ty: Ty) -> ControlFlow<Self::Break> {
                match *ty.r(self.session()) {
                    TyKind::InferVar(_) => {
                        // We can skip this because, by invariant, inference variables will never
                        // contain these types of variables.
                    }
                    TyKind::HrtbVar(var) => {
                        if self.debruijn.try_lookup_relative(var.0).is_none() {
                            return ControlFlow::Break(());
                        }
                    }
                    _ => self.walk_fallible(ty)?,
                }

                ControlFlow::Continue(())
            }
        }

        let leak_hrtb_var_result = HrtbLeakHrtbVarVisitor {
            ucx: self,
            debruijn: DebruijnTop::ZERO,
        }
        .visit_fallible(rhs_ty);

        if leak_hrtb_var_result.is_break() {
            return Err(TyAndTyUnifyCulprit::LeaksHrtbVar(
                InferTyLeaksHrtbVarError { var: lhs_var_root },
            ));
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

            fn visit_ty(&mut self, ty: Ty) -> ControlFlow<Self::Break> {
                match *ty.r(self.session()) {
                    TyKind::InferVar(var) => match self.ucx.types.lookup_infer(var) {
                        Ok(resolved) => self.visit_fallible(resolved)?,
                        Err(_) => {
                            self.ucx
                                .types
                                .restrict_floating_infer_max_universe(var, self.max_universe);
                        }
                    },
                    _ => self.walk_fallible(ty)?,
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
        lhs_root: TraitClauseList,
        rhs_root: TraitClauseList,
        ty_culprits: &mut Vec<TyAndTyUnifyCulprit>,
        re_collector: &mut MultiPromiseBuilder<'tcx, ReAndReUnifyError>,
        mode: RelationMode,
    ) {
        let s = self.session();

        if lhs_root.r(s).len() != rhs_root.r(s).len() {
            ty_culprits.push(TyAndTyUnifyCulprit::ClauseLists(lhs_root, rhs_root));
            return;
        }

        for (&lhs_clause, &rhs_clause) in lhs_root.r(s).iter().zip(rhs_root.r(s)) {
            match (lhs_clause, rhs_clause) {
                (TraitClause::Outlives(lhs_dir, lhs), TraitClause::Outlives(rhs_dir, rhs))
                    if lhs_dir == rhs_dir =>
                {
                    match (lhs, rhs) {
                        (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                            self.unify_re_and_re(lhs, rhs, mode).join(re_collector);
                        }
                        (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                            self.unify_ty_and_ty_inner(lhs, rhs, ty_culprits, re_collector, mode);
                        }
                        _ => unreachable!(),
                    }
                }
                (TraitClause::Trait(lhs), TraitClause::Trait(rhs))
                    if lhs.inner.def == rhs.inner.def =>
                {
                    if lhs.defs.r(s).len() != rhs.defs.r(s).len() {
                        ty_culprits.push(TyAndTyUnifyCulprit::ClauseLists(lhs_root, rhs_root));
                        return;
                    }

                    for (&lhs, &rhs) in lhs.defs.r(s).iter().zip(rhs.defs.r(s)) {
                        if lhs.kind != rhs.kind {
                            ty_culprits.push(TyAndTyUnifyCulprit::ClauseLists(lhs_root, rhs_root));
                            return;
                        }

                        self.unify_dyn_trait_clauses_inner(
                            lhs.clauses,
                            rhs.clauses,
                            ty_culprits,
                            re_collector,
                            RelationMode::Equate,
                        );
                    }

                    // Ensure that the inner values are compatible. HRTBs are debruijn indexed so
                    // this properly checks for alpha-equivalence w.r.t the binders.
                    self.unify_trait_spec_params_inner(
                        lhs.inner.params,
                        rhs.inner.params,
                        ty_culprits,
                        re_collector,
                    );
                }
                _ => {
                    ty_culprits.push(TyAndTyUnifyCulprit::ClauseLists(lhs_root, rhs_root));
                    return;
                }
            }
        }
    }

    fn unify_trait_spec_params_inner(
        &mut self,
        lhs: TraitParamList,
        rhs: TraitParamList,
        ty_culprits: &mut Vec<TyAndTyUnifyCulprit>,
        re_collector: &mut MultiPromiseBuilder<'tcx, ReAndReUnifyError>,
    ) {
        let s = self.session();

        for (&lhs, &rhs) in lhs.r(s).iter().zip(rhs.r(s)) {
            match (lhs, rhs) {
                (TraitParam::Equals(lhs), TraitParam::Equals(rhs)) => match (lhs, rhs) {
                    (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                        self.unify_re_and_re(lhs, rhs, RelationMode::Equate)
                            .join(re_collector);
                    }
                    (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                        self.unify_ty_and_ty_inner(
                            lhs,
                            rhs,
                            ty_culprits,
                            re_collector,
                            RelationMode::Equate,
                        );
                    }
                    _ => unreachable!(),
                },
                (TraitParam::Unspecified(lhs), TraitParam::Unspecified(rhs)) => {
                    self.unify_dyn_trait_clauses_inner(
                        lhs,
                        rhs,
                        ty_culprits,
                        re_collector,
                        RelationMode::Equate,
                    );
                }
                _ => {
                    ty_culprits.push(TyAndTyUnifyCulprit::Params(lhs, rhs));
                }
            }
        }
    }

    pub fn unify_ty_and_simple_set(
        &mut self,
        lhs: Ty,
        rhs: SimpleTySet,
    ) -> Result<(), TyAndSimpleTySetUnifyError> {
        let tcx = self.tcx();
        let s = self.session();

        let success = match *lhs.r(s) {
            TyKind::InferVar(var) => match self.lookup_ty_infer_var(var) {
                Ok(ty) => rhs.can_accept_type(ty, s),
                Err(FloatingInferVar { perm_set, .. }) => {
                    if perm_set.intersects(rhs) {
                        self.types.restrict_perm_set_of_floating(tcx, var, rhs);
                        true
                    } else {
                        false
                    }
                }
            },
            TyKind::Error(_err) => true,
            _ => rhs.can_accept_type(lhs, s),
        };

        if success {
            Ok(())
        } else {
            Err(TyAndSimpleTySetUnifyError { lhs, rhs })
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
    /// All unbound type variables are turned into `Ty::Error`.
    Error(ErrorGuaranteed),

    /// All unbound type variables are turned into their unique root representation.
    NormalizeToRoot,

    /// Panic on encountering an unbound type variable.
    Panic,
}

impl<'tcx> TyFolder<'tcx> for InferTySubstitutor<'_, 'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ucx.tcx()
    }

    fn fold_ty(&mut self, ty: Ty) -> Result<Ty, Self::Error> {
        let TyKind::InferVar(var) = *ty.r(self.session()) else {
            return self.super_fallible(ty);
        };

        match self.ucx.lookup_ty_infer_var(var) {
            Ok(v) => self.fold_fallible(v),
            Err(floating) => Ok(match self.mode {
                UnboundVarHandlingMode::Error(error) => self.tcx().intern(TyKind::Error(error)),
                UnboundVarHandlingMode::NormalizeToRoot => {
                    self.tcx().intern(TyKind::InferVar(floating.root))
                }
                UnboundVarHandlingMode::Panic => {
                    unreachable!("unexpected ambiguous inference variable")
                }
            }),
        }
    }
}
