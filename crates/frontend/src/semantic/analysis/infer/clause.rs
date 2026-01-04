use crate::{
    base::{
        Diag, Session,
        analysis::{DebruijnAbsoluteRange, DebruijnTop, Spanned},
        arena::{HasInterner, HasListInterner, Obj},
        syntax::Span,
    },
    semantic::{
        analysis::{
            CoherenceMap, ConfirmationResult, FloatingInferVar, ObligationCx, ObligationKind,
            ObligationReason, ObligationResult, SelectionRejected, SelectionResult, TyCtxt,
            TyFoldable, TyFolder, TyFolderExt, TyFolderInfallibleExt, TyFolderPreservesSpans,
            TyVisitor, TyVisitorInfallibleExt, UnboundVarHandlingMode, UnifyCx, UnifyCxMode,
        },
        syntax::{
            AdtInstance, AdtItem, AnyGeneric, FnDef, GenericBinder, GenericSubst, HrtbBinder,
            HrtbBinderKind, HrtbDebruijn, HrtbDebruijnDef, ImplItem, InferTyVar, Re, RelationMode,
            SpannedAdtInstance, SpannedHrtbBinder, SpannedHrtbBinderView, SpannedRe,
            SpannedTraitInstance, SpannedTraitParamView, SpannedTraitSpec, SpannedTy,
            SpannedTyOrRe, SpannedTyOrReList, SpannedTyProjectionView, SpannedTyView, TraitClause,
            TraitClauseList, TraitItem, TraitParam, TraitSpec, Ty, TyKind, TyOrRe, TyOrReKind,
            TyOrReList, UniversalReVar, UniversalReVarSourceInfo, UniversalTyVar,
            UniversalTyVarSourceInfo,
        },
    },
    utils::hash::FxHashMap,
};
use index_vec::IndexVec;
use std::{convert::Infallible, ops::ControlFlow};

// === ClauseCx Core === //

/// A type inference context for solving type obligations of the form...
///
/// - `Region: Region`
/// - `Type = Type`
/// - `Type: Clauses`
/// - `well-formed Type`
///
/// Obligations are enqueued out of order and the context solves them as inference variables arrive.
///
/// This context is built on top of an [`ObligationCx`].
///
/// ## Multi-Pass Checking
///
/// This context has two modes: region unaware and region aware.
///
/// - The region unaware mode just solves for type equalities, making it ideal for a first pass of
///   type-checker where one just wants to solve for type inference variables. This process is
///   allowed to fail.
///
/// - The region aware mode can take the solved inference types and, after replacing all the erased
///   regions within those solved inference types with fresh region inference variables, it can run
///   a second pass of type-checking to ensure that region inference is correct.
///
/// If all the types checked with a region aware check were obtained by a prior region unaware
/// type-check, the inference methods will never return type errors—only region errors.
///
/// This two-pass design is necessary because we want each inferred expression type to have its own
/// set of fresh region inference variables. If we instead tried to do type solving in a single
/// pass, we'd either have to...
///
/// a) Wait until a source expression's type is fully solved so that we can replace all its regions
///    with fresh region variables, which could prevent us from properly inferring certain patterns.
///
/// b) Equate source expression types without instantiating fresh new inference variable for each of
///    them, preventing us from handling region-based sub-typing. This is what using a region-aware
///    mode for the first inference pass would accomplish.
///
/// Note that, if there are no type inference variables involved in your seed queries (e.g. when
/// WF-checking traits), you can immediately skip to region aware checking.
#[derive(Clone)]
pub struct ClauseCx<'tcx> {
    ocx: ObligationCx<'tcx>,
    coherence: &'tcx CoherenceMap,
    universal_vars: IndexVec<UniversalTyVar, UniversalTyVarDescriptor>,
}

#[derive(Clone)]
struct UniversalTyVarDescriptor {
    src_info: UniversalTyVarSourceInfo,
    direct_clauses: Option<TraitClauseList>,
    elaboration: Option<UniversalElaboration>,
}

#[derive(Debug, Copy, Clone)]
pub struct UniversalElaboration {
    pub clauses: TraitClauseList,
    pub lub_re: Re,
}

impl<'tcx> ClauseCx<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, coherence: &'tcx CoherenceMap, mode: UnifyCxMode) -> Self {
        Self {
            ocx: ObligationCx::new(tcx, mode),
            coherence,
            universal_vars: IndexVec::new(),
        }
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.ocx.tcx()
    }

    pub fn session(&self) -> &'tcx Session {
        self.ocx.session()
    }

    pub fn coherence(&self) -> &'tcx CoherenceMap {
        self.coherence
    }

    pub fn ucx(&self) -> &UnifyCx<'tcx> {
        self.ocx.ucx()
    }

    pub fn ucx_mut(&mut self) -> &mut UnifyCx<'tcx> {
        self.ocx.ucx_mut()
    }

    fn push_obligation(&mut self, reason: ObligationReason, kind: ObligationKind) {
        self.ocx.push_obligation(reason, kind);
        self.process_obligations();
    }

    fn process_obligations(&mut self) {
        ObligationCx::poll_obligations(
            self,
            |this| &mut this.ocx,
            |this| this.clone(),
            |fork, kind| match kind {
                ObligationKind::ReAndRe(lhs, rhs, mode) => {
                    match fork.ucx_mut().unify_re_and_re(lhs, rhs, mode) {
                        Ok(()) => ObligationResult::Success,
                        Err(err) => ObligationResult::Failure(err.to_diag()),
                    }
                }
                ObligationKind::TyAndTy(lhs, rhs, mode) => {
                    match fork.ucx_mut().unify_ty_and_ty(lhs, rhs, mode) {
                        Ok(()) => ObligationResult::Success,
                        Err(err) => ObligationResult::Failure(err.to_diag()),
                    }
                }
                ObligationKind::TyAndTrait(lhs, rhs) => fork.run_oblige_ty_and_trait(lhs, rhs),
                ObligationKind::TyAndRe(lhs, rhs) => fork.run_oblige_ty_and_re(lhs, rhs),
                ObligationKind::TyWf(ty) => fork.run_oblige_ty_wf(ty),
            },
        );
    }
}

// Basic operations
impl<'tcx> ClauseCx<'tcx> {
    pub fn mode(&self) -> UnifyCxMode {
        self.ucx().mode()
    }

    pub fn suppress_obligation_eval<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let was_suppressed = self.ocx.obligation_eval_suppressed();
        self.ocx.set_obligation_eval_suppressed(true);

        let mut this = scopeguard::guard(self, |this| {
            this.ocx.set_obligation_eval_suppressed(was_suppressed)
        });

        f(&mut this)
    }

    pub fn fresh_ty_infer_var(&mut self) -> InferTyVar {
        self.ucx_mut().fresh_ty_infer_var()
    }

    pub fn fresh_ty_infer(&mut self) -> Ty {
        self.ucx_mut().fresh_ty_infer()
    }

    pub fn lookup_ty_infer_var(&self, var: InferTyVar) -> Result<Ty, FloatingInferVar<'_>> {
        self.ucx().lookup_ty_infer_var(var)
    }

    pub fn peel_ty_infer_var(&self, ty: Ty) -> Ty {
        self.ucx().peel_ty_infer_var(ty)
    }

    pub fn fresh_re_infer(&mut self) -> Re {
        self.ucx_mut().fresh_re_infer()
    }

    pub fn fresh_re_universal(&mut self, src_info: UniversalReVarSourceInfo) -> Re {
        self.ucx_mut().fresh_re_universal(src_info)
    }

    pub fn lookup_universal_re_src_info(
        &mut self,
        var: UniversalReVar,
    ) -> UniversalReVarSourceInfo {
        self.ucx_mut().lookup_universal_re_src_info(var)
    }

    pub fn permit_re_universal_outlives(&mut self, lhs: Re, rhs: Re) {
        self.ucx_mut().permit_re_universal_outlives(lhs, rhs);
    }

    pub fn fresh_ty_universal_var(&mut self, src_info: UniversalTyVarSourceInfo) -> UniversalTyVar {
        self.universal_vars.push(UniversalTyVarDescriptor {
            src_info,
            direct_clauses: None,
            elaboration: None,
        })
    }

    pub fn fresh_ty_universal(&mut self, src_info: UniversalTyVarSourceInfo) -> Ty {
        self.tcx()
            .intern(TyKind::UniversalVar(self.fresh_ty_universal_var(src_info)))
    }

    pub fn init_ty_universal_var_direct_clauses(
        &mut self,
        var: UniversalTyVar,
        clauses: TraitClauseList,
    ) {
        let descriptor = &mut self.universal_vars[var];

        assert!(descriptor.direct_clauses.is_none());
        descriptor.direct_clauses = Some(clauses);
    }

    pub fn lookup_universal_ty_src_info(
        &mut self,
        var: UniversalTyVar,
    ) -> UniversalTyVarSourceInfo {
        self.universal_vars[var].src_info
    }

    pub fn oblige_re_and_re(
        &mut self,
        reason: ObligationReason,
        lhs: Re,
        rhs: Re,
        mode: RelationMode,
    ) {
        self.push_obligation(reason, ObligationKind::ReAndRe(lhs, rhs, mode));
    }

    pub fn oblige_ty_and_ty(
        &mut self,
        reason: ObligationReason,
        lhs: Ty,
        rhs: Ty,
        mode: RelationMode,
    ) {
        self.push_obligation(reason, ObligationKind::TyAndTy(lhs, rhs, mode));
    }

    pub fn oblige_re_and_clauses(
        &mut self,
        reason: ObligationReason,
        lhs: Re,
        rhs: TraitClauseList,
    ) {
        let s = self.session();

        for &clause in rhs.r(s) {
            match clause {
                TraitClause::Outlives(rhs) => {
                    self.oblige_re_and_re(reason, lhs, rhs, RelationMode::LhsOntoRhs)
                }
                TraitClause::Trait(_) => {
                    unreachable!()
                }
            }
        }
    }
}

// === Importing === //

#[derive(Debug, Clone)]
pub struct ClauseImportEnv {
    pub self_ty: Ty,
    pub sig_generic_substs: Vec<GenericSubst>,
}

impl ClauseImportEnv {
    pub fn new(self_ty: Ty, sig_generic_substs: Vec<GenericSubst>) -> Self {
        Self {
            self_ty,
            sig_generic_substs,
        }
    }

    pub fn as_ref(&self) -> ClauseImportEnvRef<'_> {
        ClauseImportEnvRef {
            self_ty: self.self_ty,
            sig_generic_substs: &self.sig_generic_substs,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct ClauseImportEnvRef<'a> {
    pub self_ty: Ty,
    pub sig_generic_substs: &'a [GenericSubst],
}

impl<'a> ClauseImportEnvRef<'a> {
    pub fn new(self_ty: Ty, sig_generic_substs: &'a [GenericSubst]) -> Self {
        Self {
            self_ty,
            sig_generic_substs,
        }
    }
}

impl<'tcx> ClauseCx<'tcx> {
    pub fn importer<'a>(&'a mut self, env: ClauseImportEnvRef<'a>) -> ClauseCxImporter<'a, 'tcx> {
        ClauseCxImporter {
            ccx: self,
            env,
            hrtb_top: DebruijnTop::default(),
            hrtb_binder_ranges: FxHashMap::default(),
        }
    }

    // === Universal === //

    pub fn import_binder_list_as_universal(
        &mut self,
        self_ty: Ty,
        binders: &[Obj<GenericBinder>],
    ) -> Vec<GenericSubst> {
        self.suppress_obligation_eval(|this| {
            let substs = this.create_blank_universal_vars_from_binder_list(binders);

            this.init_universal_var_clauses_from_binder(ClauseImportEnvRef {
                self_ty,
                sig_generic_substs: &substs,
            });

            substs
        })
    }

    pub fn create_blank_universal_vars_from_binder_list(
        &mut self,
        binders: &[Obj<GenericBinder>],
    ) -> Vec<GenericSubst> {
        binders
            .iter()
            .map(|&binder| self.create_blank_universal_vars_from_binder(binder))
            .collect()
    }

    pub fn create_blank_universal_vars_from_binder(
        &mut self,
        binder: Obj<GenericBinder>,
    ) -> GenericSubst {
        let s = self.session();
        let tcx = self.tcx();

        let substs = binder
            .r(s)
            .defs
            .iter()
            .map(|&generic| match generic {
                AnyGeneric::Re(generic) => {
                    TyOrRe::Re(self.fresh_re_universal(UniversalReVarSourceInfo::Root(generic)))
                }
                AnyGeneric::Ty(generic) => {
                    TyOrRe::Ty(self.fresh_ty_universal(UniversalTyVarSourceInfo::Root(generic)))
                }
            })
            .collect::<Vec<_>>();

        let substs = tcx.intern_list(&substs);

        GenericSubst { binder, substs }
    }

    pub fn init_universal_var_clauses_from_binder(&mut self, env: ClauseImportEnvRef<'_>) {
        let s = self.session();

        for &subst in env.sig_generic_substs {
            for (&generic, &subst) in subst.binder.r(s).defs.iter().zip(subst.substs.r(s)) {
                match (generic, subst) {
                    (AnyGeneric::Re(generic), TyOrRe::Re(target)) => {
                        for &clause in generic.r(s).clauses.value.r(s) {
                            let clause = self.importer(env).fold(clause);

                            let TraitClause::Outlives(allowed_to_outlive) = clause else {
                                unreachable!()
                            };

                            self.permit_re_universal_outlives(target, allowed_to_outlive);
                        }
                    }
                    (AnyGeneric::Ty(generic), TyOrRe::Ty(target)) => {
                        let TyKind::UniversalVar(target) = *target.r(s) else {
                            unreachable!()
                        };

                        let clauses = self.importer(env).fold(generic.r(s).clauses.value);

                        self.init_ty_universal_var_direct_clauses(target, clauses);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    // === Infer === //

    pub fn import_binder_list_as_infer(
        &mut self,
        self_ty: Ty,
        binders: &[Obj<GenericBinder>],
    ) -> Vec<GenericSubst> {
        // Produce a substitution for each binder.
        let substs = self.create_blank_infer_vars_from_binder_list(binders);

        // Register clause obligations.
        self.oblige_imported_infer_binder_meets_clauses(ClauseImportEnvRef {
            self_ty,
            sig_generic_substs: &substs,
        });

        substs
    }

    pub fn create_blank_infer_vars_from_binder_list(
        &mut self,
        binders: &[Obj<GenericBinder>],
    ) -> Vec<GenericSubst> {
        binders
            .iter()
            .map(|&binder| self.create_blank_infer_vars_from_binder(binder))
            .collect()
    }

    pub fn create_blank_infer_vars_from_binder(
        &mut self,
        binder: Obj<GenericBinder>,
    ) -> GenericSubst {
        let s = self.session();
        let tcx = self.tcx();

        let substs = binder
            .r(s)
            .defs
            .iter()
            .map(|&generic| match generic {
                AnyGeneric::Re(_) => TyOrRe::Re(self.fresh_re_infer()),
                AnyGeneric::Ty(_) => TyOrRe::Ty(self.fresh_ty_infer()),
            })
            .collect::<Vec<_>>();

        let substs = tcx.intern_list(&substs);

        GenericSubst { binder, substs }
    }

    pub fn oblige_imported_infer_binder_meets_clauses(&mut self, env: ClauseImportEnvRef<'_>) {
        let s = self.session();

        for &subst in env.sig_generic_substs {
            self.oblige_wf_binder_args(
                env,
                &subst.binder.r(s).defs,
                subst.substs.r(s),
                |_this, _idx, clause| ObligationReason::GenericRequirements { clause },
            );
        }
    }

    pub fn oblige_wf_binder_args(
        &mut self,
        env: ClauseImportEnvRef<'_>,
        defs: &[AnyGeneric],
        args: &[TyOrRe],
        mut gen_reason: impl FnMut(&mut Self, usize, Span) -> ObligationReason,
    ) {
        let s = self.session();
        let tcx = self.tcx();

        for (i, (&generic, &subst)) in defs.iter().zip(args).enumerate() {
            match (generic, subst) {
                (AnyGeneric::Re(generic), TyOrRe::Re(target)) => {
                    for clause in generic.r(s).clauses.iter(tcx) {
                        let clause_span = clause.own_span();
                        let clause = self.importer(env).fold(clause.value);

                        let TraitClause::Outlives(must_outlive) = clause else {
                            unreachable!()
                        };

                        let reason = gen_reason(self, i, clause_span);

                        self.oblige_re_and_re(
                            reason,
                            target,
                            must_outlive,
                            RelationMode::LhsOntoRhs,
                        );
                    }
                }
                (AnyGeneric::Ty(generic), TyOrRe::Ty(target)) => {
                    let clauses = self.importer(env).fold_preserved(*generic.r(s).clauses);

                    for clause in clauses.iter(tcx) {
                        let reason = gen_reason(self, i, clause.own_span());

                        match clause.value {
                            TraitClause::Outlives(rhs) => {
                                self.oblige_ty_and_re(reason, target, rhs);
                            }
                            TraitClause::Trait(rhs) => {
                                self.oblige_ty_and_trait(reason, target, rhs);
                            }
                        }
                    }
                }
                _ => unreachable!(),
            }
        }
    }

    // === Specialized imports === //

    pub fn import_trait_def_env(&mut self, def: Obj<TraitItem>) -> ClauseImportEnv {
        self.suppress_obligation_eval(|this| {
            let s = this.session();
            let tcx = this.tcx();

            // Create a universal variable representing `Self`
            let self_var = this.fresh_ty_universal_var(UniversalTyVarSourceInfo::TraitSelf);
            let self_ty = tcx.intern(TyKind::UniversalVar(self_var));

            // Create universal variables for each parameter.
            let sig_generic_substs =
                this.import_binder_list_as_universal(self_ty, &[def.r(s).generics]);

            let generic_params = sig_generic_substs[0].substs;

            // Make `Self` implement the trait with these synthesized parameters.
            this.init_ty_universal_var_direct_clauses(
                self_var,
                tcx.intern_list(&[TraitClause::Trait(HrtbBinder {
                    kind: HrtbBinderKind::Imported(tcx.intern_list(&[])),
                    inner: TraitSpec {
                        def,
                        params: tcx.intern_list(
                            &generic_params
                                .r(s)
                                .iter()
                                .map(|&arg| TraitParam::Equals(arg))
                                .collect::<Vec<_>>(),
                        ),
                    },
                })]),
            );

            ClauseImportEnv::new(self_ty, sig_generic_substs)
        })
    }

    pub fn import_adt_def_env(&mut self, def: Obj<AdtItem>) -> ClauseImportEnv {
        self.suppress_obligation_eval(|this| {
            let s = this.session();
            let tcx = this.tcx();

            // Create universal parameters.
            let sig_generic_substs =
                this.create_blank_universal_vars_from_binder_list(&[def.r(s).generics]);

            // Create the `Self` type.
            let self_ty = tcx.intern(TyKind::Adt(AdtInstance {
                def,
                params: sig_generic_substs[0].substs,
            }));

            // Initialize the clauses.
            this.init_universal_var_clauses_from_binder(ClauseImportEnvRef {
                self_ty,
                sig_generic_substs: &sig_generic_substs,
            });

            ClauseImportEnv::new(self_ty, sig_generic_substs)
        })
    }

    pub fn import_impl_block_env(&mut self, def: Obj<ImplItem>) -> ClauseImportEnv {
        self.suppress_obligation_eval(|this| {
            let s = this.session();
            let tcx = this.tcx();

            // Create universal parameters.
            let sig_generic_substs =
                this.create_blank_universal_vars_from_binder_list(&[def.r(s).generics]);

            // Create the `Self` type. This type cannot contain `Self` so we give a dummy self type.
            let self_ty = this
                .importer(ClauseImportEnvRef::new(
                    tcx.intern(TyKind::SigThis),
                    &sig_generic_substs,
                ))
                .fold(def.r(s).target.value);

            // Initialize the clauses.
            this.init_universal_var_clauses_from_binder(ClauseImportEnvRef::new(
                self_ty,
                &sig_generic_substs,
            ));

            ClauseImportEnv::new(self_ty, sig_generic_substs)
        })
    }

    pub fn import_fn_item_env(&mut self, self_ty: Ty, def: Obj<FnDef>) -> Vec<GenericSubst> {
        self.import_binder_list_as_universal(self_ty, &[def.r(self.session()).generics])
    }
}

pub struct ClauseCxImporter<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    env: ClauseImportEnvRef<'a>,
    hrtb_top: DebruijnTop,
    hrtb_binder_ranges: FxHashMap<Obj<GenericBinder>, DebruijnAbsoluteRange>,
}

impl<'tcx> TyFolderPreservesSpans<'tcx> for ClauseCxImporter<'_, 'tcx> {}

impl<'tcx> ClauseCxImporter<'_, 'tcx> {
    fn lookup_generic(&self, generic: AnyGeneric) -> TyOrRe {
        let s = self.session();
        let tcx = self.tcx();

        let kind = generic.kind();
        let pos = generic.binder(s);

        if let Some(binder) = self
            .env
            .sig_generic_substs
            .iter()
            .find(|v| v.binder == pos.def)
        {
            return binder.substs.r(s)[pos.idx as usize];
        }

        if let Some(range) = self.hrtb_binder_ranges.get(&pos.def) {
            let var = HrtbDebruijn(self.hrtb_top.make_relative(range.at(pos.idx as usize)));

            return match kind {
                TyOrReKind::Re => TyOrRe::Re(Re::HrtbVar(var)),
                TyOrReKind::Ty => TyOrRe::Ty(tcx.intern(TyKind::HrtbVar(var))),
            };
        }

        panic!("no substitutions provided for signature generic {generic:?}");
    }
}

impl<'tcx> TyFolder<'tcx> for ClauseCxImporter<'_, 'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn fold_hrtb_binder<T: Copy + TyFoldable>(
        &mut self,
        binder: SpannedHrtbBinder<T>,
    ) -> Result<HrtbBinder<T>, Self::Error> {
        let s = self.session();
        let tcx = self.tcx();

        let SpannedHrtbBinderView { kind, inner } = binder.view(tcx);

        let HrtbBinderKind::Signature(binder) = kind.value else {
            unreachable!()
        };

        let binder_count = binder.r(s).defs.len();

        // Fold the inner value with a new generic binder available as an HRTB binder.
        let new_range = self.hrtb_top.move_inwards_by(binder_count);
        let old_range = self.hrtb_binder_ranges.insert(binder, new_range);

        let inner = self.fold_spanned(inner);

        match old_range {
            Some(old_range) => {
                *self.hrtb_binder_ranges.get_mut(&binder).unwrap() = old_range;
            }
            None => {
                self.hrtb_binder_ranges.remove(&binder);
            }
        }

        // Create the imported definitions.
        let defs = binder
            .r(s)
            .defs
            .iter()
            .map(|def| HrtbDebruijnDef {
                kind: def.kind(),
                clauses: self.fold_spanned(def.clauses(s)),
            })
            .collect::<Vec<_>>();

        let defs = tcx.intern_list(&defs);

        // Update the `binder_count` only after we've imported the `defs` since the definition
        // indexing scheme is relative to `binder.inner` to allow mutual recursion among generic
        // definitions.
        self.hrtb_top.move_outwards_by(binder_count);

        Ok(HrtbBinder {
            kind: HrtbBinderKind::Imported(defs),
            inner,
        })
    }

    fn fold_ty(&mut self, ty: SpannedTy) -> Result<Ty, Self::Error> {
        let s = self.session();
        let tcx = self.tcx();

        Ok(match ty.view(tcx) {
            SpannedTyView::SigThis => self.env.self_ty,
            SpannedTyView::SigInfer => self.ccx.fresh_ty_infer(),
            SpannedTyView::SigGeneric(generic) => {
                self.lookup_generic(AnyGeneric::Ty(generic)).unwrap_ty()
            }
            SpannedTyView::SigProject(projection) => {
                let SpannedTyProjectionView {
                    target,
                    spec,
                    assoc_span,
                    assoc,
                } = self.fold_preserved(projection).view(tcx);

                let assoc_infer_ty = self.ccx.fresh_ty_infer();
                let spec = {
                    let mut args = spec.value.params.r(s).to_vec();
                    args[assoc as usize] = TraitParam::Equals(TyOrRe::Ty(assoc_infer_ty));

                    TraitSpec {
                        def: spec.value.def,
                        params: tcx.intern_list(&args),
                    }
                };

                self.ccx
                    .wf_visitor()
                    .with_clause_applies_to(target.value)
                    .visit_spanned(Spanned::new_maybe_saturated(spec, assoc_span, tcx));

                self.ccx.oblige_ty_and_trait_instantiated(
                    ObligationReason::Structural,
                    target.value,
                    spec,
                );

                assoc_infer_ty
            }

            SpannedTyView::Simple(_)
            | SpannedTyView::Reference(_, _, _)
            | SpannedTyView::Adt(_)
            | SpannedTyView::Trait(_)
            | SpannedTyView::Tuple(_)
            | SpannedTyView::FnDef(_, _)
            | SpannedTyView::Error(_) => return self.super_spanned_fallible(ty),

            // These should not appear in an unimported type.
            SpannedTyView::HrtbVar(_)
            | SpannedTyView::InferVar(_)
            | SpannedTyView::UniversalVar(_) => {
                unreachable!()
            }
        })
    }

    fn fold_re(&mut self, re: SpannedRe) -> Result<Re, Self::Error> {
        Ok(match re.value {
            Re::SigInfer => self.ccx.fresh_re_infer(),
            Re::SigGeneric(generic) => self.lookup_generic(AnyGeneric::Re(generic)).unwrap_re(),
            Re::Gc | Re::Error(_) => {
                return self.super_spanned_fallible(re);
            }
            // These should not appear in an imported type.
            Re::HrtbVar(_) | Re::InferVar(_) | Re::UniversalVar(_) | Re::Erased => unreachable!(),
        })
    }
}

// === Elaboration === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn direct_ty_universal_clauses(&self, var: UniversalTyVar) -> TraitClauseList {
        self.universal_vars[var].direct_clauses.unwrap()
    }

    pub fn elaborate_ty_universal_clauses(&mut self, var: UniversalTyVar) -> UniversalElaboration {
        // See whether this universal variable has been elaborated yet.
        if let Some(elaborated) = self.universal_vars[var].elaboration {
            return elaborated;
        }

        // If not, accumulate a collection of clauses.
        let mut elaborated = Vec::new();

        let lub_re = self.fresh_re_universal(UniversalReVarSourceInfo::ElaboratedLub);

        self.elaborate_clause_and_implied(
            var,
            lub_re,
            &mut elaborated,
            self.direct_ty_universal_clauses(var),
        );

        let elaborated = UniversalElaboration {
            clauses: self.tcx().intern_list(&elaborated),
            lub_re,
        };
        self.universal_vars[var].elaboration = Some(elaborated);
        elaborated
    }

    fn elaborate_clause_and_implied(
        &mut self,
        root: UniversalTyVar,
        lub_re: Re,
        accum: &mut Vec<TraitClause>,
        target: TraitClauseList,
    ) {
        let s = self.session();

        for &target in target.r(s) {
            match target {
                TraitClause::Outlives(re) => {
                    self.permit_re_universal_outlives(lub_re, re);
                    accum.push(TraitClause::Outlives(re));
                }
                TraitClause::Trait(spec) => {
                    // // Elaborate with filled in parameters.
                    // let new_params = spec
                    //     .params
                    //     .r(s)
                    //     .iter()
                    //     .zip(&spec.def.r(s).generics.r(s).defs)
                    //     .enumerate()
                    //     .map(|(idx, (param, base))| match *param {
                    //         TraitParam::Equals(ty) => TraitParam::Equals(ty),
                    //         TraitParam::Unspecified(extra_clauses) => {
                    //             let universal = self.fresh_ty_universal_var(
                    //                 UniversalTyVarSourceInfo::Projection(root, spec, idx as u32),
                    //             );
                    //             let base = *base.as_ty().unwrap().r(s).clauses;
                    //
                    //             self.importer(self_ty, sig_generic_substs);
                    //
                    //             todo!()
                    //         }
                    //     });
                    //
                    // // Elaborate super-traits.
                    // // TODO

                    accum.push(TraitClause::Trait(spec));
                }
            }
        }
    }
}

// === Ty & Clause Relations === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn oblige_ty_and_clauses(
        &mut self,
        reason: ObligationReason,
        lhs: Ty,
        rhs: TraitClauseList,
    ) {
        let s = self.session();

        for &clause in rhs.r(s) {
            match clause {
                TraitClause::Outlives(rhs) => {
                    self.oblige_ty_and_re(reason, lhs, rhs);
                }
                TraitClause::Trait(rhs) => {
                    self.oblige_ty_and_trait(reason, lhs, rhs);
                }
            }
        }
    }

    pub fn oblige_ty_and_trait(
        &mut self,
        reason: ObligationReason,
        lhs: Ty,
        rhs: HrtbBinder<TraitSpec>,
    ) {
        let rhs = self.instantiate_hrtb_universal(rhs);
        self.oblige_ty_and_trait_instantiated(reason, lhs, rhs)
    }

    pub fn oblige_ty_and_trait_instantiated(
        &mut self,
        reason: ObligationReason,
        lhs: Ty,
        rhs: TraitSpec,
    ) {
        self.push_obligation(reason, ObligationKind::TyAndTrait(lhs, rhs));
    }

    fn run_oblige_ty_and_trait(&mut self, lhs: Ty, rhs: TraitSpec) -> ObligationResult {
        let tcx = self.tcx();
        let s = self.session();

        // See whether the type itself can provide the implementation.
        match *self.peel_ty_infer_var(lhs).r(s) {
            TyKind::Trait(clauses) => {
                todo!()
            }
            TyKind::UniversalVar(universal) => {
                match self
                    .clone()
                    .try_select_inherent_impl(self.elaborate_ty_universal_clauses(universal), rhs)
                {
                    Ok(res) => {
                        return res.into_obligation_res(self);
                    }
                    Err(SelectionRejected) => {
                        // (fallthrough)
                    }
                }
            }
            TyKind::InferVar(_) => {
                // We can't yet rule out the possibility that this obligation is inherently
                // fulfilled.
                return ObligationResult::NotReady;
            }
            TyKind::Error(_) => {
                // Error types can do anything.
                return ObligationResult::Success;
            }
            TyKind::SigThis
            | TyKind::SigInfer
            | TyKind::SigGeneric(_)
            | TyKind::SigProject(_)
            // LHS HRTBs should have been instantiated right before the obligation.
            | TyKind::HrtbVar(_) => {
                unreachable!()
            }
            TyKind::Simple(_)
            | TyKind::Reference(_, _, _)
            | TyKind::Adt(_)
            | TyKind::Tuple(_)
            | TyKind::FnDef(_, _) => {
                // (the `impl` must come externally, fallthrough)
            }
        }

        // Otherwise, scan for a suitable `impl`.
        let mut prev_confirmation = None;

        let candidates = self.coherence.gather_impl_candidates(
            tcx,
            self.ucx()
                .substitutor(UnboundVarHandlingMode::EraseToSigInfer)
                .fold(lhs),
            self.ucx()
                .substitutor(UnboundVarHandlingMode::EraseToSigInfer)
                .fold(rhs),
        );

        for candidate in candidates {
            let Ok(confirmation) = self.clone().try_select_block_impl(lhs, candidate, rhs) else {
                continue;
            };

            if prev_confirmation.is_some() {
                return ObligationResult::NotReady;
            }

            prev_confirmation = Some(confirmation)
        }

        let Some(confirmation) = prev_confirmation else {
            return ObligationResult::Failure(Diag::anon_err(format_args!(
                "failed to prove {:?} implements {:?}",
                self.ucx()
                    .substitutor(UnboundVarHandlingMode::NormalizeToRoot)
                    .fold(lhs),
                self.ucx()
                    .substitutor(UnboundVarHandlingMode::NormalizeToRoot)
                    .fold(rhs),
            )));
        };

        confirmation.into_obligation_res(self)
    }

    fn try_select_inherent_impl(
        mut self,
        lhs: UniversalElaboration,
        rhs: TraitSpec,
    ) -> SelectionResult<Self> {
        let s = self.session();

        // Find the clause that could prove our trait.
        let lhs = lhs
            .clauses
            .r(s)
            .iter()
            .copied()
            .find(|&clause| match clause {
                TraitClause::Outlives(_) => false,
                TraitClause::Trait(lhs) => lhs.inner.def == rhs.def,
            });

        let Some(lhs) = lhs else {
            return Err(SelectionRejected);
        };

        let TraitClause::Trait(lhs) = lhs else {
            unreachable!()
        };

        // Instantiate the binder with inference variables so that we may select the correct
        // implementation of it.
        let lhs = self.instantiate_hrtb_infer(lhs);

        // See whether we can select an inherent `impl`.
        let mut param_iter = lhs.params.r(s).iter().zip(rhs.params.r(s));

        for (&lhs_param, &rhs_param) in
            (&mut param_iter).take(rhs.def.r(s).regular_generic_count as usize)
        {
            let TraitParam::Equals(lhs) = lhs_param else {
                unreachable!();
            };

            match rhs_param {
                TraitParam::Equals(rhs) => match (lhs, rhs) {
                    (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                        // This can be an obligation because selection shouldn't depend on regions.
                        self.oblige_re_and_re(
                            ObligationReason::Structural,
                            lhs,
                            rhs,
                            RelationMode::Equate,
                        );
                    }
                    (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                        if let Err(_err) =
                            self.ucx_mut()
                                .unify_ty_and_ty(lhs, rhs, RelationMode::Equate)
                        {
                            return Err(SelectionRejected);
                        }
                    }
                    _ => unreachable!(),
                },
                TraitParam::Unspecified(_) => {
                    unreachable!()
                }
            }
        }

        // If we can, push its obligations.
        for (&lhs_param, &rhs_param) in param_iter {
            let TraitParam::Equals(lhs) = lhs_param else {
                unreachable!();
            };

            match rhs_param {
                TraitParam::Equals(rhs) => match (lhs, rhs) {
                    (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                        self.oblige_re_and_re(
                            ObligationReason::Structural,
                            lhs,
                            rhs,
                            RelationMode::Equate,
                        );
                    }
                    (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                        self.oblige_ty_and_ty(
                            ObligationReason::Structural,
                            lhs,
                            rhs,
                            RelationMode::Equate,
                        );
                    }
                    _ => unreachable!(),
                },
                TraitParam::Unspecified(rhs) => match lhs {
                    TyOrRe::Re(lhs) => {
                        self.oblige_re_and_clauses(ObligationReason::Structural, lhs, rhs);
                    }
                    TyOrRe::Ty(lhs) => {
                        self.oblige_ty_and_clauses(ObligationReason::Structural, lhs, rhs);
                    }
                },
            }
        }

        Ok(ConfirmationResult::Success(self))
    }

    fn try_select_block_impl(
        mut self,
        lhs: Ty,
        rhs: Obj<ImplItem>,
        spec: TraitSpec,
    ) -> SelectionResult<Self> {
        let s = self.session();

        // Obtain inference variables for all generics in the `impl` and tentatively create
        // obligations for them.
        let trait_substs = self.import_binder_list_as_infer(lhs, &[rhs.r(s).generics]);

        // Import the target type and trait. WF obligations are not needed on these types because
        // the `impl` itself has been WF-checked for all types compatible with the generic
        // parameters.
        let target_ty = self
            .importer(ClauseImportEnvRef::new(lhs, &trait_substs))
            .fold_spanned(rhs.r(s).target);

        let target_trait = self
            .importer(ClauseImportEnvRef::new(lhs, &trait_substs))
            .fold_spanned(rhs.r(s).trait_.unwrap());

        // Does the `lhs` type match the `rhs`'s target type?
        if self
            .ucx_mut()
            .unify_ty_and_ty(lhs, target_ty, RelationMode::Equate)
            .is_err()
        {
            return Err(SelectionRejected);
        }

        // See whether our RHS trait's generic parameters can be satisfied by this `impl`.
        debug_assert_eq!(target_trait.def, spec.def);

        for (&instance, &required_param) in target_trait
            .params
            .r(s)
            .iter()
            .zip(spec.params.r(s))
            .take(spec.def.r(s).regular_generic_count as usize)
        {
            match required_param {
                TraitParam::Equals(required) => match (instance, required) {
                    (TyOrRe::Re(instance), TyOrRe::Re(required)) => {
                        if self
                            .ucx_mut()
                            .unify_re_and_re(instance, required, RelationMode::Equate)
                            .is_err()
                        {
                            return Err(SelectionRejected);
                        }
                    }
                    (TyOrRe::Ty(instance), TyOrRe::Ty(required)) => {
                        if self
                            .ucx_mut()
                            .unify_ty_and_ty(instance, required, RelationMode::Equate)
                            .is_err()
                        {
                            return Err(SelectionRejected);
                        }
                    }
                    _ => unreachable!(),
                },
                TraitParam::Unspecified(_) => {
                    unreachable!()
                }
            }
        }

        // Register obligations for associated types.
        for (&instance_ty, &required_param) in target_trait
            .params
            .r(s)
            .iter()
            .zip(spec.params.r(s))
            .skip(spec.def.r(s).regular_generic_count as usize)
        {
            // Associated types are never regions.
            let instance_ty = instance_ty.unwrap_ty();

            match required_param {
                TraitParam::Equals(required_ty) => {
                    let TyOrRe::Ty(required_ty) = required_ty else {
                        unreachable!()
                    };

                    self.oblige_ty_and_ty(
                        ObligationReason::Structural,
                        instance_ty,
                        required_ty,
                        RelationMode::Equate,
                    );
                }
                TraitParam::Unspecified(additional_clauses) => {
                    self.oblige_ty_and_clauses(
                        ObligationReason::Structural,
                        instance_ty,
                        additional_clauses,
                    );
                }
            }
        }

        Ok(ConfirmationResult::Success(self))
    }
}

// === HRTB instantiation === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn instantiate_hrtb_universal(&mut self, binder: HrtbBinder<TraitSpec>) -> TraitSpec {
        let tcx = self.tcx();
        let s = self.session();

        let HrtbBinderKind::Imported(defs) = binder.kind else {
            unreachable!();
        };

        // Fast path :)
        if defs.r(s).is_empty() {
            return binder.inner;
        }

        self.suppress_obligation_eval(|this| {
            // Make up new universal variables for our binder.
            let vars = defs
                .r(s)
                .iter()
                .map(|def| match def.kind {
                    TyOrReKind::Re => {
                        TyOrRe::Re(this.fresh_re_universal(UniversalReVarSourceInfo::HrtbVar))
                    }
                    TyOrReKind::Ty => {
                        TyOrRe::Ty(this.fresh_ty_universal(UniversalTyVarSourceInfo::HrtbVar))
                    }
                })
                .collect::<Vec<_>>();

            let vars = tcx.intern_list(&vars);

            // Initialize their clauses.
            for (&def, &var) in defs.r(s).iter().zip(vars.r(s)) {
                match var {
                    TyOrRe::Re(var) => {
                        let clauses = HrtbSubstitutionFolder::new(this, vars, s).fold(def.clauses);

                        for clause in clauses.r(s) {
                            let TraitClause::Outlives(re) = *clause else {
                                unreachable!();
                            };

                            this.permit_re_universal_outlives(var, re);
                        }
                    }
                    TyOrRe::Ty(var) => {
                        let TyKind::UniversalVar(var) = *var.r(s) else {
                            unreachable!()
                        };

                        let clauses = HrtbSubstitutionFolder::new(this, vars, s).fold(def.clauses);

                        this.init_ty_universal_var_direct_clauses(var, clauses);
                    }
                }
            }

            // Fold the inner type
            HrtbSubstitutionFolder::new(this, vars, s).fold(binder.inner)
        })
    }

    pub fn instantiate_hrtb_infer(&mut self, binder: HrtbBinder<TraitSpec>) -> TraitSpec {
        let tcx = self.tcx();
        let s = self.session();

        let HrtbBinderKind::Imported(defs) = binder.kind else {
            unreachable!();
        };

        // Fast path :)
        if defs.r(s).is_empty() {
            return binder.inner;
        }

        self.suppress_obligation_eval(|this| {
            // Make up new inference variables for our binder.
            let vars = defs
                .r(s)
                .iter()
                .map(|def| match def.kind {
                    TyOrReKind::Re => TyOrRe::Re(this.fresh_re_infer()),
                    TyOrReKind::Ty => TyOrRe::Ty(this.fresh_ty_infer()),
                })
                .collect::<Vec<_>>();

            let vars = tcx.intern_list(&vars);

            // Constrain the new inference variables with their obligations.
            for (&def, &var) in defs.r(s).iter().zip(vars.r(s)) {
                match var {
                    TyOrRe::Re(var) => {
                        let clauses = HrtbSubstitutionFolder::new(this, vars, s).fold(def.clauses);

                        this.oblige_re_and_clauses(ObligationReason::Structural, var, clauses);
                    }
                    TyOrRe::Ty(var) => {
                        let clauses = HrtbSubstitutionFolder::new(this, vars, s).fold(def.clauses);

                        this.oblige_ty_and_clauses(ObligationReason::Structural, var, clauses);
                    }
                }
            }

            // Fold the inner type
            HrtbSubstitutionFolder::new(this, vars, s).fold(binder.inner)
        })
    }
}

pub struct HrtbSubstitutionFolder<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    replace_with: TyOrReList,
    top: DebruijnTop,
}

impl<'a, 'tcx> HrtbSubstitutionFolder<'a, 'tcx> {
    pub fn new(ccx: &'a mut ClauseCx<'tcx>, replace_with: TyOrReList, s: &Session) -> Self {
        Self {
            ccx,
            replace_with,
            top: DebruijnTop::new(replace_with.r(s).len()),
        }
    }
}

impl<'tcx> TyFolder<'tcx> for HrtbSubstitutionFolder<'_, 'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn fold_hrtb_binder<T: Copy + TyFoldable>(
        &mut self,
        binder: SpannedHrtbBinder<T>,
    ) -> Result<HrtbBinder<T>, Self::Error> {
        let s = self.session();
        let binder = binder.value;

        let HrtbBinderKind::Imported(defs) = binder.kind else {
            unreachable!();
        };

        let bind_count = defs.r(s).len();

        self.top.move_inwards_by(bind_count);
        let inner = self.super_(binder.inner);
        self.top.move_outwards_by(bind_count);

        Ok(HrtbBinder {
            kind: binder.kind,
            inner,
        })
    }

    fn fold_ty(&mut self, ty: SpannedTy) -> Result<Ty, Self::Error> {
        let s = self.session();
        let ty = ty.value;

        if let TyKind::HrtbVar(var) = *ty.r(s) {
            let abs = self.top.lookup_relative(var.0).index();

            if abs < self.replace_with.r(s).len() {
                return Ok(self.replace_with.r(s)[abs].unwrap_ty());
            }
        }

        Ok(self.super_(ty))
    }

    fn fold_re(&mut self, re: SpannedRe) -> Result<Re, Self::Error> {
        let s = self.session();
        let re = re.value;

        if let Re::HrtbVar(var) = re {
            let abs = self.top.lookup_relative(var.0).index();

            if abs < self.replace_with.r(s).len() {
                return Ok(self.replace_with.r(s)[abs].unwrap_re());
            }
        }

        Ok(self.super_(re))
    }
}

// === Ty & Re Relations === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn oblige_ty_and_re(&mut self, reason: ObligationReason, lhs: Ty, rhs: Re) {
        self.push_obligation(reason, ObligationKind::TyAndRe(lhs, rhs));
    }

    fn run_oblige_ty_and_re(&mut self, lhs: Ty, rhs: Re) -> ObligationResult {
        let s = self.session();

        match *lhs.r(s) {
            TyKind::SigThis
            | TyKind::SigInfer
            | TyKind::SigGeneric(_)
            | TyKind::SigProject(_)
            | TyKind::HrtbVar(_) => {
                unreachable!()
            }
            TyKind::FnDef(_, _) | TyKind::Simple(_) | TyKind::Error(_) => {
                // (trivial)
            }
            TyKind::Reference(lhs, _muta, _pointee) => {
                // No need to unify the pointee since WF checks already ensure that it outlives
                // `lhs`.
                if let Err(err) = self
                    .ucx_mut()
                    .unify_re_and_re(lhs, rhs, RelationMode::LhsOntoRhs)
                {
                    return ObligationResult::Failure(err.to_diag());
                }
            }
            TyKind::Adt(lhs) => {
                // ADTs are bounded by which regions they mention.
                for &lhs in lhs.params.r(s) {
                    match lhs {
                        TyOrRe::Re(lhs) => {
                            if let Err(err) =
                                self.ucx_mut()
                                    .unify_re_and_re(lhs, rhs, RelationMode::LhsOntoRhs)
                            {
                                return ObligationResult::Failure(err.to_diag());
                            }
                        }
                        TyOrRe::Ty(lhs) => {
                            self.oblige_ty_and_re(ObligationReason::Structural, lhs, rhs);
                        }
                    }
                }
            }
            TyKind::Trait(lhs) => {
                for &lhs in lhs.r(s) {
                    match lhs {
                        TraitClause::Outlives(lhs) => {
                            // There is guaranteed to be exactly one outlives constraint for a trait
                            // object so relating these constraints is sufficient to ensure that the
                            // object outlives the `rhs`.
                            if let Err(err) =
                                self.ucx_mut()
                                    .unify_re_and_re(lhs, rhs, RelationMode::LhsOntoRhs)
                            {
                                return ObligationResult::Failure(err.to_diag());
                            }
                        }
                        TraitClause::Trait(_) => {
                            // (if the outlives constraint says the trait is okay, it's okay)
                        }
                    }
                }
            }
            TyKind::Tuple(lhs) => {
                for &lhs in lhs.r(s) {
                    self.oblige_ty_and_re(ObligationReason::Structural, lhs, rhs);
                }
            }
            TyKind::UniversalVar(var) => {
                let lub_re = self.elaborate_ty_universal_clauses(var).lub_re;

                self.oblige_re_and_re(
                    ObligationReason::Structural,
                    lub_re,
                    rhs,
                    RelationMode::LhsOntoRhs,
                );
            }
            TyKind::InferVar(inf_lhs) => {
                if let Ok(inf_lhs) = self.lookup_ty_infer_var(inf_lhs) {
                    self.oblige_ty_and_re(ObligationReason::Structural, inf_lhs, rhs);
                } else {
                    return ObligationResult::NotReady;
                }
            }
        }

        ObligationResult::Success
    }
}

// === WF Relations === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn wf_visitor(&mut self) -> ClauseTyWfVisitor<'_, 'tcx> {
        ClauseTyWfVisitor {
            ccx: self,
            clause_applies_to: None,
        }
    }

    pub fn oblige_ty_wf(&mut self, reason: ObligationReason, ty: Ty) {
        self.push_obligation(reason, ObligationKind::TyWf(ty));
    }

    pub fn run_oblige_ty_wf(&mut self, ty: Ty) -> ObligationResult {
        let ty = self.peel_ty_infer_var(ty);

        if matches!(ty.r(self.session()), TyKind::InferVar(_)) {
            return ObligationResult::NotReady;
        }

        self.wf_visitor().visit(ty);

        ObligationResult::Success
    }
}

pub struct ClauseTyWfVisitor<'a, 'tcx> {
    pub ccx: &'a mut ClauseCx<'tcx>,
    pub clause_applies_to: Option<Ty>,
}

impl ClauseTyWfVisitor<'_, '_> {
    pub fn with_clause_applies_to(mut self, ty: Ty) -> Self {
        self.clause_applies_to = Some(ty);
        self
    }
}

impl<'tcx> TyVisitor<'tcx> for ClauseTyWfVisitor<'_, 'tcx> {
    type Break = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn visit_ty(&mut self, ty: SpannedTy) -> ControlFlow<Self::Break> {
        match ty.view(self.tcx()) {
            SpannedTyView::Trait(_) => {
                let old_clause_applies_to = self.clause_applies_to.replace(ty.value);
                self.walk_spanned(ty);
                self.clause_applies_to = old_clause_applies_to;
            }
            SpannedTyView::Reference(re, _muta, pointee) => {
                self.ccx
                    .oblige_ty_and_re(ObligationReason::Structural, pointee.value, re.value);

                self.walk_spanned(ty);
            }
            SpannedTyView::FnDef(..) => {
                todo!()
            }
            SpannedTyView::Simple(_)
            | SpannedTyView::Adt(_)
            | SpannedTyView::Tuple(_)
            | SpannedTyView::UniversalVar(_)
            | SpannedTyView::HrtbVar(_)
            | SpannedTyView::Error(_) => {
                self.walk_spanned(ty);
            }
            SpannedTyView::InferVar(_) => {
                self.ccx
                    .oblige_ty_wf(ObligationReason::WfDeferred(ty.own_span()), ty.value);
            }
            SpannedTyView::SigThis
            | SpannedTyView::SigInfer
            | SpannedTyView::SigGeneric(_)
            | SpannedTyView::SigProject(_) => {
                unreachable!()
            }
        }

        ControlFlow::Continue(())
    }

    fn visit_trait_spec(&mut self, spec: SpannedTraitSpec) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        let params = spec
            .view(tcx)
            .params
            .iter(tcx)
            .map(|param| match param.view(tcx) {
                SpannedTraitParamView::Equals(v) => v,
                SpannedTraitParamView::Unspecified(_) => {
                    SpannedTyOrRe::new_unspanned(TyOrRe::Ty(self.ccx.fresh_ty_infer()))
                }
            })
            .collect::<Vec<_>>();

        let params = SpannedTyOrReList::alloc_list(spec.own_span(), &params, tcx);

        // Just like in `rustc`, we never produce obligations on the associated types since, if an
        // `impl` is found, we just rely on the fact that `impl` WF checks already validated the
        // type for its clauses and ensure that our `impl` matches what the trait spec said it would
        // contain.
        self.check_generics(
            spec.value.def.r(s).generics,
            params,
            Some(spec.value.def.r(s).regular_generic_count),
        );

        self.walk_spanned(spec);

        ControlFlow::Continue(())
    }

    fn visit_trait_instance(&mut self, instance: SpannedTraitInstance) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        self.check_generics(
            instance.value.def.r(s).generics,
            instance.view(tcx).params,
            None,
        );
        self.walk_spanned(instance);

        ControlFlow::Continue(())
    }

    fn visit_adt_instance(&mut self, instance: SpannedAdtInstance) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        // Check generics
        let old_clause_applies_to = self
            .clause_applies_to
            .replace(tcx.intern(TyKind::Adt(instance.value)));

        self.check_generics(
            instance.value.def.r(s).generics,
            instance.view(tcx).params,
            None,
        );

        self.clause_applies_to = old_clause_applies_to;

        // Ensure parameter types are also well-formed.
        self.walk_spanned(instance);

        ControlFlow::Continue(())
    }
}

impl ClauseTyWfVisitor<'_, '_> {
    fn check_generics(
        &mut self,
        binder: Obj<GenericBinder>,
        all_params: SpannedTyOrReList,
        validate_count: Option<u32>,
    ) {
        let s = self.session();
        let tcx = self.tcx();

        let defs = &binder.r(s).defs[..];
        let defs = match validate_count {
            Some(limit) => &defs[..limit as usize],
            None => defs,
        };

        let validated_params = all_params.value.r(s);
        let validated_params = match validate_count {
            Some(limit) => &validated_params[..limit as usize],
            None => validated_params,
        };

        self.ccx.oblige_wf_binder_args(
            ClauseImportEnvRef::new(
                self.clause_applies_to.unwrap(),
                &[GenericSubst {
                    binder,
                    substs: all_params.value,
                }],
            ),
            defs,
            validated_params,
            |_, param_idx, clause_span| ObligationReason::WfForGenericParam {
                use_span: all_params.nth(param_idx, tcx).own_span(),
                clause_span,
            },
        );
    }
}
