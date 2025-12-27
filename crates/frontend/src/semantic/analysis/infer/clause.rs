use crate::{
    base::{Diag, Session, arena::Obj},
    semantic::{
        analysis::{
            BinderSubstitution, CoherenceMap, ConfirmationResult, FloatingInferVar, ObligationCx,
            ObligationKind, ObligationReason, ObligationResult, SelectionRejected, SelectionResult,
            SubstitutionFolder, TyCtxt, TyFolder, TyFolderInfallible as _,
            TyFolderInfalliblePreservesSpans as _, TyFolderPreservesSpans, TyFolderSuper,
            TyVisitor, TyVisitorUnspanned, TyVisitorWalk, UnboundVarHandlingMode, UnifyCx,
            UnifyCxMode,
        },
        syntax::{
            AnyGeneric, GenericBinder, ImplItem, InferTyVar, ListOfTraitClauseList, Re,
            RelationMode, SpannedAdtInstance, SpannedTraitInstance, SpannedTraitParamView,
            SpannedTraitSpec, SpannedTy, SpannedTyOrRe, SpannedTyOrReList, SpannedTyOrReView,
            SpannedTyView, TraitClause, TraitClauseList, TraitParam, TraitSpec, Ty, TyKind, TyOrRe,
            TyOrReList,
        },
    },
};
use std::{convert::Infallible, ops::ControlFlow};

// === ClauseCx Core === //

/// A type inference context for solving type obligations of the form...
///
/// - `Region: Region`
/// - `Type = Type`
/// - `Type: Clauses`
/// - `Clauses entail Clauses`
/// - `is-well-formed Type`
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
///
/// ## Well-formedness checks
///
/// There are two types of well-formedness requirements a type may have...
///
/// - A type WF requirement where a generic parameter must implement a trait (e.g. if `Foo<T>` has a
///   clause stipulating that `T: MyTrait`)
///
/// - A region WF constraint where a lifetime must outlive another lifetime (e.g. `&'a T` would
///   imply that `T: 'a`).
///
/// Relational methods never check type WF requirements or push region WF constraints by
/// themselves but will never crash if these WF requirements aren't met. You can "bolt on" these WF
/// requirements at the end of a region-aware inference session by calling `wf_ty` on all the types
/// the programmer has created.
#[derive(Clone)]
pub struct ClauseCx<'tcx> {
    ocx: ObligationCx<'tcx>,
    coherence: &'tcx CoherenceMap,
}

impl<'tcx> ClauseCx<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, coherence: &'tcx CoherenceMap, mode: UnifyCxMode) -> Self {
        Self {
            ocx: ObligationCx::new(tcx, mode),
            coherence,
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
        self.ocx.push_obligation_no_poll(reason, kind);
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

// Forwards
impl<'tcx> ClauseCx<'tcx> {
    pub fn instantiator(&mut self, self_ty: Ty) -> ClauseTyInstantiator<'_, 'tcx> {
        ClauseTyInstantiator { ccx: self, self_ty }
    }

    pub fn mode(&self) -> UnifyCxMode {
        self.ucx().mode()
    }

    pub fn fresh_ty_var(&mut self) -> InferTyVar {
        self.ucx_mut().fresh_ty_var()
    }

    pub fn fresh_ty(&mut self) -> Ty {
        self.ucx_mut().fresh_ty()
    }

    pub fn lookup_ty_var(&self, var: InferTyVar) -> Result<Ty, FloatingInferVar<'_>> {
        self.ucx().lookup_ty_var(var)
    }

    pub fn peel_ty_var(&self, ty: Ty) -> Ty {
        self.ucx().peel_ty_var(ty)
    }

    pub fn fresh_re(&mut self) -> Re {
        self.ucx_mut().fresh_re()
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

    pub fn oblige_re_and_clause(
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

// === Ty & Clause Relations === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
struct ImplFreshInfer {
    target: Ty,
    trait_: TyOrReList,
    impl_generics: TyOrReList,
    impl_generic_clauses: ListOfTraitClauseList,
}

impl<'tcx> ClauseCx<'tcx> {
    pub fn oblige_ty_and_clause(
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

    pub fn oblige_ty_and_trait(&mut self, reason: ObligationReason, lhs: Ty, rhs: TraitSpec) {
        self.push_obligation(reason, ObligationKind::TyAndTrait(lhs, rhs));
    }

    fn run_oblige_ty_and_trait(&mut self, lhs: Ty, rhs: TraitSpec) -> ObligationResult {
        let tcx = self.tcx();
        let s = self.session();

        // See whether the type itself can provide the implementation.
        match *self.peel_ty_var(lhs).r(s) {
            TyKind::Trait(clauses) => {
                todo!()
            }
            TyKind::Universal(generic) => {
                match self
                    .clone()
                    .try_select_inherent_impl(tcx.elaborate_generic_clauses(generic, None), rhs)
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
            TyKind::This | TyKind::ExplicitInfer => unreachable!(),
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
                .substitutor(UnboundVarHandlingMode::EraseToExplicitInfer)
                .fold_ty(lhs),
            self.ucx()
                .substitutor(UnboundVarHandlingMode::EraseToExplicitInfer)
                .fold_trait_spec(rhs),
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
                    .fold_ty(lhs),
                self.ucx()
                    .substitutor(UnboundVarHandlingMode::NormalizeToRoot)
                    .fold_trait_spec(rhs),
            )));
        };

        confirmation.into_obligation_res(self)
    }

    fn try_select_inherent_impl(
        mut self,
        lhs_elaborated: TraitClauseList,
        rhs: TraitSpec,
    ) -> SelectionResult<Self> {
        let s = self.session();

        // Find the clause that could prove our trait.
        let lhs = lhs_elaborated
            .r(s)
            .iter()
            .copied()
            .find(|&clause| match clause {
                TraitClause::Outlives(_) => false,
                TraitClause::Trait(lhs) => lhs.def == rhs.def,
            });

        let Some(lhs) = lhs else {
            return Err(SelectionRejected);
        };

        let TraitClause::Trait(lhs) = lhs else {
            unreachable!()
        };

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
                        self.oblige_re_and_clause(ObligationReason::Structural, lhs, rhs);
                    }
                    TyOrRe::Ty(lhs) => {
                        self.oblige_ty_and_clause(ObligationReason::Structural, lhs, rhs);
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
        let tcx = self.tcx();
        let s = self.session();

        // Replace universal qualifications in `impl` with inference variables
        let rhs_fresh = self.instantiate_fresh_impl_vars(rhs);

        // Does the `lhs` type match the `rhs`'s target type?
        if self
            .ucx_mut()
            .unify_ty_and_ty(lhs, rhs_fresh.target, RelationMode::Equate)
            .is_err()
        {
            return Err(SelectionRejected);
        }

        // See whether our RHS trait's generic parameters can be satisfied by this `impl`.
        for (&instance, &required_param) in rhs_fresh
            .trait_
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

        // Obtain all required sub-obligations from generic parameters on the `impl`.
        for &infer_step in rhs.r(s).optimal_solve_order.iter() {
            let var = rhs_fresh.impl_generics.r(s)[infer_step.generic_idx as usize];
            let clause = rhs_fresh.impl_generic_clauses.r(s)[infer_step.generic_idx as usize].r(s)
                [infer_step.clause_idx as usize];

            let clause = tcx.intern_trait_clause_list(&[clause]);

            match var {
                TyOrRe::Re(re) => {
                    self.oblige_re_and_clause(ObligationReason::Structural, re, clause);
                }
                TyOrRe::Ty(ty) => {
                    self.oblige_ty_and_clause(ObligationReason::ImplConstraint, ty, clause);
                }
            }
        }

        // See whether the user-supplied associated type constraints match what we inferred.
        for (&instance_ty, &required_param) in rhs_fresh
            .trait_
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
                    self.oblige_ty_and_clause(
                        ObligationReason::Structural,
                        instance_ty,
                        additional_clauses,
                    );
                }
            }
        }

        Ok(ConfirmationResult::Success(self))
    }

    fn instantiate_fresh_impl_vars(&mut self, candidate: Obj<ImplItem>) -> ImplFreshInfer {
        let tcx = self.tcx();
        let s = self.session();

        // Define fresh variables describing the substitutions to be made.
        let binder = candidate.r(s).generics;
        let impl_generics = binder
            .r(s)
            .defs
            .iter()
            .map(|generic| match generic {
                AnyGeneric::Re(_) => TyOrRe::Re(self.fresh_re()),
                AnyGeneric::Ty(_) => TyOrRe::Ty(self.fresh_ty()),
            })
            .collect::<Vec<_>>();

        let impl_generics = tcx.intern_ty_or_re_list(&impl_generics);
        let substs = BinderSubstitution {
            binder,
            substs: impl_generics,
        };

        // Substitute the target type
        let target = SubstitutionFolder::new(tcx, tcx.intern_ty(TyKind::This), Some(substs))
            .fold_ty(candidate.r(s).target.value);

        // Substitute inference clauses
        let inf_var_clauses = binder
            .r(s)
            .defs
            .iter()
            .map(|generic| {
                let clauses = match generic {
                    AnyGeneric::Re(generic) => generic.r(s).clauses.value,
                    AnyGeneric::Ty(generic) => generic.r(s).user_clauses.value,
                };

                SubstitutionFolder::new(tcx, target, Some(substs)).fold_clause_list(clauses)
            })
            .collect::<Vec<_>>();

        let impl_generic_clauses = tcx.intern_list_of_trait_clause_list(&inf_var_clauses);

        let trait_ = SubstitutionFolder::new(tcx, target, Some(substs))
            .fold_ty_or_re_list(candidate.r(s).trait_.unwrap().value.params);

        ImplFreshInfer {
            target,
            trait_,
            impl_generics,
            impl_generic_clauses,
        }
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
            TyKind::This | TyKind::ExplicitInfer => unreachable!(),
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
            TyKind::Universal(_) => todo!(),
            TyKind::InferVar(inf_lhs) => {
                if let Ok(inf_lhs) = self.lookup_ty_var(inf_lhs) {
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
        // TODO: Wait for inference resolution and perform coinductivity checks to break WF cycles

        ControlFlow::Continue(()) = self.wf_visitor().visit_ty(ty);

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

    fn visit_spanned_ty(&mut self, ty: SpannedTy) -> ControlFlow<Self::Break> {
        match ty.view(self.tcx()) {
            SpannedTyView::Trait(_) => {
                let old_clause_applies_to = self.clause_applies_to.replace(ty.value);
                self.walk_ty(ty)?;
                self.clause_applies_to = old_clause_applies_to;
            }
            SpannedTyView::Reference(re, _muta, pointee) => {
                self.ccx.oblige_ty_and_re(
                    ObligationReason::WfForReference(pointee.own_span()),
                    pointee.value,
                    re.value,
                );

                self.walk_ty(ty)?;
            }
            SpannedTyView::FnDef(..) => {
                todo!()
            }
            SpannedTyView::This
            | SpannedTyView::Simple(_)
            | SpannedTyView::Adt(_)
            | SpannedTyView::Tuple(_)
            | SpannedTyView::ExplicitInfer
            | SpannedTyView::Universal(_)
            | SpannedTyView::InferVar(_)
            | SpannedTyView::Error(_) => {
                self.walk_ty(ty)?;
            }
        }

        ControlFlow::Continue(())
    }

    fn visit_spanned_trait_spec(&mut self, spec: SpannedTraitSpec) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        let params = spec
            .view(tcx)
            .params
            .iter(tcx)
            .map(|param| match param.view(tcx) {
                SpannedTraitParamView::Equals(v) => v,
                SpannedTraitParamView::Unspecified(_) => {
                    SpannedTyOrRe::new_unspanned(TyOrRe::Ty(self.ccx.fresh_ty()))
                }
            })
            .collect::<Vec<_>>();

        let params = SpannedTyOrReList::alloc_list(spec.own_span(), &params, tcx);

        self.check_generics(spec.value.def.r(s).generics, params);

        self.walk_trait_spec(spec)?;

        ControlFlow::Continue(())
    }

    fn visit_spanned_trait_instance(
        &mut self,
        instance: SpannedTraitInstance,
    ) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        self.check_generics(instance.value.def.r(s).generics, instance.view(tcx).params);
        self.walk_trait_instance(instance)?;

        ControlFlow::Continue(())
    }

    fn visit_spanned_adt_instance(
        &mut self,
        instance: SpannedAdtInstance,
    ) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        // Check generics
        let old_clause_applies_to = self
            .clause_applies_to
            .replace(tcx.intern_ty(TyKind::Adt(instance.value)));

        self.check_generics(instance.value.def.r(s).generics, instance.view(tcx).params);

        self.clause_applies_to = old_clause_applies_to;

        // Ensure parameter types are also well-formed.
        self.walk_adt_instance(instance)?;

        ControlFlow::Continue(())
    }
}

impl ClauseTyWfVisitor<'_, '_> {
    fn check_generics(&mut self, binder: Obj<GenericBinder>, params: SpannedTyOrReList) {
        let tcx = self.tcx();
        let s = self.session();

        // Create a folder to replace generics in the trait with the user's supplied generics.
        let mut trait_subst = SubstitutionFolder {
            tcx,
            self_ty: self.clause_applies_to.unwrap(),
            substitution: Some(BinderSubstitution {
                binder,
                substs: params.value,
            }),
        };

        for (actual, requirements) in params.iter(tcx).zip(&binder.r(s).defs) {
            match (actual.view(tcx), requirements) {
                (SpannedTyOrReView::Re(actual), AnyGeneric::Re(requirements)) => {
                    let requirements =
                        trait_subst.fold_spanned_clause_list(*requirements.r(s).clauses);

                    self.ccx.oblige_re_and_clause(
                        ObligationReason::WfForTraitParam {
                            use_site: actual.own_span(),
                            obligation_site: requirements.own_span(),
                        },
                        actual.value,
                        requirements.value,
                    );
                }
                (SpannedTyOrReView::Ty(actual), AnyGeneric::Ty(requirements)) => {
                    let requirements =
                        trait_subst.fold_spanned_clause_list(*requirements.r(s).user_clauses);

                    self.ccx.oblige_ty_and_clause(
                        ObligationReason::WfForTraitParam {
                            use_site: actual.own_span(),
                            obligation_site: requirements.own_span(),
                        },
                        actual.value,
                        requirements.value,
                    );
                }
                _ => unreachable!(),
            }
        }
    }
}

// === Type Instantiation === //

/// A type folder which instantiates a user-written type to be compatible with a [`ClauseCx`].
///
/// It...
///
/// - Replaces `Self` types.
/// - Instantiates `ExplicitInfer` types.
///
/// Once a user's type is instantiated, it can be safely used inside a `ClauseCx`. All types
/// used internally by a `ClauseCx` are naturally normalized.
pub struct ClauseTyInstantiator<'a, 'tcx> {
    pub ccx: &'a mut ClauseCx<'tcx>,
    pub self_ty: Ty,
}

impl<'tcx> TyFolderPreservesSpans<'tcx> for ClauseTyInstantiator<'_, 'tcx> {}

impl<'tcx> TyFolder<'tcx> for ClauseTyInstantiator<'_, 'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn try_fold_ty(&mut self, ty: Ty) -> Result<Ty, Self::Error> {
        let s = self.session();

        let ty = match *ty.r(s) {
            TyKind::This => self.self_ty,
            TyKind::ExplicitInfer => self.ccx.fresh_ty(),
            TyKind::Simple(_)
            | TyKind::Error(_)
            | TyKind::FnDef(_, _)
            | TyKind::Universal(_)
            | TyKind::Reference(_, _, _)
            | TyKind::Adt(_)
            | TyKind::Trait(_)
            | TyKind::Tuple(_)
            | TyKind::InferVar(_) => {
                let Ok(v) = self.super_ty(ty);
                v
            }
        };

        Ok(ty)
    }
}
