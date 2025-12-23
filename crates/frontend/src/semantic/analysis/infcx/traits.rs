use crate::{
    base::{
        Diag, Session,
        arena::{HasListInterner, LateInit, Obj},
    },
    semantic::{
        analysis::{
            BinderSubstitution, ConfirmationResult, FloatingInferVar, InfTySubstitutor,
            ObligationCx, ObligationKind, ObligationReason, ObligationResult, ReAndReRelateError,
            SelectionRejected, SelectionResult, SubstitutionFolder, TyAndTyRelateError, TyCtxt,
            TyFolderInfallible as _, TyShapeMap, UnboundVarHandlingMode, UnifyCx, UnifyCxMode,
        },
        syntax::{
            AnyGeneric, Crate, FnDef, GenericBinder, GenericSolveStep, ImplItem, InferTyVar,
            ListOfTraitClauseList, Re, RelationMode, SolidTyShape, SolidTyShapeKind, SpannedTy,
            TraitClause, TraitClauseList, TraitParam, TraitSpec, Ty, TyKind, TyOrRe, TyOrReList,
            TyShape,
        },
    },
};
use index_vec::{IndexVec, define_index_type};

// === CoherenceMap === //

#[derive(Debug, Default)]
pub struct CoherenceMap {
    by_shape: TyShapeMap<CoherenceMapEntry>,
}

#[derive(Debug, Copy, Clone)]
enum CoherenceMapEntry {
    TraitImpl(Obj<ImplItem>),
    InherentMethod(Obj<FnDef>),
}

impl CoherenceMap {
    pub fn populate(&mut self, tcx: &TyCtxt, krate: Obj<Crate>) {
        let s = &tcx.session;

        // Extend map with all `impl`s.
        for &item in &**krate.r(s).items {
            let Some(item) = item.r(s).kind.as_impl() else {
                continue;
            };

            match item.r(s).trait_ {
                Some(trait_) => {
                    let arg_count = trait_.value.def.r(s).regular_generic_count as usize;
                    self.by_shape.insert(
                        tcx.shape_of_trait_def(
                            trait_.value.def,
                            &trait_.value.params.r(s)[..arg_count],
                            item.r(s).target.value,
                        ),
                        CoherenceMapEntry::TraitImpl(item),
                        s,
                    );
                }
                None => {
                    for &method in &**item.r(s).methods {
                        self.by_shape.insert(
                            TyShape::Solid(SolidTyShape {
                                kind: SolidTyShapeKind::InherentMethodImpl(method.r(s).name.text),
                                children: tcx
                                    .intern(&[tcx.erase_ty_to_shape(item.r(s).target.value)]),
                            }),
                            CoherenceMapEntry::InherentMethod(method),
                            s,
                        );
                    }
                }
            }
        }

        // Perform coherence checks
        // TODO
    }
}

// === Order Solving === //

impl TyCtxt {
    pub fn determine_impl_generic_solve_order(&self, def: Obj<ImplItem>) {
        let s = &self.session;

        define_index_type! {
            struct GenericIdx = u32;
        }

        define_index_type! {
            struct ClauseIndex = u32;
        }

        struct GenericState {
            covered: bool,
            deps: Vec<ClauseIndex>,
        }

        struct ClauseState {
            blockers: u32,
            step_idx: GenericSolveStep,
            spec: TraitSpec,
        }

        let generic_defs = &def.r(s).generics.r(s).defs;

        // Populate clauses
        let mut generic_states = generic_defs
            .iter()
            .map(|_| GenericState {
                covered: false,
                deps: Vec::new(),
            })
            .collect::<IndexVec<GenericIdx, _>>();

        let mut clause_states = IndexVec::<ClauseIndex, ClauseState>::new();

        for (step_generic_idx, main_generic_def) in generic_defs.iter().enumerate() {
            for (step_clause_idx, clause_def) in
                main_generic_def.clauses(s).value.r(s).iter().enumerate()
            {
                let TraitClause::Trait(spec) = *clause_def else {
                    continue;
                };

                let clause_state_idx = clause_states.next_idx();
                let mut blockers = 1;

                generic_states[step_generic_idx].deps.push(clause_state_idx);

                for &param in &spec.params.r(s)[..spec.def.r(s).regular_generic_count as usize] {
                    let TraitParam::Equals(ty) = param else {
                        unreachable!()
                    };

                    cbit::cbit!(for generic in self.mentioned_generics(ty) {
                        debug_assert_eq!(generic.binder(s).unwrap().def, def.r(s).generics);

                        generic_states[generic.binder(s).unwrap().idx as usize]
                            .deps
                            .push(clause_state_idx);

                        blockers += 1;
                    });
                }

                clause_states.push(ClauseState {
                    step_idx: GenericSolveStep {
                        generic_idx: step_generic_idx as u32,
                        clause_idx: step_clause_idx as u32,
                    },
                    blockers,
                    spec,
                });
            }
        }

        // Iteratively mark covered generics.
        let mut solve_queue = Vec::new();
        let mut solve_order = Vec::new();

        fn cover_idx(
            solve_queue: &mut Vec<TraitSpec>,
            solve_order: &mut Vec<GenericSolveStep>,
            generic_states: &mut IndexVec<GenericIdx, GenericState>,
            clause_states: &mut IndexVec<ClauseIndex, ClauseState>,
            idx: GenericIdx,
        ) {
            let generic = &mut generic_states[idx];

            if generic.covered {
                return;
            }

            generic.covered = true;

            for &dep in &generic.deps {
                let clause = &mut clause_states[dep];
                clause.blockers -= 1;

                if clause.blockers > 0 {
                    continue;
                }

                solve_queue.push(clause.spec);
                solve_order.push(clause.step_idx);
            }
        }

        fn cover_ty(
            tcx: &TyCtxt,
            solve_queue: &mut Vec<TraitSpec>,
            solve_order: &mut Vec<GenericSolveStep>,
            generic_states: &mut IndexVec<GenericIdx, GenericState>,
            clause_states: &mut IndexVec<ClauseIndex, ClauseState>,
            binder: Obj<GenericBinder>,
            ty: Ty,
        ) {
            let s = &tcx.session;

            cbit::cbit!(for generic in tcx.mentioned_generics(TyOrRe::Ty(ty)) {
                debug_assert_eq!(generic.binder(s).unwrap().def, binder);

                cover_idx(
                    solve_queue,
                    solve_order,
                    generic_states,
                    clause_states,
                    GenericIdx::from_raw(generic.binder(s).unwrap().idx),
                );
            });
        }

        // Cover generics appearing in the target type and trait.
        cover_ty(
            self,
            &mut solve_queue,
            &mut solve_order,
            &mut generic_states,
            &mut clause_states,
            def.r(s).generics,
            def.r(s).target.value,
        );

        if let Some(trait_) = def.r(s).trait_ {
            for &param in trait_.value.params.r(s) {
                match param {
                    TyOrRe::Re(param) => {
                        match param {
                            Re::Gc | Re::Error(_) => {
                                // (nothing mentioned)
                            }
                            Re::Universal(param) => {
                                cover_idx(
                                    &mut solve_queue,
                                    &mut solve_order,
                                    &mut generic_states,
                                    &mut clause_states,
                                    GenericIdx::from_raw(param.r(s).binder.unwrap().idx),
                                );
                            }
                            Re::InferVar(_) | Re::ExplicitInfer | Re::Erased => unreachable!(),
                        }
                    }
                    TyOrRe::Ty(param) => {
                        cover_ty(
                            self,
                            &mut solve_queue,
                            &mut solve_order,
                            &mut generic_states,
                            &mut clause_states,
                            def.r(s).generics,
                            param,
                        );
                    }
                }
            }
        }

        // Recursively uncover more generics.
        while let Some(clause) = solve_queue.pop() {
            for param in &clause.params.r(s)[(clause.def.r(s).regular_generic_count as usize)..] {
                match param {
                    TraitParam::Equals(eq) => {
                        // We can use this to reveal more equalities!
                        cover_ty(
                            self,
                            &mut solve_queue,
                            &mut solve_order,
                            &mut generic_states,
                            &mut clause_states,
                            def.r(s).generics,
                            eq.unwrap_ty(),
                        );
                    }
                    TraitParam::Unspecified(_) => {
                        // (does not contribute to solve order)
                    }
                }
            }
        }

        // Ensure that all generics are covered.
        for (state, def) in generic_states.iter().zip(generic_defs) {
            if !state.covered {
                Diag::span_err(def.span(s), "generic parameter not covered by `impl`").emit();
            }
        }

        LateInit::init(&def.r(s).generic_solve_order, solve_order);
    }
}

// === TraitCx Core === //

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
/// the programmer has created. This has to be done at the end of an inference session since
/// inferred types must all be solved by this point.
#[derive(Clone)]
pub struct TraitCx<'tcx> {
    ocx: ObligationCx<'tcx>,
    coherence: &'tcx CoherenceMap,
}

impl<'tcx> TraitCx<'tcx> {
    pub fn new(
        tcx: &'tcx TyCtxt,
        coherence: &'tcx CoherenceMap,
        mode: UnifyCxMode,
        max_obligation_depth: u32,
    ) -> Self {
        Self {
            ocx: ObligationCx::new(tcx, mode, max_obligation_depth),
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

    fn process_obligations(&mut self) {
        if self.ocx.is_running_obligation() {
            return;
        }

        while let Some(kind) = self.ocx.start_running_obligation() {
            let mut fork = self.clone();

            let res = match kind {
                ObligationKind::TyAndTrait(lhs, rhs) => fork.run_relate_ty_and_trait(lhs, rhs),
                ObligationKind::TyAndRe(lhs, rhs) => fork.run_relate_ty_and_re(lhs, rhs),
            };

            if fork.ocx.finish_running_obligation(res).should_apply() {
                *self = fork;
            }
        }
    }
}

// Forwards
impl<'tcx> TraitCx<'tcx> {
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

    pub fn relate_re_and_re(
        &mut self,
        lhs: Re,
        rhs: Re,
        mode: RelationMode,
    ) -> Result<(), Box<ReAndReRelateError>> {
        let res = self.ucx_mut().relate_re_and_re(lhs, rhs, mode);
        self.process_obligations();
        res
    }

    pub fn relate_ty_and_ty(
        &mut self,
        lhs: Ty,
        rhs: Ty,
        mode: RelationMode,
    ) -> Result<(), Box<TyAndTyRelateError>> {
        let res = self.ucx_mut().relate_ty_and_ty(lhs, rhs, mode);
        self.process_obligations();
        res
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

impl<'tcx> TraitCx<'tcx> {
    pub fn relate_ty_and_clause(
        &mut self,
        reason: ObligationReason,
        lhs: Ty,
        rhs: TraitClauseList,
    ) {
        let s = self.session();

        for &clause in rhs.r(s) {
            match clause {
                TraitClause::Outlives(rhs) => {
                    self.relate_ty_and_re(reason, lhs, rhs);
                }
                TraitClause::Trait(rhs) => {
                    self.relate_ty_and_trait(reason, lhs, rhs);
                }
            }
        }
    }

    pub fn relate_re_and_clause(&mut self, lhs: Re, rhs: TraitClauseList) {
        let s = self.session();

        for &clause in rhs.r(s) {
            match clause {
                TraitClause::Outlives(rhs) => {
                    self.relate_re_and_re(lhs, rhs, RelationMode::LhsOntoRhs);
                }
                TraitClause::Trait(_) => {
                    unreachable!()
                }
            }
        }
    }

    pub fn relate_ty_and_trait(&mut self, reason: ObligationReason, lhs: Ty, rhs: TraitSpec) {
        self.ocx
            .push_obligation(reason, ObligationKind::TyAndTrait(lhs, rhs));
    }

    fn run_relate_ty_and_trait(&mut self, lhs: Ty, rhs: TraitSpec) -> ObligationResult {
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
            TyKind::Error(..) => {
                // Error types can do anything.
                return ObligationResult::Success;
            }
            TyKind::This | TyKind::ExplicitInfer => unreachable!(),
            TyKind::Simple(..)
            | TyKind::Reference(..)
            | TyKind::Adt(..)
            | TyKind::Tuple(..)
            | TyKind::FnDef(..) => {
                // (the `impl` must come externally, fallthrough)
            }
        }

        // Otherwise, scan for a suitable `impl`.
        let mut prev_confirmation = None;

        for candidate in self.gather_impl_candidates(lhs, rhs) {
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
                "failed to prove {lhs:?} implements {rhs:?}"
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

        for (&lhs_param, &rhs_param) in lhs
            .params
            .r(s)
            .iter()
            .zip(rhs.params.r(s))
            .take(rhs.def.r(s).regular_generic_count as usize)
        {
            let TraitParam::Equals(lhs) = lhs_param else {
                unreachable!();
            };

            match rhs_param {
                TraitParam::Equals(rhs) => match (lhs, rhs) {
                    (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                        if let Err(_err) = self.relate_re_and_re(lhs, rhs, RelationMode::Equate) {
                            return Err(SelectionRejected);
                        }
                    }
                    (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                        if let Err(_err) = self.relate_ty_and_ty(lhs, rhs, RelationMode::Equate) {
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

        // TODO: Obligations

        Ok(ConfirmationResult::Success(self))
    }

    fn gather_impl_candidates(
        &self,
        lhs: Ty,
        rhs: TraitSpec,
    ) -> impl Iterator<Item = Obj<ImplItem>> + 'tcx {
        let tcx = self.tcx();
        let s = self.session();

        self.coherence
            .by_shape
            .lookup(
                tcx.shape_of_trait_def(
                    rhs.def,
                    &rhs.params.r(s)[..rhs.def.r(s).regular_generic_count as usize]
                        .iter()
                        .map(|&v| match v {
                            TraitParam::Equals(v) => InfTySubstitutor::new(
                                self.ucx(),
                                UnboundVarHandlingMode::EraseToExplicitInfer,
                            )
                            .fold_ty_or_re(v),
                            TraitParam::Unspecified(_) => unreachable!(),
                        })
                        .collect::<Vec<_>>(),
                    InfTySubstitutor::new(self.ucx(), UnboundVarHandlingMode::EraseToExplicitInfer)
                        .fold_ty(lhs),
                ),
                s,
            )
            .map(|v| {
                let CoherenceMapEntry::TraitImpl(v) = *v else {
                    unreachable!()
                };

                v
            })
    }

    fn try_select_block_impl(
        mut self,
        lhs: Ty,
        rhs: Obj<ImplItem>,
        spec: TraitSpec,
    ) -> SelectionResult<Self> {
        let s = self.session();

        // Replace universal qualifications in `impl` with inference variables
        let rhs_fresh = self.instantiate_fresh_impl_vars(rhs);

        // Does the `lhs` type match the `rhs`'s target type?
        if self
            .relate_ty_and_ty(lhs, rhs_fresh.target, RelationMode::Equate)
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
                            .relate_re_and_re(instance, required, RelationMode::Equate)
                            .is_err()
                        {
                            return Err(SelectionRejected);
                        }
                    }
                    (TyOrRe::Ty(instance), TyOrRe::Ty(required)) => {
                        if self
                            .relate_ty_and_ty(instance, required, RelationMode::Equate)
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
        // TODO

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

impl<'tcx> TraitCx<'tcx> {
    pub fn relate_ty_and_re(&mut self, reason: ObligationReason, lhs: Ty, rhs: Re) {
        self.ocx
            .push_obligation(reason, ObligationKind::TyAndRe(lhs, rhs));
    }

    fn run_relate_ty_and_re(&mut self, lhs: Ty, rhs: Re) -> ObligationResult {
        let s = self.session();

        match *lhs.r(s) {
            TyKind::This | TyKind::ExplicitInfer => unreachable!(),
            TyKind::FnDef(_) | TyKind::Simple(_) | TyKind::Error(_) => {
                // (trivial)
            }
            TyKind::Reference(lhs, _muta, _pointee) => {
                // No need to relate the pointee since WF checks already ensure that it outlives
                // `lhs`.
                if let Err(err) = self.relate_re_and_re(lhs, rhs, RelationMode::LhsOntoRhs) {
                    return ObligationResult::Failure(err.to_diag());
                }
            }
            TyKind::Adt(lhs) => {
                // ADTs are bounded by which regions they mention.
                for &lhs in lhs.params.r(s) {
                    match lhs {
                        TyOrRe::Re(lhs) => {
                            if let Err(err) =
                                self.relate_re_and_re(lhs, rhs, RelationMode::LhsOntoRhs)
                            {
                                return ObligationResult::Failure(err.to_diag());
                            }
                        }
                        TyOrRe::Ty(lhs) => {
                            self.relate_ty_and_re(ObligationReason::Structural, lhs, rhs);
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
                                self.relate_re_and_re(lhs, rhs, RelationMode::LhsOntoRhs)
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
                    self.relate_ty_and_re(ObligationReason::Structural, lhs, rhs);
                }
            }
            TyKind::Universal(_) => todo!(),
            TyKind::InferVar(inf_lhs) => {
                if let Ok(inf_lhs) = self.lookup_ty_var(inf_lhs) {
                    self.relate_ty_and_re(ObligationReason::Structural, inf_lhs, rhs);
                } else {
                    return ObligationResult::NotReady;
                }
            }
        }

        ObligationResult::Success
    }
}

// === WF Relations === //

impl<'tcx> TraitCx<'tcx> {
    pub fn wf_ty(&mut self, ty: SpannedTy) {
        todo!()
    }
}
