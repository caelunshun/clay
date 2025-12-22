use crate::{
    base::{
        Diag, HardDiag, Session,
        arena::{HasListInterner, LateInit, Obj},
        syntax::Span,
    },
    semantic::{
        analysis::{
            BinderSubstitution, FloatingInferVar, InfTySubstitutor, InferCx, InferCxMode,
            ObservedTyVar, ReAndReRelateError, SubstitutionFolder, TyAndTyRelateError, TyCtxt,
            TyFolderInfallible as _, TyShapeMap, UnboundVarHandlingMode,
        },
        syntax::{
            AnyGeneric, Crate, FnDef, GenericBinder, GenericSolveStep, ImplItem, InferTyVar,
            ListOfTraitClauseList, Re, RelationMode, SolidTyShape, SolidTyShapeKind, SpannedTy,
            TraitClause, TraitClauseList, TraitParam, TraitSpec, Ty, TyKind, TyOrRe, TyOrReList,
            TyShape,
        },
    },
    utils::hash::{FxHashMap, FxHashSet},
};
use index_vec::{IndexVec, define_index_type};
use std::collections::VecDeque;

// === Errors === //

#[derive(Debug, Clone)]
pub struct RelateClauseAndTraitError;

#[derive(Debug, Clone)]
pub struct SelectTraitError;

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

// === ObligationCx Core === //

/// A type inference context for solving type obligations of the form...
///
/// - `Region: Region`
/// - `Type = Type`
/// - `Type: Clauses`
/// - `Clauses entail Clauses`
/// - `is-well-formed Type`
///
/// This context is built on top of an [`InferCx`].
///
/// ## Obligation Solving
///
/// An obligation is something that must unconditionally hold in order for a program to compile.
/// This means that, unlike `InferCx` relations, obligations cannot be tried for success. In return
/// for this strict structure, obligations are automatically scheduled out of order to ensure that
/// all inference variables are solved in the correct order. Additionally, obligations can be solved
/// co-inductively—that is, an obligation can assume itself to be true while proving itself.
///
/// ## Multi-pass Checking
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
pub struct ObligationCx<'tcx> {
    icx: InferCx<'tcx>,
    coherence: &'tcx CoherenceMap,

    /// The obligation we're currently in the process of invoking.
    current_obligation: Option<ObligationIdx>,

    /// All obligations ever registered with us.
    all_obligations: IndexVec<ObligationIdx, Obligation>,

    /// Every single obligation we've ever tried to prove. We only ever have to prove a given
    /// obligation and, if an obligation depends on itself, it is safe to assume it holds
    /// coinductively while proving itself.
    all_obligation_kinds: FxHashSet<ObligationKind>,

    /// The queue obligations to invoke. These are invoked in FIFO order to ensure that we properly
    /// explore all branches of the proof tree simultaneously.
    run_queue: VecDeque<ObligationIdx>,

    /// A map from inference variables to obligations they could re-run upon being inferred.
    var_wake_ups: FxHashMap<ObservedTyVar, Vec<ObligationIdx>>,

    /// The number of observed inference variables we have processed from `icx`'s
    /// `observed_reveal_order` list.
    rerun_var_read_len: usize,

    /// The maximum depth we're willing to expand for obligations
    max_obligation_depth: u32,
}

define_index_type! {
    pub struct ObligationIdx = u32;
}

struct Obligation {
    /// The obligation responsible for spawning this new obligation.
    parent: Option<ObligationIdx>,

    /// The number of parent obligations leading to the creation of this obligation.
    depth: u32,

    /// The reason for which this obligation was spawned.
    reason: ObligationReason,

    /// The kind of obligation we're trying to prove.
    kind: ObligationKind,

    /// The set of variables whose inference could cause us to rerun. Cleared once the obligation is
    /// enqueued to re-run and re-populated if, after the re-run, the obligation is still ambiguous.
    can_wake_by: FxHashSet<ObservedTyVar>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ObligationKind {
    TyAndTrait(Ty, TraitSpec),
    TyAndRe(Ty, Re),
}

impl ObligationKind {
    // TODO
    pub fn proves_what(self, s: &Session) -> String {
        _ = s;
        format!("{self:?}")
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ObligationReason {
    FunctionBody(Span),
    Structural,
}

#[derive(Debug, Clone)]
pub enum ObligationResult {
    /// The obligation was successfully satisfied.
    Success,

    /// The obligation is guaranteed to fail.
    Failure(HardDiag),

    /// The obligation has failed because of an ambiguity. This could either be caused by a missing
    /// inference variable or, if no inference variables were looked up or unified in the solving of
    /// this obligation, a genuine ambiguity.
    ///
    /// If this result is returned, the obligation will be enqueued to run again once one or more of
    /// the inference variables the obligation depended upon during execution have been solved.
    Ambiguous(HardDiag),
}

// Constructor and getters
impl<'tcx> ObligationCx<'tcx> {
    pub fn new(
        tcx: &'tcx TyCtxt,
        coherence: &'tcx CoherenceMap,
        mode: InferCxMode,
        max_obligation_depth: u32,
    ) -> Self {
        Self {
            icx: InferCx::new(tcx, mode),
            coherence,
            current_obligation: None,
            all_obligations: IndexVec::new(),
            all_obligation_kinds: FxHashSet::default(),
            run_queue: VecDeque::new(),
            var_wake_ups: FxHashMap::default(),
            rerun_var_read_len: 0,
            max_obligation_depth,
        }
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.icx.tcx()
    }

    pub fn session(&self) -> &'tcx Session {
        self.icx.session()
    }

    pub fn coherence(&self) -> &'tcx CoherenceMap {
        self.coherence
    }

    pub fn icx(&self) -> &InferCx<'tcx> {
        &self.icx
    }

    pub fn icx_mut(&mut self) -> &mut InferCx<'tcx> {
        &mut self.icx
    }
}

// Forwards
impl<'tcx> ObligationCx<'tcx> {
    pub fn mode(&self) -> InferCxMode {
        self.icx.mode()
    }

    pub fn fresh_ty_var(&mut self) -> InferTyVar {
        self.icx.fresh_ty_var()
    }

    pub fn fresh_ty(&mut self) -> Ty {
        self.icx.fresh_ty()
    }

    pub fn lookup_ty_var(&self, var: InferTyVar) -> Result<Ty, FloatingInferVar<'_>> {
        self.icx.lookup_ty_var(var)
    }

    pub fn peel_ty_var(&self, ty: Ty) -> Ty {
        self.icx.peel_ty_var(ty)
    }

    pub fn fresh_re(&mut self) -> Re {
        self.icx.fresh_re()
    }

    pub fn relate_re_and_re(
        &mut self,
        lhs: Re,
        rhs: Re,
        mode: RelationMode,
    ) -> Result<(), Box<ReAndReRelateError>> {
        let res = self.icx.relate_re_and_re(lhs, rhs, mode);
        self.process_obligations();
        res
    }

    pub fn relate_ty_and_ty(
        &mut self,
        lhs: Ty,
        rhs: Ty,
        mode: RelationMode,
    ) -> Result<(), Box<TyAndTyRelateError>> {
        let res = self.icx.relate_ty_and_ty(lhs, rhs, mode);
        self.process_obligations();
        res
    }
}

// Core operations
impl<'tcx> ObligationCx<'tcx> {
    pub fn push_obligation(&mut self, reason: ObligationReason, kind: ObligationKind) {
        if self.all_obligation_kinds.insert(kind) {
            return;
        }

        let depth = self
            .current_obligation
            .map_or(0, |v| self.all_obligations[v].depth + 1);

        let obligation = self.all_obligations.push(Obligation {
            parent: self.current_obligation,
            depth,
            reason,
            kind,
            can_wake_by: FxHashSet::default(),
        });

        self.run_queue.push_back(obligation);
        self.process_obligations();
    }

    pub fn process_obligations(&mut self) {
        if self.current_obligation.is_some() {
            return;
        }

        self.process_obligations_inner(/* error_on_ambiguity*/ false);
    }

    pub fn force_obligations_to_finish(&mut self) {
        self.process_obligations_inner(/* error_on_ambiguity*/ true);
    }

    fn process_obligations_inner(&mut self, error_on_ambiguity: bool) {
        let s = self.session();

        debug_assert!(self.current_obligation.is_none());

        self.discover_obligations_reruns();

        while let Some(front_idx) = self.run_queue.pop_front() {
            let Obligation {
                depth,
                kind,
                ref can_wake_by,
                ..
            } = self.all_obligations[front_idx];

            debug_assert!(can_wake_by.is_empty());

            // Run the obligation.
            let old_icx = self.icx.clone();

            let result = 'res: {
                if depth >= self.max_obligation_depth {
                    break 'res ObligationResult::Failure(Diag::anon_err(format_args!(
                        "overflowed requirements while trying to prove {}",
                        kind.proves_what(s),
                    )));
                }

                self.current_obligation = Some(front_idx);

                let mut this = scopeguard::guard(&mut *self, |this| {
                    this.current_obligation = None;
                });

                this.icx.start_tracing();
                this.run_obligation_now(kind)
            };

            let involved_vars = self.icx.finish_tracing();

            // Process its result.
            let diag = match result {
                ObligationResult::Success => None,
                ObligationResult::Failure(diag) => {
                    self.icx = old_icx;
                    Some(diag)
                }
                ObligationResult::Ambiguous(diag) => {
                    self.icx = old_icx;

                    let front = &mut self.all_obligations[front_idx];

                    if !error_on_ambiguity {
                        for var in involved_vars {
                            if self.icx.lookup_ty_var(var).is_ok() {
                                continue;
                            }

                            let var = self.icx.observe_ty_var(var);

                            if !front.can_wake_by.insert(var) {
                                continue;
                            }

                            self.var_wake_ups.entry(var).or_default().push(front_idx);
                        }
                    }

                    front.can_wake_by.is_empty().then_some(diag)
                }
            };

            if let Some(diag) = diag {
                // TODO: Push reason stack
                diag.emit();
            }

            self.discover_obligations_reruns();
        }
    }

    fn discover_obligations_reruns(&mut self) {
        for &var in &self.icx.observed_reveal_order()[self.rerun_var_read_len..] {
            let Some(awoken) = self.var_wake_ups.remove(&var) else {
                continue;
            };

            for awoken_idx in awoken {
                let awoken = &mut self.all_obligations[awoken_idx];

                if !awoken.can_wake_by.contains(&var) {
                    continue;
                }

                awoken.can_wake_by.clear();

                self.run_queue.push_back(awoken_idx);
            }
        }

        self.rerun_var_read_len = self.icx.observed_reveal_order().len();
    }

    fn run_obligation_now(&mut self, kind: ObligationKind) -> ObligationResult {
        match kind {
            ObligationKind::TyAndTrait(lhs, rhs) => self.run_relate_ty_and_trait(lhs, rhs),
            ObligationKind::TyAndRe(lhs, rhs) => self.run_relate_ty_and_re(lhs, rhs),
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

impl<'tcx> ObligationCx<'tcx> {
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
        self.push_obligation(reason, ObligationKind::TyAndTrait(lhs, rhs));
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
                match Self::relate_clause_and_trait(
                    &mut self.icx,
                    tcx.elaborate_generic_clauses(generic, None),
                    rhs,
                ) {
                    Ok(()) => {
                        return ObligationResult::Success;
                    }
                    Err(RelateClauseAndTraitError) => {
                        // (fallthrough)
                    }
                }
            }
            TyKind::InferVar(_) => {
                // We can't yet rule out the possibility that this obligation is inherently
                // fulfilled.
                return ObligationResult::Ambiguous(HardDiag::anon_err("type annotation required"));
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

        // Select an unambiguous satisfying `impl`.
        // TODO

        // Register that `impl`'s obligations.
        // TODO

        todo!()
    }

    fn gather_impl_candidates<'a>(
        &'a self,
        lhs: Ty,
        rhs: TraitSpec,
    ) -> impl Iterator<Item = Obj<ImplItem>> + 'tcx {
        let tcx = self.tcx();
        let s = self.session();

        self.coherence()
            .by_shape
            .lookup(
                tcx.shape_of_trait_def(
                    rhs.def,
                    &rhs.params.r(s)[..rhs.def.r(s).regular_generic_count as usize]
                        .iter()
                        .map(|&v| match v {
                            TraitParam::Equals(v) => InfTySubstitutor::new(
                                self.icx(),
                                UnboundVarHandlingMode::EraseToExplicitInfer,
                            )
                            .fold_ty_or_re(v),
                            TraitParam::Unspecified(_) => unreachable!(),
                        })
                        .collect::<Vec<_>>(),
                    InfTySubstitutor::new(self.icx(), UnboundVarHandlingMode::EraseToExplicitInfer)
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

    fn instantiate_fresh_impl_vars(
        icx: &mut InferCx<'tcx>,
        candidate: Obj<ImplItem>,
    ) -> ImplFreshInfer {
        let tcx = icx.tcx();
        let s = icx.session();

        // Define fresh variables describing the substitutions to be made.
        let binder = candidate.r(s).generics;
        let impl_generics = binder
            .r(s)
            .defs
            .iter()
            .map(|generic| match generic {
                AnyGeneric::Re(_) => TyOrRe::Re(icx.fresh_re()),
                AnyGeneric::Ty(_) => TyOrRe::Ty(icx.fresh_ty()),
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

    fn try_select_impl_no_fork(
        icx: &mut InferCx<'tcx>,
        lhs: Ty,
        rhs: Obj<ImplItem>,
        spec: TraitSpec,
    ) -> Result<ImplFreshInfer, SelectTraitError> {
        let s = icx.session();

        // Replace universal qualifications in `impl` with inference variables
        let rhs_fresh = Self::instantiate_fresh_impl_vars(icx, rhs);

        // Does the `lhs` type match the `rhs`'s target type?
        if icx
            .relate_ty_and_ty(lhs, rhs_fresh.target, RelationMode::Equate)
            .is_err()
        {
            return Err(SelectTraitError);
        }

        // See whether our specific target trait clauses can be covered by the inferred
        // generics. We only check the regular generics at this stage since associated types are
        // defined entirely from our solved regular generics.
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
                        if icx
                            .relate_re_and_re(instance, required, RelationMode::Equate)
                            .is_err()
                        {
                            return Err(SelectTraitError);
                        }
                    }
                    (TyOrRe::Ty(instance), TyOrRe::Ty(required)) => {
                        if icx
                            .relate_ty_and_ty(instance, required, RelationMode::Equate)
                            .is_err()
                        {
                            return Err(SelectTraitError);
                        }
                    }
                    _ => unreachable!(),
                },
                TraitParam::Unspecified(_) => {
                    unreachable!()
                }
            }
        }

        Ok(rhs_fresh)
    }

    fn relate_clause_and_trait(
        icx: &mut InferCx<'tcx>,
        lhs_elaborated: TraitClauseList,
        rhs: TraitSpec,
    ) -> Result<(), RelateClauseAndTraitError> {
        let s = icx.session();

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
            return Err(RelateClauseAndTraitError);
        };

        let TraitClause::Trait(lhs) = lhs else {
            unreachable!()
        };

        let mut fork = icx.clone();

        for (&lhs_param, &rhs_param) in lhs.params.r(s).iter().zip(rhs.params.r(s)) {
            let TraitParam::Equals(lhs) = lhs_param else {
                unreachable!();
            };

            match rhs_param {
                TraitParam::Equals(rhs) => match (lhs, rhs) {
                    (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                        if let Err(_err) = fork.relate_re_and_re(lhs, rhs, RelationMode::Equate) {
                            return Err(RelateClauseAndTraitError);
                        }
                    }
                    (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                        if let Err(_err) = fork.relate_ty_and_ty(lhs, rhs, RelationMode::Equate) {
                            return Err(RelateClauseAndTraitError);
                        }
                    }
                    _ => unreachable!(),
                },
                TraitParam::Unspecified(rhs_clauses) => {
                    let TyOrRe::Ty(lhs) = lhs else { unreachable!() };

                    if let Err(_err) = Self::relate_ty_and_clause(&mut fork, lhs, rhs_clauses) {
                        return Err(RelateClauseAndTraitError);
                    }
                }
            }
        }

        *icx = fork;

        Ok(())
    }
}

// === Ty & Re Relations === //

impl<'tcx> ObligationCx<'tcx> {
    pub fn relate_ty_and_re(&mut self, reason: ObligationReason, lhs: Ty, rhs: Re) {
        self.push_obligation(reason, ObligationKind::TyAndRe(lhs, rhs));
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
                    return ObligationResult::Ambiguous(HardDiag::anon_err(
                        "type annotation required",
                    ));
                }
            }
        }

        ObligationResult::Success
    }
}

// === WF Relations === //

impl<'tcx> ObligationCx<'tcx> {
    pub fn wf_ty(&mut self, ty: SpannedTy) {
        todo!()
    }
}
