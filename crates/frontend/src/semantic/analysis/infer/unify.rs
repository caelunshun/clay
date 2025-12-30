use crate::{
    base::{ErrorGuaranteed, HardDiag, Session, arena::HasInterner},
    semantic::{
        analysis::{TyCtxt, TyFolder, TyFolderInfallible, TyVisitor, TyVisitorExt},
        syntax::{
            InferReVar, InferTyVar, Mutability, Re, ReVariance, RelationMode, SpannedTy,
            SpannedTyView, TraitClause, TraitClauseList, TraitParam, Ty, TyKind, TyOrRe,
            UniversalReVar, UniversalReVarSourceInfo,
        },
    },
    utils::hash::FxHashSet,
};
use bit_set::BitSet;
use disjoint::DisjointSetVec;
use index_vec::{IndexVec, define_index_type};
use smallvec::SmallVec;
use std::{cell::RefCell, convert::Infallible, ops::ControlFlow, rc::Rc};

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
            "could not unify {:?} and {:?}",
            self.origin_lhs, self.origin_rhs,
        ))
    }
}

#[derive(Debug, Clone)]
pub enum TyAndTyUnifyCulprit {
    Types(Ty, Ty),
    Regions(Box<ReAndReUnifyError>),
    ClauseLists(TraitClauseList, TraitClauseList),
    Params(TraitParam, TraitParam),
    RecursiveType(InferTyOccursError),
}

#[derive(Debug, Clone)]
pub struct InferTyOccursError {
    pub var: InferTyVar,
    pub occurs_in: Ty,
}

#[derive(Debug, Clone)]
pub struct ReAndReUnifyError {
    pub lhs: Re,
    pub rhs: Re,
    pub offenses: Vec<ReAndReUnifyOffense>,
}

#[derive(Debug, Clone)]
pub struct ReAndReUnifyOffense {
    pub universal: UniversalReVar,
    pub forced_to_outlive: Re,
}

impl ReAndReUnifyError {
    // TODO
    pub fn to_diag(self) -> HardDiag {
        HardDiag::anon_err(format_args!(
            "could not unify {:?} and {:?}",
            self.lhs, self.rhs,
        ))
    }
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
    types: TyInferTracker,
    regions: Option<ReInferTracker>,
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
            types: TyInferTracker::default(),
            regions: match mode {
                UnifyCxMode::RegionBlind => None,
                UnifyCxMode::RegionAware => Some(ReInferTracker::default()),
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

    pub fn permit_re_universal_outlives(&mut self, lhs: Re, rhs: Re) {
        let Some(regions) = &mut self.regions else {
            debug_assert!(matches!(lhs, Re::Erased));
            debug_assert!(matches!(rhs, Re::Erased));

            return;
        };

        debug_assert!(matches!(lhs, Re::UniversalVar(_)));
        debug_assert!(matches!(rhs, Re::UniversalVar(_)));

        regions.unify(lhs, rhs, None);
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
    ) -> Result<(), Box<ReAndReUnifyError>> {
        let Some(regions) = &mut self.regions else {
            debug_assert!(matches!(lhs, Re::Erased));
            debug_assert!(matches!(rhs, Re::Erased));

            return Ok(());
        };

        let tmp1;
        let tmp2;
        let equivalences = match mode {
            RelationMode::LhsOntoRhs => {
                tmp1 = [(lhs, rhs)];
                &tmp1[..]
            }
            RelationMode::RhsOntoLhs => {
                tmp1 = [(rhs, lhs)];
                &tmp1[..]
            }
            RelationMode::Equate => {
                tmp2 = [(lhs, rhs), (rhs, lhs)];
                &tmp2[..]
            }
        };

        let mut offenses = Vec::new();
        let mut fork = regions.clone();

        for &(lhs, rhs) in equivalences {
            if lhs == rhs {
                continue;
            }

            match (lhs, rhs) {
                (Re::Erased, _) | (_, Re::Erased) | (Re::SigInfer, _) | (_, Re::SigInfer) => {
                    unreachable!()
                }
                _ => {
                    fork.unify(lhs, rhs, Some(&mut offenses));
                }
            }
        }

        if !offenses.is_empty() {
            return Err(Box::new(ReAndReUnifyError { lhs, rhs, offenses }));
        }

        *regions = fork;

        Ok(())
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
            | (_, TyKind::SigGeneric(_)) => {
                unreachable!()
            }
            (
                TyKind::Reference(lhs_re, lhs_muta, lhs_pointee),
                TyKind::Reference(rhs_re, rhs_muta, rhs_pointee),
            ) if lhs_muta == rhs_muta => {
                if let Err(err) = self.unify_re_and_re(lhs_re, rhs_re, mode) {
                    culprits.push(TyAndTyUnifyCulprit::Regions(err));
                }

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
                            if let Err(err) = self.unify_re_and_re(lhs, rhs, mode) {
                                culprits.push(TyAndTyUnifyCulprit::Regions(err));
                            }
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
                    // In `rustc`, these types always seem to be invariant...
                    //
                    // ```rust
                    // fn meow<'a, 'b>() {
                    //     let a = &mut foo::<'a>;
                    //     let b = &mut bar::<'b>;
                    //
                    //     eq(a, b);
                    // }
                    //
                    // fn eq<T>(a: &mut T, b: &mut T) {}
                    //
                    // fn foo<'a>() -> &'a mut u32 {}
                    //
                    // fn bar<'a>() -> &'a mut u32 {}
                    // ```
                    //
                    // ```
                    // error[E0308]: mismatched types
                    //  --> src/lib.rs:5:11
                    //   |
                    // 5 |     eq(a, b);
                    //   |     --    ^ expected `&mut fn() -> &mut u32 {foo::<'_>}`, found `&mut fn() -> &mut u32 {bar::<'_>}`
                    //   |     |
                    //   |     arguments to this function are incorrect
                    //   |
                    //   = note: expected mutable reference `&mut fn() -> &'a mut _ {foo::<'a>}`
                    //              found mutable reference `&mut fn() -> &'b mut _ {bar::<'b>}`
                    // note: function defined here
                    // ```
                    let mode = RelationMode::Equate;

                    match (lhs, rhs) {
                        (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                            if let Err(err) = self.unify_re_and_re(lhs, rhs, mode) {
                                culprits.push(TyAndTyUnifyCulprit::Regions(err));
                            }
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
                .fold_ty(rhs_ty);

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
        lhs: TraitClauseList,
        rhs: TraitClauseList,
        culprits: &mut Vec<TyAndTyUnifyCulprit>,
        mode: RelationMode,
    ) {
        let s = self.session();

        if lhs.r(s).len() != rhs.r(s).len() {
            culprits.push(TyAndTyUnifyCulprit::ClauseLists(lhs, rhs));
            return;
        }

        for (&lhs_clause, &rhs_clause) in lhs.r(s).iter().zip(rhs.r(s)) {
            match (lhs_clause, rhs_clause) {
                (TraitClause::Outlives(lhs), TraitClause::Outlives(rhs)) => {
                    // Technically, `MyTrait + 'a + 'b: 'c` could imply either `'a: 'c` or
                    // `'b: 'c`, meaning that relating both would be unnecessary but this
                    // logic will produce constraints for both. This isn't a problem because
                    // we only ever lower trait objects with *exactly one* outlives
                    // constraint.
                    if let Err(err) = self.unify_re_and_re(lhs, rhs, mode) {
                        culprits.push(TyAndTyUnifyCulprit::Regions(err));
                    }
                }
                (TraitClause::Trait(lhs), TraitClause::Trait(rhs)) if lhs.def == rhs.def => {
                    for (&lhs, &rhs) in lhs.params.r(s).iter().zip(rhs.params.r(s)) {
                        match (lhs, rhs) {
                            (TraitParam::Equals(lhs), TraitParam::Equals(rhs)) => {
                                match (lhs, rhs) {
                                    (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                                        if let Err(err) =
                                            self.unify_re_and_re(lhs, rhs, RelationMode::Equate)
                                        {
                                            culprits.push(TyAndTyUnifyCulprit::Regions(err));
                                        }
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
                    culprits.push(TyAndTyUnifyCulprit::ClauseLists(lhs, rhs));
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

    fn try_fold_ty_infer_var_use(&mut self, var: InferTyVar) -> Result<Ty, Self::Error> {
        match self.ucx.lookup_ty_infer_var(var) {
            Ok(v) => self.try_fold_ty(v),
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

// === TyInferTracker === //

#[derive(Debug, Clone)]
struct TyInferTracker {
    disjoint: DisjointSetVec<DisjointTyInferNode>,
    observed_reveal_order: Vec<ObservedTyInferVar>,
    next_observe_idx: ObservedTyInferVar,
    tracing_state: Option<Rc<TyInferTracingState>>,
}

#[derive(Debug, Clone)]
struct DisjointTyInferNode {
    root: Option<DisjointTyInferRoot>,
    observed_idx: Option<ObservedTyInferVar>,
}

#[derive(Debug, Clone)]
enum DisjointTyInferRoot {
    Known(Ty),
    Floating(Vec<ObservedTyInferVar>),
}

#[derive(Debug)]
struct TyInferTracingState {
    set: RefCell<FxHashSet<InferTyVar>>,
    var_count: InferTyVar,
}

impl Default for TyInferTracker {
    fn default() -> Self {
        Self {
            disjoint: DisjointSetVec::new(),
            observed_reveal_order: Vec::new(),
            next_observe_idx: ObservedTyInferVar::from_usize(0),
            tracing_state: None,
        }
    }
}

impl TyInferTracker {
    fn start_tracing(&mut self) {
        debug_assert!(self.tracing_state.is_none());

        self.tracing_state = Some(Rc::new(TyInferTracingState {
            set: RefCell::default(),
            var_count: InferTyVar(self.disjoint.len() as u32),
        }))
    }

    fn finish_tracing(&mut self) -> FxHashSet<InferTyVar> {
        let set = self.tracing_state.take().expect("not tracing");
        let set = Rc::into_inner(set)
            .expect("derived inference contexts remain using the same tracing state");

        set.set.into_inner()
    }

    fn mention_var_for_tracing(&self, var: InferTyVar) {
        let Some(state) = &self.tracing_state else {
            return;
        };

        if var.0 >= state.var_count.0 {
            return;
        }

        state.set.borrow_mut().insert(var);
    }

    fn fresh(&mut self) -> InferTyVar {
        let var = InferTyVar(self.disjoint.len() as u32);
        self.disjoint.push(DisjointTyInferNode {
            root: Some(DisjointTyInferRoot::Floating(Vec::new())),
            observed_idx: None,
        });
        var
    }

    fn observe(&mut self, var: InferTyVar) -> ObservedTyInferVar {
        let observed_idx = &mut self.disjoint[var.0 as usize].observed_idx;

        if let Some(observed_idx) = *observed_idx {
            return observed_idx;
        }

        let observed_idx = *observed_idx.insert(self.next_observe_idx);
        self.next_observe_idx += 1;

        let root_var = self.disjoint.root_of(var.0 as usize);

        match self.disjoint[root_var].root.as_mut().unwrap() {
            DisjointTyInferRoot::Known(_) => {
                self.observed_reveal_order.push(observed_idx);
            }
            DisjointTyInferRoot::Floating(observed) => {
                observed.push(observed_idx);
            }
        }

        observed_idx
    }

    fn observed_reveal_order(&self) -> &[ObservedTyInferVar] {
        &self.observed_reveal_order
    }

    fn lookup(&self, var: InferTyVar) -> Result<Ty, FloatingInferVar<'_>> {
        let root_var = self.disjoint.root_of(var.0 as usize);

        match self.disjoint[root_var].root.as_ref().unwrap() {
            &DisjointTyInferRoot::Known(ty) => Ok(ty),
            DisjointTyInferRoot::Floating(observed_equivalent) => {
                self.mention_var_for_tracing(var);

                Err(FloatingInferVar {
                    root: InferTyVar(root_var as u32),
                    observed_equivalent,
                })
            }
        }
    }

    fn assign_floating_to_non_var(&mut self, var: InferTyVar, ty: Ty) {
        let root_idx = self.disjoint.root_of(var.0 as usize);
        let root = self.disjoint[root_idx].root.as_mut().unwrap();

        let DisjointTyInferRoot::Floating(observed) = root else {
            unreachable!();
        };

        self.observed_reveal_order.extend_from_slice(observed);
        *root = DisjointTyInferRoot::Known(ty);
    }

    fn union_unrelated_floating(&mut self, lhs: InferTyVar, rhs: InferTyVar) {
        let lhs_root = self.disjoint.root_of(lhs.0 as usize);
        let rhs_root = self.disjoint.root_of(rhs.0 as usize);

        if lhs_root == rhs_root {
            return;
        }

        let lhs_root = self.disjoint[lhs_root].root.take().unwrap();
        let rhs_root = self.disjoint[rhs_root].root.take().unwrap();

        let (
            DisjointTyInferRoot::Floating(mut lhs_observed),
            DisjointTyInferRoot::Floating(mut rhs_observed),
        ) = (lhs_root, rhs_root)
        else {
            unreachable!()
        };

        self.disjoint.join(lhs.0 as usize, rhs.0 as usize);

        let new_root = self.disjoint.root_of(lhs.0 as usize);
        let new_root = &mut self.disjoint[new_root].root;

        debug_assert!(new_root.is_none());

        lhs_observed.append(&mut rhs_observed);

        *new_root = Some(DisjointTyInferRoot::Floating(lhs_observed));
    }
}

// === ReInferTracker === //

#[derive(Debug, Clone)]
struct ReInferTracker {
    /// The set of universal region variables we're tracking.
    universals: IndexVec<UniversalReVar, TrackedUniversal>,

    /// A map from `ReInferIndex` (which represents either the `'gc` region, a tracked inference
    /// region, or a tracked universal region) to the actual region being represented.
    tracked_any: IndexVec<AnyReIndex, TrackedAny>,

    /// The set of all unified pairs to avoid duplicates.
    unified_pairs: FxHashSet<(AnyReIndex, AnyReIndex)>,
}

define_index_type! {
    struct AnyReIndex = u32;
}

impl AnyReIndex {
    const GC: Self = Self { _raw: 0 };
}

#[derive(Debug, Clone)]
struct TrackedUniversal {
    index: AnyReIndex,
    outlives: BitSet,
    src_info: UniversalReVarSourceInfo,
}

#[derive(Debug, Clone)]
struct TrackedAny {
    kind: TrackedAnyKind,
    outlived_by: SmallVec<[AnyReIndex; 1]>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
enum TrackedAnyKind {
    Gc,
    Inference,
    Universal(UniversalReVar),
}

impl Default for ReInferTracker {
    fn default() -> Self {
        Self {
            universals: IndexVec::default(),
            tracked_any: IndexVec::from_iter([TrackedAny {
                kind: TrackedAnyKind::Gc,
                outlived_by: SmallVec::new(),
            }]),
            unified_pairs: FxHashSet::default(),
        }
    }
}

impl ReInferTracker {
    fn fresh_infer(&mut self) -> InferReVar {
        let var = InferReVar(self.tracked_any.next_idx().raw());

        self.tracked_any.push(TrackedAny {
            kind: TrackedAnyKind::Inference,
            outlived_by: SmallVec::new(),
        });

        var
    }

    fn fresh_universal(&mut self, src_info: UniversalReVarSourceInfo) -> UniversalReVar {
        let index = self.tracked_any.push(TrackedAny {
            kind: TrackedAnyKind::Universal(self.universals.next_idx()),
            outlived_by: SmallVec::new(),
        });

        let mut outlives = BitSet::new();
        outlives.insert(index.index());

        self.universals.push(TrackedUniversal {
            index,
            outlives,
            src_info,
        })
    }

    fn lookup_universal_src_info(&self, var: UniversalReVar) -> UniversalReVarSourceInfo {
        self.universals[var].src_info
    }

    fn region_to_idx(&mut self, re: Re) -> Option<AnyReIndex> {
        match re {
            Re::Gc => Some(AnyReIndex::GC),
            Re::UniversalVar(universal) => Some(self.universals[universal].index),
            Re::InferVar(idx) => Some(AnyReIndex::from_raw(idx.0)),
            Re::SigInfer | Re::SigGeneric(_) | Re::Erased => unreachable!(),
            Re::Error(_) => None,
        }
    }

    fn unify(&mut self, lhs: Re, rhs: Re, mut offenses: Option<&mut Vec<ReAndReUnifyOffense>>) {
        if lhs == rhs {
            return;
        }

        let (Some(lhs), Some(rhs)) = (self.region_to_idx(lhs), self.region_to_idx(rhs)) else {
            return;
        };

        // Ensure that we don't perform a relation more than once.
        if !self.unified_pairs.insert((lhs, rhs)) {
            return;
        }

        // Record the outlives constraint.
        self.tracked_any[rhs].outlived_by.push(lhs);

        // For every universal region, update the outlives graph.
        for universal in self.universals.indices() {
            if !self.universals[universal].outlives.contains(rhs.index()) {
                continue;
            }

            if self.universals[universal].outlives.contains(lhs.index()) {
                continue;
            }

            let mut dfs_stack = vec![lhs];

            while let Some(top) = dfs_stack.pop() {
                self.universals[universal].outlives.insert(top.index());

                let offending_re = match self.tracked_any[top].kind {
                    TrackedAnyKind::Gc => Some(Re::Gc),
                    TrackedAnyKind::Inference => None,
                    TrackedAnyKind::Universal(var) => Some(Re::UniversalVar(var)),
                };

                if let Some(offenses) = &mut offenses
                    && let Some(offending_re) = offending_re
                {
                    offenses.push(ReAndReUnifyOffense {
                        universal,
                        forced_to_outlive: offending_re,
                    });
                }

                for &outlived_by in &self.tracked_any[top].outlived_by {
                    if self.universals[universal]
                        .outlives
                        .contains(outlived_by.index())
                    {
                        continue;
                    }

                    dfs_stack.push(outlived_by);
                }
            }
        }
    }
}
