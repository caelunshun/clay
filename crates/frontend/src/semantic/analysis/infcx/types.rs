use crate::{
    base::{ErrorGuaranteed, Session, arena::Obj},
    semantic::{
        analysis::{
            TyCtxt, TyFolder, TyFolderInfallible, TyVisitor, TyVisitorUnspanned, TyVisitorWalk,
        },
        syntax::{
            InferReVar, InferTyVar, Mutability, Re, ReVariance, RegionGeneric, RelationMode,
            SpannedTy, SpannedTyView, TraitClause, TraitClauseList, TraitParam, Ty, TyKind, TyOrRe,
        },
    },
    utils::hash::{FxHashSet, FxIndexMap},
};
use bit_set::BitSet;
use disjoint::DisjointSetVec;
use index_vec::{IndexVec, define_index_type};
use smallvec::SmallVec;
use std::{convert::Infallible, ops::ControlFlow};

// === Errors === //

#[derive(Debug, Clone)]
pub struct TyAndTyRelateError {
    pub origin_lhs: Ty,
    pub origin_rhs: Ty,
    pub culprits: Vec<TyAndTyRelateCulprit>,
}

#[derive(Debug, Clone)]
pub enum TyAndTyRelateCulprit {
    Types(Ty, Ty),
    Regions(Box<ReAndReRelateError>),
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
pub struct ReAndReRelateError {
    pub lhs: Re,
    pub rhs: Re,
    pub offenses: Vec<ReAndReRelateOffense>,
}

#[derive(Debug, Clone)]
pub struct ReAndReRelateOffense {
    pub universal: Obj<RegionGeneric>,
    pub forced_to_outlive: Re,
}

// === InferCx === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum InferCxMode {
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
/// those obligations, you'll need an [`ObligationCx`](super::ObligationCx).
#[derive(Debug, Clone)]
pub struct InferCx<'tcx> {
    tcx: &'tcx TyCtxt,
    types: TyInferTracker,
    regions: Option<ReInferTracker>,
}

define_index_type! {
    pub struct ObservedTyVar = u32;
}

#[derive(Debug, Copy, Clone)]
pub struct FloatingInferVar<'a> {
    pub root: InferTyVar,
    pub observed_equivalent: &'a [ObservedTyVar],
}

impl<'tcx> InferCx<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, mode: InferCxMode) -> Self {
        Self {
            tcx,
            types: TyInferTracker::default(),
            regions: match mode {
                InferCxMode::RegionBlind => None,
                InferCxMode::RegionAware => Some(ReInferTracker::default()),
            },
        }
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    pub fn session(&self) -> &'tcx Session {
        &self.tcx.session
    }

    pub fn mode(&self) -> InferCxMode {
        if self.regions.is_some() {
            InferCxMode::RegionAware
        } else {
            InferCxMode::RegionBlind
        }
    }

    pub fn fresh_ty_var(&mut self) -> InferTyVar {
        self.types.fresh()
    }

    pub fn fresh_ty(&mut self) -> Ty {
        self.tcx().intern_ty(TyKind::InferVar(self.fresh_ty_var()))
    }

    pub fn observe_ty_var(&mut self, var: InferTyVar) -> ObservedTyVar {
        self.types.observe(var)
    }

    pub fn observed_reveal_order(&self) -> &[ObservedTyVar] {
        self.types.observed_reveal_order()
    }

    pub fn lookup_ty_var(&self, var: InferTyVar) -> Result<Ty, FloatingInferVar<'_>> {
        self.types.lookup(var)
    }

    pub fn peel_ty_var(&self, ty: Ty) -> Ty {
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

    pub fn fresh_re(&mut self) -> Re {
        if let Some(regions) = &mut self.regions {
            Re::InferVar(regions.fresh())
        } else {
            Re::Erased
        }
    }

    pub fn relate_re_and_re(
        &mut self,
        lhs: Re,
        rhs: Re,
        mode: RelationMode,
    ) -> Result<(), Box<ReAndReRelateError>> {
        let Some(regions) = &mut self.regions else {
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
                (Re::Erased, _)
                | (_, Re::Erased)
                | (Re::ExplicitInfer, _)
                | (_, Re::ExplicitInfer) => unreachable!(),
                _ => {
                    fork.relate(lhs, rhs, self.tcx, &mut offenses);
                }
            }
        }

        if !offenses.is_empty() {
            return Err(Box::new(ReAndReRelateError { lhs, rhs, offenses }));
        }

        *regions = fork;

        Ok(())
    }

    /// Relates two types such that they match. The `mode` specifies how the regions inside the
    /// types should be related. For example, if it is `RelationMode::LhsOntoRhs`, relating
    /// `&'0 u32` and `&'1 u32` will result in the region relation `'0: '1`.
    pub fn relate_ty_and_ty(
        &mut self,
        lhs: Ty,
        rhs: Ty,
        mode: RelationMode,
    ) -> Result<(), Box<TyAndTyRelateError>> {
        let mut fork = self.clone();
        let mut culprits = Vec::new();

        fork.relate_ty_and_ty_inner(lhs, rhs, &mut culprits, mode);

        if !culprits.is_empty() {
            return Err(Box::new(TyAndTyRelateError {
                origin_lhs: lhs,
                origin_rhs: rhs,
                culprits,
            }));
        }

        *self = fork;

        Ok(())
    }

    fn relate_ty_and_ty_inner(
        &mut self,
        lhs: Ty,
        rhs: Ty,
        culprits: &mut Vec<TyAndTyRelateCulprit>,
        mode: RelationMode,
    ) {
        let s = self.session();

        if lhs == rhs {
            // The types are compatible!
            return;
        }

        match (*lhs.r(s), *rhs.r(s)) {
            (TyKind::This, _)
            | (_, TyKind::This)
            | (TyKind::ExplicitInfer, _)
            | (_, TyKind::ExplicitInfer) => {
                unreachable!()
            }
            (
                TyKind::Reference(lhs_re, lhs_muta, lhs_pointee),
                TyKind::Reference(rhs_re, rhs_muta, rhs_pointee),
            ) if lhs_muta == rhs_muta => {
                if let Err(err) = self.relate_re_and_re(lhs_re, rhs_re, mode) {
                    culprits.push(TyAndTyRelateCulprit::Regions(err));
                }

                let variance = match lhs_muta {
                    Mutability::Mut => ReVariance::Invariant,
                    Mutability::Not => ReVariance::Covariant,
                };

                self.relate_ty_and_ty_inner(
                    lhs_pointee,
                    rhs_pointee,
                    culprits,
                    mode.with_variance(variance),
                );
            }
            (TyKind::Adt(lhs), TyKind::Adt(rhs)) if lhs.def == rhs.def => {
                for (&lhs, &rhs) in lhs.params.r(s).iter().zip(rhs.params.r(s)) {
                    match (lhs, rhs) {
                        (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                            if let Err(err) = self.relate_re_and_re(lhs, rhs, mode) {
                                culprits.push(TyAndTyRelateCulprit::Regions(err));
                            }
                        }
                        (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                            // TODO: variance
                            self.relate_ty_and_ty_inner(lhs, rhs, culprits, mode);
                        }
                        _ => unreachable!(),
                    }
                }
            }
            (TyKind::Trait(lhs), TyKind::Trait(rhs)) => {
                self.relate_dyn_trait_clauses_inner(lhs, rhs, culprits, mode);
            }
            (TyKind::Tuple(lhs), TyKind::Tuple(rhs)) if lhs.r(s).len() == rhs.r(s).len() => {
                for (&lhs, &rhs) in lhs.r(s).iter().zip(rhs.r(s)) {
                    self.relate_ty_and_ty_inner(lhs, rhs, culprits, mode);
                }
            }
            (TyKind::InferVar(lhs_var), TyKind::InferVar(rhs_var)) => {
                match (self.types.lookup(lhs_var), self.types.lookup(rhs_var)) {
                    (Ok(lhs_ty), Ok(rhs_ty)) => {
                        self.relate_ty_and_ty_inner(lhs_ty, rhs_ty, culprits, mode);
                    }
                    (Ok(lhs_ty), Err(rhs_floating)) => {
                        if let Err(err) = self.relate_var_and_non_var_ty(rhs_floating.root, lhs_ty)
                        {
                            culprits.push(TyAndTyRelateCulprit::RecursiveType(err));
                        }
                    }
                    (Err(lhs_floating), Ok(rhs_ty)) => {
                        if let Err(err) = self.relate_var_and_non_var_ty(lhs_floating.root, rhs_ty)
                        {
                            culprits.push(TyAndTyRelateCulprit::RecursiveType(err));
                        }
                    }
                    (Err(_), Err(_)) => {
                        // Cannot fail occurs check because neither type structurally includes the
                        // other.
                        self.types.union_unrelated_floating(lhs_var, rhs_var);
                    }
                }
            }
            (TyKind::InferVar(lhs_var), _) => {
                if let Ok(known_lhs) = self.types.lookup(lhs_var) {
                    self.relate_ty_and_ty_inner(known_lhs, rhs, culprits, mode);
                } else if let Err(err) = self.relate_var_and_non_var_ty(lhs_var, rhs) {
                    culprits.push(TyAndTyRelateCulprit::RecursiveType(err));
                }
            }
            (_, TyKind::InferVar(rhs_var)) => {
                if let Ok(known_rhs) = self.types.lookup(rhs_var) {
                    self.relate_ty_and_ty_inner(lhs, known_rhs, culprits, mode);
                } else if let Err(err) = self.relate_var_and_non_var_ty(rhs_var, lhs) {
                    culprits.push(TyAndTyRelateCulprit::RecursiveType(err));
                }
            }
            // Omissions okay because of intern equality fast-path:
            //
            // - `(Simple, Simple)`
            // - `(FnDef, FnDef)`
            // - `(Universal, Universal)`
            //
            // TODO: Check exhaustiveness automatically.
            _ => {
                culprits.push(TyAndTyRelateCulprit::Types(lhs, rhs));
            }
        }
    }

    fn relate_var_and_non_var_ty(
        &mut self,
        lhs_var_root: InferTyVar,
        rhs_ty: Ty,
    ) -> Result<(), InferTyOccursError> {
        debug_assert_eq!(
            self.types.lookup(lhs_var_root).map_err(|v| v.root),
            Err(lhs_var_root),
        );

        struct OccursVisitor<'a, 'tcx> {
            icx: &'a InferCx<'tcx>,
            reject: InferTyVar,
        }

        impl<'tcx> TyVisitor<'tcx> for OccursVisitor<'_, 'tcx> {
            type Break = ();

            fn tcx(&self) -> &'tcx TyCtxt {
                self.icx.tcx()
            }

            fn visit_spanned_ty(&mut self, ty: SpannedTy) -> ControlFlow<Self::Break> {
                if let SpannedTyView::InferVar(var) = ty.view(self.tcx()) {
                    match self.icx.types.lookup(var) {
                        Ok(resolved) => self.visit_ty(resolved),
                        Err(other_floating) => {
                            if self.reject == other_floating.root {
                                ControlFlow::Break(())
                            } else {
                                ControlFlow::Continue(())
                            }
                        }
                    }
                } else {
                    self.walk_ty(ty)
                }
            }
        }

        let does_occur = OccursVisitor {
            icx: self,
            reject: lhs_var_root,
        }
        .visit_ty(rhs_ty)
        .is_break();

        if does_occur {
            let occurs_in = InfTySubstitutor::new(self, UnboundVarHandlingMode::NormalizeToRoot)
                .fold_ty(rhs_ty);

            return Err(InferTyOccursError {
                var: lhs_var_root,
                occurs_in,
            });
        }

        self.types.assign_floating_to_non_var(lhs_var_root, rhs_ty);

        Ok(())
    }

    fn relate_dyn_trait_clauses_inner(
        &mut self,
        lhs: TraitClauseList,
        rhs: TraitClauseList,
        culprits: &mut Vec<TyAndTyRelateCulprit>,
        mode: RelationMode,
    ) {
        let s = self.session();

        if lhs.r(s).len() != rhs.r(s).len() {
            culprits.push(TyAndTyRelateCulprit::ClauseLists(lhs, rhs));
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
                    if let Err(err) = self.relate_re_and_re(lhs, rhs, mode) {
                        culprits.push(TyAndTyRelateCulprit::Regions(err));
                    }
                }
                (TraitClause::Trait(lhs), TraitClause::Trait(rhs)) if lhs.def == rhs.def => {
                    for (&lhs, &rhs) in lhs.params.r(s).iter().zip(rhs.params.r(s)) {
                        match (lhs, rhs) {
                            (TraitParam::Equals(lhs), TraitParam::Equals(rhs)) => {
                                match (lhs, rhs) {
                                    (TyOrRe::Re(lhs), TyOrRe::Re(rhs)) => {
                                        if let Err(err) =
                                            self.relate_re_and_re(lhs, rhs, RelationMode::Equate)
                                        {
                                            culprits.push(TyAndTyRelateCulprit::Regions(err));
                                        }
                                    }
                                    (TyOrRe::Ty(lhs), TyOrRe::Ty(rhs)) => {
                                        self.relate_ty_and_ty_inner(
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
                                self.relate_dyn_trait_clauses_inner(
                                    lhs,
                                    rhs,
                                    culprits,
                                    RelationMode::Equate,
                                );
                            }
                            _ => {
                                culprits.push(TyAndTyRelateCulprit::Params(lhs, rhs));
                            }
                        }
                    }
                }
                _ => {
                    culprits.push(TyAndTyRelateCulprit::ClauseLists(lhs, rhs));
                    return;
                }
            }
        }
    }
}

// === InfTySubstitutor === //

#[derive(Debug, Copy, Clone)]
pub struct InfTySubstitutor<'a, 'tcx> {
    infer_types: &'a TyInferTracker,
    tcx: &'tcx TyCtxt,
    mode: UnboundVarHandlingMode,
}

#[derive(Debug, Copy, Clone)]
pub enum UnboundVarHandlingMode {
    Error(ErrorGuaranteed),
    NormalizeToRoot,
    EraseToExplicitInfer,
    Panic,
}

impl<'a, 'tcx> InfTySubstitutor<'a, 'tcx> {
    pub fn new(icx: &'a InferCx<'tcx>, mode: UnboundVarHandlingMode) -> Self {
        Self {
            infer_types: &icx.types,
            tcx: icx.tcx,
            mode,
        }
    }
}

impl<'tcx> TyFolder<'tcx> for InfTySubstitutor<'_, 'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    fn try_fold_ty_infer_use(&mut self, var: InferTyVar) -> Result<Ty, Self::Error> {
        match self.infer_types.lookup(var) {
            Ok(v) => self.try_fold_ty(v),
            Err(floating) => Ok(match self.mode {
                UnboundVarHandlingMode::Error(error) => self.tcx().intern_ty(TyKind::Error(error)),
                UnboundVarHandlingMode::NormalizeToRoot => {
                    self.tcx().intern_ty(TyKind::InferVar(floating.root))
                }
                UnboundVarHandlingMode::EraseToExplicitInfer => {
                    self.tcx().intern_ty(TyKind::ExplicitInfer)
                }
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
    observed_reveal_order: Vec<ObservedTyVar>,
    next_observe_idx: ObservedTyVar,
}

#[derive(Debug, Clone)]
struct DisjointTyInferNode {
    root: Option<DisjointTyInferRoot>,
    observed_idx: Option<ObservedTyVar>,
}

#[derive(Debug, Clone)]
enum DisjointTyInferRoot {
    Known(Ty),
    Floating(Vec<ObservedTyVar>),
}

impl Default for TyInferTracker {
    fn default() -> Self {
        Self {
            disjoint: DisjointSetVec::new(),
            observed_reveal_order: Vec::new(),
            next_observe_idx: ObservedTyVar::from_usize(0),
        }
    }
}

impl TyInferTracker {
    fn fresh(&mut self) -> InferTyVar {
        let var = InferTyVar(self.disjoint.len() as u32);
        self.disjoint.push(DisjointTyInferNode {
            root: Some(DisjointTyInferRoot::Floating(Vec::new())),
            observed_idx: None,
        });
        var
    }

    fn observe(&mut self, var: InferTyVar) -> ObservedTyVar {
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

    fn observed_reveal_order(&self) -> &[ObservedTyVar] {
        &self.observed_reveal_order
    }

    fn lookup(&self, var: InferTyVar) -> Result<Ty, FloatingInferVar<'_>> {
        let root_var = self.disjoint.root_of(var.0 as usize);

        match self.disjoint[root_var].root.as_ref().unwrap() {
            &DisjointTyInferRoot::Known(ty) => Ok(ty),
            DisjointTyInferRoot::Floating(observed_equivalent) => Err(FloatingInferVar {
                root: InferTyVar(root_var as u32),
                observed_equivalent,
            }),
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
    /// The set of universal regions we're tracking.
    tracked_universals: FxIndexMap<Obj<RegionGeneric>, TrackedUniversal>,

    /// A map from `ReInferIndex` (which represents either the `'gc` region, a tracked inference
    /// region, or a tracked universal region) to the actual region being represented.
    tracked_any: IndexVec<AnyReIndex, TrackedAny>,

    /// The set of all related pairs to avoid duplicates.
    related_pairs: FxHashSet<(AnyReIndex, AnyReIndex)>,
}

define_index_type! {
    struct AnyReIndex = u32;
}

impl AnyReIndex {
    const GC: Self = Self { _raw: 0 };
}

#[derive(Debug, Clone)]
struct TrackedUniversal {
    generic: Obj<RegionGeneric>,
    index: AnyReIndex,
    outlives: BitSet,
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
    Universal(u32),
}

impl Default for ReInferTracker {
    fn default() -> Self {
        Self {
            tracked_universals: FxIndexMap::default(),
            tracked_any: IndexVec::from_iter([TrackedAny {
                kind: TrackedAnyKind::Gc,
                outlived_by: SmallVec::new(),
            }]),
            related_pairs: FxHashSet::default(),
        }
    }
}

impl ReInferTracker {
    fn fresh(&mut self) -> InferReVar {
        let var = InferReVar(self.tracked_any.next_idx().raw());

        self.tracked_any.push(TrackedAny {
            kind: TrackedAnyKind::Inference,
            outlived_by: SmallVec::new(),
        });

        var
    }

    fn region_to_idx(&mut self, re: Re, tcx: &TyCtxt) -> Option<AnyReIndex> {
        let s = &tcx.session;

        match re {
            Re::Gc => Some(AnyReIndex::GC),
            Re::Universal(generic) => {
                let new_universal_idx = self.tracked_universals.len();

                match self.tracked_universals.entry(generic) {
                    indexmap::map::Entry::Occupied(entry) => Some(entry.get().index),
                    indexmap::map::Entry::Vacant(entry) => {
                        let index = self.tracked_any.push(TrackedAny {
                            kind: TrackedAnyKind::Universal(new_universal_idx as u32),
                            outlived_by: SmallVec::new(),
                        });

                        entry.insert(TrackedUniversal {
                            generic,
                            index,
                            outlives: {
                                let mut outlives = BitSet::new();
                                outlives.insert(index.index());
                                outlives
                            },
                        });

                        // Introduce universal outlives without reporting their relations to the
                        // user. That way, the only errors that can be produced originate from
                        // discovering new constraints beyond that.
                        for outlives in generic.r(s).clauses.iter(tcx) {
                            let TraitClause::Outlives(outlives) = outlives.value else {
                                unreachable!()
                            };

                            let Some(rhs) = self.region_to_idx(outlives, tcx) else {
                                continue;
                            };

                            let mut errors = Vec::new();
                            self.relate_inner(index, rhs, Some(&mut errors));
                        }

                        Some(index)
                    }
                }
            }
            Re::InferVar(idx) => Some(AnyReIndex::from_raw(idx.0)),
            Re::ExplicitInfer | Re::Erased => unreachable!(),
            Re::Error(_) => None,
        }
    }

    fn relate(&mut self, lhs: Re, rhs: Re, tcx: &TyCtxt, offenses: &mut Vec<ReAndReRelateOffense>) {
        if lhs == rhs {
            return;
        }

        let (Some(lhs), Some(rhs)) = (self.region_to_idx(lhs, tcx), self.region_to_idx(rhs, tcx))
        else {
            return;
        };

        self.relate_inner(lhs, rhs, Some(offenses));
    }

    fn relate_inner(
        &mut self,
        lhs: AnyReIndex,
        rhs: AnyReIndex,
        mut offenses: Option<&mut Vec<ReAndReRelateOffense>>,
    ) {
        // Ensure that we don't perform a relation more than once.
        if !self.related_pairs.insert((lhs, rhs)) {
            return;
        }

        // Record the outlives constraint.
        self.tracked_any[rhs].outlived_by.push(lhs);

        // For every universal region, update the outlives graph.
        for universal_idx in 0..self.tracked_universals.len() {
            if !self.tracked_universals[universal_idx]
                .outlives
                .contains(rhs.index())
            {
                continue;
            }

            if self.tracked_universals[universal_idx]
                .outlives
                .contains(lhs.index())
            {
                continue;
            }

            let generic = self.tracked_universals[universal_idx].generic;

            let mut dfs_stack = vec![lhs];

            while let Some(top) = dfs_stack.pop() {
                self.tracked_universals[universal_idx]
                    .outlives
                    .insert(top.index());

                let offending_re = match self.tracked_any[top].kind {
                    TrackedAnyKind::Gc => Some(Re::Gc),
                    TrackedAnyKind::Inference => None,
                    TrackedAnyKind::Universal(idx) => {
                        Some(Re::Universal(self.tracked_universals[idx as usize].generic))
                    }
                };

                if let Some(offenses) = &mut offenses
                    && let Some(offending_re) = offending_re
                {
                    offenses.push(ReAndReRelateOffense {
                        universal: generic,
                        forced_to_outlive: offending_re,
                    });
                }

                for &outlived_by in &self.tracked_any[top].outlived_by {
                    if self.tracked_universals[universal_idx]
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
