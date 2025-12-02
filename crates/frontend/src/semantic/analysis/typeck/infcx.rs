use crate::{
    base::{ErrorGuaranteed, Session, arena::Obj},
    semantic::{
        analysis::{
            CoherenceMap, TyCtxt, TyFolder, TyFolderInfallible, TyVisitor, TyVisitorUnspanned,
            TyVisitorWalk,
        },
        syntax::{
            InferReVar, InferTyVar, Mutability, Re, ReVariance, RegionGeneric, RelationMode,
            SpannedRe, SpannedTraitClauseList, SpannedTraitClauseView, SpannedTraitParam,
            SpannedTraitParamView, SpannedTy, SpannedTyOrReView, SpannedTyView, Ty, TyKind,
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
    pub origin_lhs: SpannedTy,
    pub origin_rhs: SpannedTy,
    pub culprits: Vec<TyAndTyRelateCulprit>,
}

#[derive(Debug, Clone)]
pub enum TyAndTyRelateCulprit {
    Types(SpannedTy, SpannedTy),
    Regions(Box<ReAndReRelateError>),
    ClauseLists(SpannedTraitClauseList, SpannedTraitClauseList),
    Params(SpannedTraitParam, SpannedTraitParam),
    RecursiveType(InferTyOccursError),
}

#[derive(Debug, Clone)]
pub struct ReAndReRelateError {
    pub lhs: SpannedRe,
    pub rhs: SpannedRe,
    pub offenses: Vec<ReAndReRelateOffense>,
}

#[derive(Debug, Clone)]
pub struct ReAndReRelateOffense {
    pub universal: Obj<RegionGeneric>,
    pub forced_to_outlive: Re,
}

#[derive(Debug, Clone)]
pub struct TyAndReRelateError {
    pub lhs: SpannedTy,
    pub rhs: SpannedRe,
    pub culprits: Vec<Box<ReAndReRelateError>>,
}

#[derive(Debug, Clone)]
pub struct InferTyOccursError {
    pub var: InferTyVar,
    pub occurs_in: Ty,
}

// === InferCx === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum InferCxMode {
    RegionBlind,
    RegionAware,
}

/// A type inference context for solving type equations of the form...
///
/// - `Region: Region`
/// - `Type = Type`
/// - `Type: Clauses`
///
/// Using the above equations, it can also solve equations of the form...
///
/// - `Clauses entail Clauses`
/// - `is-well-formed Type`
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
#[derive(Debug, Clone)]
pub struct InferCx<'tcx> {
    tcx: &'tcx TyCtxt,
    coherence: &'tcx CoherenceMap,
    types: TyInferTracker,
    regions: Option<ReInferTracker>,
}

impl<'tcx> InferCx<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, coherence: &'tcx CoherenceMap, mode: InferCxMode) -> Self {
        Self {
            tcx,
            coherence,
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

    pub fn coherence(&self) -> &'tcx CoherenceMap {
        self.coherence
    }

    pub fn mode(&self) -> InferCxMode {
        if self.regions.is_some() {
            InferCxMode::RegionAware
        } else {
            InferCxMode::RegionBlind
        }
    }

    pub fn fresh_ty(&mut self) -> Ty {
        self.tcx().intern_ty(TyKind::InferVar(self.types.fresh()))
    }

    pub fn peel_ty_var(&self, ty: SpannedTy) -> SpannedTy {
        let tcx = self.tcx();

        match ty.view(tcx) {
            SpannedTyView::InferVar(var) => {
                if let Ok(var) = self.types.lookup(var) {
                    SpannedTy::new_maybe_saturated(var, ty.own_span(), tcx)
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
        lhs: SpannedRe,
        rhs: SpannedRe,
        mode: RelationMode,
    ) -> Result<(), Box<ReAndReRelateError>> {
        let Some(regions) = &mut self.regions else {
            return Ok(());
        };

        let tcx = self.tcx;

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
            if lhs.value == rhs.value {
                continue;
            }

            match (lhs.view(tcx), rhs.view(tcx)) {
                (Re::Erased, _)
                | (_, Re::Erased)
                | (Re::ExplicitInfer, _)
                | (_, Re::ExplicitInfer) => unreachable!(),
                _ => {
                    fork.relate(lhs.value, rhs.value, self.tcx, &mut offenses);
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
        lhs: SpannedTy,
        rhs: SpannedTy,
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
        lhs: SpannedTy,
        rhs: SpannedTy,
        culprits: &mut Vec<TyAndTyRelateCulprit>,
        mode: RelationMode,
    ) {
        let tcx = self.tcx();
        let s = self.session();

        if lhs.value == rhs.value {
            // The types are compatible!
            return;
        }

        match (lhs.view(tcx), rhs.view(tcx)) {
            (SpannedTyView::This, _)
            | (_, SpannedTyView::This)
            | (SpannedTyView::ExplicitInfer, _)
            | (_, SpannedTyView::ExplicitInfer) => {
                unreachable!()
            }
            (
                SpannedTyView::Reference(lhs_re, lhs_muta, lhs_pointee),
                SpannedTyView::Reference(rhs_re, rhs_muta, rhs_pointee),
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
            (SpannedTyView::Adt(lhs), SpannedTyView::Adt(rhs))
                if lhs.value.def == rhs.value.def =>
            {
                let lhs = lhs.view(tcx);
                let rhs = rhs.view(tcx);

                for (lhs, rhs) in lhs.params.iter(tcx).zip(rhs.params.iter(tcx)) {
                    match (lhs.view(tcx), rhs.view(tcx)) {
                        (SpannedTyOrReView::Re(lhs), SpannedTyOrReView::Re(rhs)) => {
                            if let Err(err) = self.relate_re_and_re(lhs, rhs, mode) {
                                culprits.push(TyAndTyRelateCulprit::Regions(err));
                            }
                        }
                        (SpannedTyOrReView::Ty(lhs), SpannedTyOrReView::Ty(rhs)) => {
                            // TODO: variance
                            self.relate_ty_and_ty_inner(lhs, rhs, culprits, mode);
                        }
                        _ => unreachable!(),
                    }
                }
            }
            (SpannedTyView::Trait(lhs), SpannedTyView::Trait(rhs)) => {
                self.relate_dyn_trait_clauses_inner(lhs, rhs, culprits, mode);
            }
            (SpannedTyView::Tuple(lhs), SpannedTyView::Tuple(rhs)) if lhs.len(s) == rhs.len(s) => {
                for (lhs, rhs) in lhs.iter(tcx).zip(rhs.iter(tcx)) {
                    self.relate_ty_and_ty_inner(lhs, rhs, culprits, mode);
                }
            }
            (SpannedTyView::InferVar(lhs_var), SpannedTyView::InferVar(rhs_var)) => {
                match (self.types.lookup(lhs_var), self.types.lookup(rhs_var)) {
                    (Ok(lhs_ty), Ok(rhs_ty)) => {
                        self.relate_ty_and_ty_inner(
                            SpannedTy::new_maybe_saturated(lhs_ty, lhs.own_span(), tcx),
                            SpannedTy::new_maybe_saturated(rhs_ty, rhs.own_span(), tcx),
                            culprits,
                            mode,
                        );
                    }
                    (Ok(lhs_ty), Err(rhs_root)) => {
                        if let Err(err) = self.relate_var_and_ty(rhs_root, lhs_ty) {
                            culprits.push(TyAndTyRelateCulprit::RecursiveType(err));
                        }
                    }
                    (Err(lhs_root), Ok(rhs_ty)) => {
                        if let Err(err) = self.relate_var_and_ty(lhs_root, rhs_ty) {
                            culprits.push(TyAndTyRelateCulprit::RecursiveType(err));
                        }
                    }
                    (Err(_), Err(_)) => {
                        // Cannot fail occurs check because neither type structurally includes the
                        // other.
                        self.types.union_unrelated(lhs_var, rhs_var);
                    }
                }
            }
            (SpannedTyView::InferVar(lhs_var), _) => {
                if let Ok(known_lhs) = self.types.lookup(lhs_var) {
                    self.relate_ty_and_ty_inner(
                        SpannedTy::new_maybe_saturated(known_lhs, lhs.own_span(), tcx),
                        rhs,
                        culprits,
                        mode,
                    );
                } else if let Err(err) = self.relate_var_and_ty(lhs_var, rhs.value) {
                    culprits.push(TyAndTyRelateCulprit::RecursiveType(err));
                }
            }
            (_, SpannedTyView::InferVar(rhs_var)) => {
                if let Ok(known_rhs) = self.types.lookup(rhs_var) {
                    self.relate_ty_and_ty_inner(
                        lhs,
                        SpannedTy::new_maybe_saturated(known_rhs, rhs.own_span(), tcx),
                        culprits,
                        mode,
                    );
                } else if let Err(err) = self.relate_var_and_ty(rhs_var, lhs.value) {
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

    pub fn relate_var_and_ty(
        &mut self,
        lhs_var_root: InferTyVar,
        rhs_ty: Ty,
    ) -> Result<(), InferTyOccursError> {
        debug_assert!(self.types.lookup(lhs_var_root) == Err(lhs_var_root));

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
                        Err(other_root) => {
                            if self.reject == other_root {
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

        self.types.assign(lhs_var_root, rhs_ty);

        Ok(())
    }

    fn relate_dyn_trait_clauses_inner(
        &mut self,
        lhs: SpannedTraitClauseList,
        rhs: SpannedTraitClauseList,
        culprits: &mut Vec<TyAndTyRelateCulprit>,
        mode: RelationMode,
    ) {
        let s = self.session();
        let tcx = self.tcx();

        if lhs.len(s) != rhs.len(s) {
            culprits.push(TyAndTyRelateCulprit::ClauseLists(lhs, rhs));
            return;
        }

        for (lhs_clause, rhs_clause) in lhs.iter(tcx).zip(rhs.iter(tcx)) {
            match (lhs_clause.view(tcx), rhs_clause.view(tcx)) {
                (SpannedTraitClauseView::Outlives(lhs), SpannedTraitClauseView::Outlives(rhs)) => {
                    // Technically, `MyTrait + 'a + 'b: 'c` could imply either `'a: 'c` or
                    // `'b: 'c`, meaning that relating both would be unnecessary but this
                    // logic will produce constraints for both. This isn't a problem because
                    // we only ever lower trait objects with *exactly one* outlives
                    // constraint.
                    if let Err(err) = self.relate_re_and_re(lhs, rhs, mode) {
                        culprits.push(TyAndTyRelateCulprit::Regions(err));
                    }
                }
                (SpannedTraitClauseView::Trait(lhs), SpannedTraitClauseView::Trait(rhs))
                    if lhs.value.def == rhs.value.def =>
                {
                    for (lhs, rhs) in lhs
                        .view(tcx)
                        .params
                        .iter(tcx)
                        .zip(rhs.view(tcx).params.iter(tcx))
                    {
                        match (lhs.view(tcx), rhs.view(tcx)) {
                            (
                                SpannedTraitParamView::Equals(lhs),
                                SpannedTraitParamView::Equals(rhs),
                            ) => match (lhs.view(tcx), rhs.view(tcx)) {
                                (SpannedTyOrReView::Re(lhs), SpannedTyOrReView::Re(rhs)) => {
                                    if let Err(err) =
                                        self.relate_re_and_re(lhs, rhs, RelationMode::Equate)
                                    {
                                        culprits.push(TyAndTyRelateCulprit::Regions(err));
                                    }
                                }
                                (SpannedTyOrReView::Ty(lhs), SpannedTyOrReView::Ty(rhs)) => {
                                    self.relate_ty_and_ty_inner(
                                        lhs,
                                        rhs,
                                        culprits,
                                        RelationMode::Equate,
                                    );
                                }
                                _ => unreachable!(),
                            },
                            (
                                SpannedTraitParamView::Unspecified(lhs),
                                SpannedTraitParamView::Unspecified(rhs),
                            ) => {
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

    pub fn relate_ty_and_re(
        &mut self,
        lhs: SpannedTy,
        rhs: SpannedRe,
    ) -> Result<(), Box<TyAndReRelateError>> {
        let mut fork = self.clone();
        let mut culprits = Vec::new();

        fork.relate_ty_and_re_inner(lhs, rhs, &mut culprits);

        if !culprits.is_empty() {
            return Err(Box::new(TyAndReRelateError { lhs, rhs, culprits }));
        }

        Ok(())
    }

    #[expect(clippy::vec_box)]
    fn relate_ty_and_re_inner(
        &mut self,
        lhs: SpannedTy,
        rhs: SpannedRe,
        culprits: &mut Vec<Box<ReAndReRelateError>>,
    ) {
        let tcx = self.tcx();

        match lhs.view(tcx) {
            SpannedTyView::This | SpannedTyView::ExplicitInfer => unreachable!(),
            SpannedTyView::FnDef(_) | SpannedTyView::Simple(_) | SpannedTyView::Error(_) => {
                // (trivial)
            }
            SpannedTyView::Reference(lhs, _muta, _pointee) => {
                // No need to relate the pointee since WF checks already ensure that it outlives
                // `lhs`.
                if let Err(err) = self.relate_re_and_re(lhs, rhs, RelationMode::LhsOntoRhs) {
                    culprits.push(err);
                }
            }
            SpannedTyView::Adt(lhs) => {
                // ADTs are bounded by which regions they mention.
                for lhs in lhs.view(tcx).params.iter(tcx) {
                    match lhs.view(tcx) {
                        SpannedTyOrReView::Re(lhs) => {
                            if let Err(err) =
                                self.relate_re_and_re(lhs, rhs, RelationMode::LhsOntoRhs)
                            {
                                culprits.push(err);
                            }
                        }
                        SpannedTyOrReView::Ty(lhs) => {
                            self.relate_ty_and_re_inner(lhs, rhs, culprits);
                        }
                    }
                }
            }
            SpannedTyView::Trait(lhs) => {
                for lhs in lhs.iter(tcx) {
                    match lhs.view(tcx) {
                        SpannedTraitClauseView::Outlives(lhs) => {
                            // There is guaranteed to be exactly one outlives constraint for a trait
                            // object so relating these constraints is sufficient to ensure that the
                            // object outlives the `rhs`.
                            if let Err(err) =
                                self.relate_re_and_re(lhs, rhs, RelationMode::LhsOntoRhs)
                            {
                                culprits.push(err);
                            }
                        }
                        SpannedTraitClauseView::Trait(_) => {
                            // (if the outlives constraint says the trait is okay, it's okay)
                        }
                    }
                }
            }
            SpannedTyView::Tuple(lhs) => {
                for lhs in lhs.iter(tcx) {
                    self.relate_ty_and_re_inner(lhs, rhs, culprits);
                }
            }
            SpannedTyView::Universal(_) => todo!(),
            SpannedTyView::InferVar(inf_lhs) => {
                if let Ok(inf_lhs) = self.types.lookup(inf_lhs) {
                    self.relate_ty_and_re_inner(
                        SpannedTy::new_maybe_saturated(inf_lhs, lhs.own_span(), tcx),
                        rhs,
                        culprits,
                    );
                } else {
                    // Defer the check.
                    todo!();
                }
            }
        }
    }

    pub fn wf_ty(&mut self, ty: SpannedTy) {
        todo!()
    }
}

// === TyInferTracker === //

#[derive(Debug, Clone, Default)]
pub struct TyInferTracker {
    disjoint: DisjointSetVec<Option<Ty>>,
}

impl TyInferTracker {
    pub fn fresh(&mut self) -> InferTyVar {
        let var = InferTyVar(self.disjoint.len() as u32);
        self.disjoint.push(None);
        var
    }

    pub fn lookup(&self, var: InferTyVar) -> Result<Ty, InferTyVar> {
        let root_var = self.disjoint.root_of(var.0 as usize);

        self.disjoint[root_var].ok_or(InferTyVar(root_var as u32))
    }

    pub fn assign(&mut self, var: InferTyVar, ty: Ty) {
        let root_idx = self.disjoint.root_of(var.0 as usize);
        let root = &mut self.disjoint[root_idx];

        debug_assert!(root.is_none());

        *root = Some(ty);
    }

    pub fn union_unrelated(&mut self, lhs: InferTyVar, rhs: InferTyVar) {
        let lhs_ty = self.lookup(lhs).ok();
        let rhs_ty = self.lookup(rhs).ok();

        debug_assert!(lhs_ty.is_none() && rhs_ty.is_none());

        self.disjoint.join(lhs.0 as usize, rhs.0 as usize);
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
            Err(normalized) => Ok(match self.mode {
                UnboundVarHandlingMode::Error(error) => self.tcx().intern_ty(TyKind::Error(error)),
                UnboundVarHandlingMode::NormalizeToRoot => {
                    self.tcx().intern_ty(TyKind::InferVar(normalized))
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

// === ReInferTracker === //

#[derive(Debug, Clone)]
pub struct ReInferTracker {
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
    pub fn fresh(&mut self) -> InferReVar {
        let var = InferReVar(self.tracked_any.next_idx().raw());

        self.tracked_any.push(TrackedAny {
            kind: TrackedAnyKind::Inference,
            outlived_by: SmallVec::new(),
        });

        var
    }

    fn region_to_idx(&mut self, re: Re, tcx: &TyCtxt) -> AnyReIndex {
        let s = &tcx.session;

        match re {
            Re::Gc => AnyReIndex::GC,
            Re::Universal(generic) => {
                let new_universal_idx = self.tracked_universals.len();

                match self.tracked_universals.entry(generic) {
                    indexmap::map::Entry::Occupied(entry) => entry.get().index,
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
                            let SpannedTraitClauseView::Outlives(outlives) = outlives.view(tcx)
                            else {
                                unreachable!()
                            };

                            let rhs = self.region_to_idx(outlives.value, tcx);

                            let mut errors = Vec::new();
                            self.relate_inner(index, rhs, Some(&mut errors));
                        }

                        index
                    }
                }
            }
            Re::InferVar(idx) => AnyReIndex::from_raw(idx.0),
            Re::ExplicitInfer | Re::Erased => unreachable!(),
        }
    }

    pub fn relate(
        &mut self,
        lhs: Re,
        rhs: Re,
        tcx: &TyCtxt,
        offenses: &mut Vec<ReAndReRelateOffense>,
    ) {
        if lhs == rhs {
            return;
        }

        let lhs = self.region_to_idx(lhs, tcx);
        let rhs = self.region_to_idx(rhs, tcx);

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
