use crate::{
    base::Session,
    semantic::{
        analysis::TyCtxt,
        syntax::{
            InferTyVar, Re, RelationMode, SpannedRe, SpannedTraitClauseList,
            SpannedTraitClauseView, SpannedTraitParam, SpannedTraitParamView, SpannedTy,
            SpannedTyOrReView, SpannedTyView, Ty,
        },
    },
};
use disjoint::DisjointSetVec;

// === InferCx === //

#[derive(Debug, Clone)]
pub struct TyEquateError {
    pub origin_lhs: SpannedTy,
    pub origin_rhs: SpannedTy,
    pub culprits: Vec<TyEquateCulprit>,
}

#[derive(Debug, Copy, Clone)]
pub enum TyEquateCulprit {
    Types(SpannedTy, SpannedTy),
    ClauseLists(SpannedTraitClauseList, SpannedTraitClauseList),
    Params(SpannedTraitParam, SpannedTraitParam),
}

/// A type inference context for solving type equations of the form...
///
/// - `Region: Region`
/// - `Type = Type`
/// - `Type: Clauses`
/// - `Clauses entail Clauses`
///
/// This context has two modes: region unaware and region aware.
///
/// - The region unaware mode just solves for type equalities, making it ideal for a first pass of
///   type-checker where one just wants to solve for type inference variables. This process is
///   allowed to fail.
///
/// - The region aware mode can take the solved inference types and, after replacing all the erased
///   regions with fresh region inference variables, it can come up with a list of region
///   constraints that have to be true in order for the program to region-check.
///
/// If all the types checked with a region aware check were obtained by a prior region unaware
/// type-check, the inference methods will never return errors. Indeed, region relations will never
/// produce errors. After all, one can always solve all region errors by inferring everything to
/// `'gc`.
///
/// Region checking is done in a separate pass involving a region lattice obtained with
/// [`InferCx::make_region_lattice`], which allows a user to quickly determine...
///
/// - Whether some pair of regions (which could be universal, inferred, or `'gc`), are forced to
///   outlive or equal one another.
///
/// - The bounds required for a given universal region.
///
/// This second bit of information is useful for region checking. All region errors secretly involve
/// the relationship between a universal region and another region. For example, if an inference
/// finds that some region variable `'a` has to live for `'b` but `'a` doesn't have a `'a: 'b`
/// constraint, that would be an error. Likewise with `'a: 'gc` constraints.
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
#[derive(Debug)]
pub struct InferCx<'tcx> {
    tcx: &'tcx TyCtxt,
    ty_inf: TyInferCx,
    re_inf: Option<ReInferCx>,
}

impl<'tcx> InferCx<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, infer_regions: bool) -> Self {
        Self {
            tcx,
            ty_inf: TyInferCx::default(),
            re_inf: infer_regions.then(ReInferCx::default),
        }
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    pub fn session(&self) -> &'tcx Session {
        &self.tcx.session
    }

    pub fn fork(&mut self) {
        todo!()
    }

    pub fn apply(&mut self) {
        todo!()
    }

    pub fn reject(&mut self) {
        todo!();
    }

    pub fn make_region_lattice(&self) {
        todo!()
    }

    pub fn fresh_ty(&mut self) -> InferTyVar {
        self.ty_inf.fresh()
    }

    pub fn fresh_re(&mut self) -> Re {
        let Some(re_inf) = &mut self.re_inf else {
            return Re::Erased;
        };

        todo!()
    }

    pub fn relate_re(&mut self, lhs: SpannedRe, rhs: SpannedRe, mode: RelationMode) {
        let tcx = self.tcx();

        let Some(re_inf) = &mut self.re_inf else {
            return;
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
                    // TODO: Push it!
                }
            }
        }
    }

    /// Relates two types such that they match. The `mode` specifies how the regions inside the
    /// types should be related. For example, if it is `RelationMode::LhsOntoRhs`, relating
    /// `&'0 u32` and `&'1 u32` will result in the region relation `'0: '1`.
    pub fn relate_ty(
        &mut self,
        lhs: SpannedTy,
        rhs: SpannedTy,
        mode: RelationMode,
    ) -> Result<(), TyEquateError> {
        self.fork();

        let mut culprits = Vec::new();

        self.relate_ty_inner(lhs, rhs, &mut culprits, mode);

        if !culprits.is_empty() {
            self.reject();

            return Err(TyEquateError {
                origin_lhs: lhs,
                origin_rhs: rhs,
                culprits,
            });
        }

        self.apply();

        Ok(())
    }

    fn relate_ty_inner(
        &mut self,
        lhs: SpannedTy,
        rhs: SpannedTy,
        culprits: &mut Vec<TyEquateCulprit>,
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
                SpannedTyView::Reference(lhs_re, lhs_pointee),
                SpannedTyView::Reference(rhs_re, rhs_pointee),
            ) => {
                self.relate_re(lhs_re, rhs_re, mode);
                self.relate_ty_inner(lhs_pointee, rhs_pointee, culprits, mode);
            }
            (SpannedTyView::Adt(lhs), SpannedTyView::Adt(rhs))
                if lhs.value.def == rhs.value.def =>
            {
                let lhs = lhs.view(tcx);
                let rhs = rhs.view(tcx);

                for (lhs, rhs) in lhs.params.iter(s).zip(rhs.params.iter(s)) {
                    match (lhs.view(tcx), rhs.view(tcx)) {
                        (SpannedTyOrReView::Re(lhs), SpannedTyOrReView::Re(rhs)) => {
                            self.relate_re(lhs, rhs, mode);
                        }
                        (SpannedTyOrReView::Ty(lhs), SpannedTyOrReView::Ty(rhs)) => {
                            self.relate_ty_inner(lhs, rhs, culprits, mode);
                        }
                        _ => unreachable!(),
                    }
                }
            }
            (SpannedTyView::Trait(lhs), SpannedTyView::Trait(rhs)) => {
                self.relate_ty_trait_clauses_inner(lhs, rhs, culprits, mode);
            }
            (SpannedTyView::Tuple(lhs), SpannedTyView::Tuple(rhs)) if lhs.len(s) == rhs.len(s) => {
                for (lhs, rhs) in lhs.iter(s).zip(rhs.iter(s)) {
                    self.relate_ty_inner(lhs, rhs, culprits, mode);
                }
            }
            (SpannedTyView::InferVar(lhs_var), SpannedTyView::InferVar(rhs_var)) => {
                if let (Some(lhs_ty), Some(rhs_ty)) =
                    (self.ty_inf.lookup(lhs_var), self.ty_inf.lookup(rhs_var))
                {
                    // TODO: Saturating spanned types?
                    self.relate_ty_inner(
                        SpannedTy::new_unspanned(lhs_ty),
                        SpannedTy::new_unspanned(rhs_ty),
                        culprits,
                        mode,
                    );
                } else {
                    self.ty_inf.union(lhs_var, rhs_var);
                }
            }
            (SpannedTyView::InferVar(lhs_var), _) => {
                if let Some(known_lhs) = self.ty_inf.lookup(lhs_var) {
                    // TODO: Saturating spanned types?
                    self.relate_ty_inner(SpannedTy::new_unspanned(known_lhs), rhs, culprits, mode);
                } else {
                    self.ty_inf.assign(lhs_var, rhs.value);
                }
            }
            (_, SpannedTyView::InferVar(rhs_var)) => {
                if let Some(known_rhs) = self.ty_inf.lookup(rhs_var) {
                    // TODO: Saturating spanned types?
                    self.relate_ty_inner(lhs, SpannedTy::new_unspanned(known_rhs), culprits, mode);
                } else {
                    self.ty_inf.assign(rhs_var, lhs.value);
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
                culprits.push(TyEquateCulprit::Types(lhs, rhs));
            }
        }
    }

    fn relate_ty_trait_clauses_inner(
        &mut self,
        lhs: SpannedTraitClauseList,
        rhs: SpannedTraitClauseList,
        culprits: &mut Vec<TyEquateCulprit>,
        mode: RelationMode,
    ) {
        let s = self.session();
        let tcx = self.tcx();

        if lhs.len(s) != rhs.len(s) {
            culprits.push(TyEquateCulprit::ClauseLists(lhs, rhs));
            return;
        }

        for (lhs_clause, rhs_clause) in lhs.iter(s).zip(rhs.iter(s)) {
            match (lhs_clause.view(tcx), rhs_clause.view(tcx)) {
                (SpannedTraitClauseView::Outlives(lhs), SpannedTraitClauseView::Outlives(rhs)) => {
                    // Technically, `MyTrait + 'a + 'b: 'c` could imply either `'a: 'c` or
                    // `'b: 'c`, meaning that relating both would be unnecessary but this
                    // logic will produce constraints for both. This isn't a problem because
                    // we only ever lower trait objects with *exactly one* outlives
                    // constraint.
                    self.relate_re(lhs, rhs, mode);
                }
                (SpannedTraitClauseView::Trait(lhs), SpannedTraitClauseView::Trait(rhs))
                    if lhs.value.def == rhs.value.def =>
                {
                    for (lhs, rhs) in lhs
                        .view(tcx)
                        .params
                        .iter(s)
                        .zip(rhs.view(tcx).params.iter(s))
                    {
                        match (lhs.view(tcx), rhs.view(tcx)) {
                            (
                                SpannedTraitParamView::Equals(lhs),
                                SpannedTraitParamView::Equals(rhs),
                            ) => match (lhs.view(tcx), rhs.view(tcx)) {
                                (SpannedTyOrReView::Re(lhs), SpannedTyOrReView::Re(rhs)) => {
                                    self.relate_re(lhs, rhs, RelationMode::Equate);
                                }
                                (SpannedTyOrReView::Ty(lhs), SpannedTyOrReView::Ty(rhs)) => {
                                    self.relate_ty_inner(lhs, rhs, culprits, RelationMode::Equate);
                                }
                                _ => unreachable!(),
                            },
                            (
                                SpannedTraitParamView::Unspecified(lhs),
                                SpannedTraitParamView::Unspecified(rhs),
                            ) => {
                                self.relate_ty_trait_clauses_inner(
                                    lhs,
                                    rhs,
                                    culprits,
                                    RelationMode::Equate,
                                );
                            }
                            _ => {
                                culprits.push(TyEquateCulprit::Params(lhs, rhs));
                            }
                        }
                    }
                }
                _ => {
                    culprits.push(TyEquateCulprit::ClauseLists(lhs, rhs));
                    return;
                }
            }
        }
    }

    pub fn wf_ty(&mut self, ty: SpannedTy) {
        todo!()
    }
}

// === TyInferCx === //

#[derive(Debug, Clone, Default)]
pub struct TyInferCx {
    disjoint: DisjointSetVec<Option<Ty>>,
}

impl TyInferCx {
    pub fn fresh(&mut self) -> InferTyVar {
        let var = InferTyVar(self.disjoint.len() as u32);
        self.disjoint.push(None);
        var
    }

    pub fn assign(&mut self, var: InferTyVar, ty: Ty) {
        let root = self.disjoint.root_of(var.0 as usize);
        let root = &mut self.disjoint[root];

        debug_assert!(root.is_none());
        *root = Some(ty);
    }

    pub fn lookup(&self, var: InferTyVar) -> Option<Ty> {
        self.disjoint[self.disjoint.root_of(var.0 as usize)]
    }

    pub fn union(&mut self, lhs: InferTyVar, rhs: InferTyVar) {
        let lhs_ty = self.lookup(lhs);
        let rhs_ty = self.lookup(rhs);

        debug_assert!(lhs_ty.is_none() || rhs_ty.is_none());

        self.disjoint.join(lhs.0 as usize, rhs.0 as usize);

        let new_root = self.disjoint.root_of(lhs.0 as usize);
        self.disjoint[new_root] = lhs_ty.or(rhs_ty);
    }
}

// === ReInferCx === //

#[derive(Debug, Default)]
pub struct ReInferCx {
    // TODO
}
