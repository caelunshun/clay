use crate::{
    base::Session,
    semantic::{
        analysis::{TyCtxt, TyVisitor, TyVisitorWalk},
        syntax::{
            InferTyVar, Re, RelationMode, SpannedRe, SpannedTraitClauseList,
            SpannedTraitClauseView, SpannedTraitParam, SpannedTraitParamView, SpannedTy,
            SpannedTyOrReView, SpannedTyView, Ty,
        },
    },
};
use disjoint::DisjointSetVec;
use std::{convert::Infallible, ops::ControlFlow};

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

    pub fn relate_wf_ty(&mut self, ty: SpannedTy) {
        todo!()
    }

    pub fn relate_ty(
        &mut self,
        lhs: SpannedTy,
        rhs: SpannedTy,
        mode: RelationMode,
    ) -> Result<(), TyEquateError> {
        let mut culprits = Vec::new();

        self.relate_wf_ty(lhs);
        self.relate_wf_ty(rhs);
        self.relate_ty_inner(lhs, rhs, &mut culprits, mode);

        if !culprits.is_empty() {
            return Err(TyEquateError {
                origin_lhs: lhs,
                origin_rhs: rhs,
                culprits,
            });
        }

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

    pub fn relate_ty_and_re(&mut self, lhs: SpannedTy, rhs: SpannedRe, mode: RelationMode) {
        if self.re_inf.is_none() {
            return;
        }

        struct MentionVisitor<'a, 'tcx> {
            icx: &'a mut InferCx<'tcx>,
            rhs: SpannedRe,
            mode: RelationMode,
        }

        impl<'tcx> TyVisitor<'tcx> for MentionVisitor<'_, 'tcx> {
            type Break = Infallible;

            fn tcx(&self) -> &'tcx TyCtxt {
                self.icx.tcx()
            }

            fn visit_spanned_re(&mut self, re: SpannedRe) -> ControlFlow<Self::Break> {
                self.icx.relate_re(re, self.rhs, self.mode);
                self.walk_re(re)?;

                ControlFlow::Continue(())
            }
        }

        _ = MentionVisitor {
            icx: self,
            rhs,
            mode,
        }
        .visit_spanned_ty(lhs);
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
