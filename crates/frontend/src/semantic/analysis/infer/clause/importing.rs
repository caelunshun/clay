//! Logic to import a user-written type in a signature or function body into a form the inference
//! context can understand.

use crate::{
    base::{
        analysis::{DebruijnAbsoluteRange, DebruijnTop, Spanned},
        arena::{HasInterner, HasListInterner, Obj},
        syntax::Span,
    },
    semantic::{
        analysis::{
            CheckOrigin, CheckOriginKind, ClauseCx, TyCtxt, TyFoldable, TyFolder, TyFolderExt,
            TyFolderInfallibleExt, TyFolderPreservesSpans, TyVisitorInfallibleExt,
        },
        syntax::{
            AdtInstance, AdtItem, AnyGeneric, FnDef, GenericBinder, GenericSubst, HrtbBinder,
            HrtbBinderKind, HrtbDebruijn, HrtbDebruijnDef, ImplItem, Re, SpannedHrtbBinder,
            SpannedHrtbBinderView, SpannedRe, SpannedTy, SpannedTyProjectionView, SpannedTyView,
            TraitClause, TraitItem, TraitParam, TraitSpec, Ty, TyKind, TyOrRe, TyOrReKind,
            UniversalReVarSourceInfo, UniversalTyVarSourceInfo,
        },
    },
    utils::hash::FxHashMap,
};
use std::convert::Infallible;

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

                            let TraitClause::Outlives(allowed_to_outlive_dir, allowed_to_outlive) =
                                clause
                            else {
                                unreachable!()
                            };

                            self.permit_universe_re_outlives_general(
                                target,
                                allowed_to_outlive,
                                allowed_to_outlive_dir,
                            );
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
        origin: &CheckOrigin,
        self_ty: Ty,
        binders: &[Obj<GenericBinder>],
    ) -> Vec<GenericSubst> {
        // Produce a substitution for each binder.
        let substs = self.create_blank_infer_vars_from_binder_list(binders);

        // Register clause obligations.
        self.oblige_imported_infer_binder_meets_clauses(
            origin,
            ClauseImportEnvRef {
                self_ty,
                sig_generic_substs: &substs,
            },
        );

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

    pub fn oblige_imported_infer_binder_meets_clauses(
        &mut self,
        origin: &CheckOrigin,
        env: ClauseImportEnvRef<'_>,
    ) {
        let s = self.session();

        for &subst in env.sig_generic_substs {
            self.oblige_wf_args_meet_binder(
                env,
                &subst.binder.r(s).defs,
                subst.substs.r(s),
                |_this, _idx, clause| {
                    CheckOrigin::new(
                        Some(origin.clone()),
                        CheckOriginKind::GenericRequirements { clause },
                    )
                },
            );
        }
    }

    pub fn oblige_wf_args_meet_binder(
        &mut self,
        env: ClauseImportEnvRef<'_>,
        defs: &[AnyGeneric],
        args: &[TyOrRe],
        mut gen_reason: impl FnMut(&mut Self, usize, Span) -> CheckOrigin,
    ) {
        let s = self.session();
        let tcx = self.tcx();

        for (i, (&generic, &subst)) in defs.iter().zip(args).enumerate() {
            match (generic, subst) {
                (AnyGeneric::Re(generic), TyOrRe::Re(target)) => {
                    for clause in generic.r(s).clauses.iter(tcx) {
                        let clause_span = clause.own_span();
                        let clause = self.importer(env).fold(clause.value);

                        let TraitClause::Outlives(must_outlive_dir, must_outlive) = clause else {
                            unreachable!()
                        };

                        let reason = gen_reason(self, i, clause_span);

                        self.oblige_general_outlives(
                            reason,
                            TyOrRe::Re(target),
                            must_outlive,
                            must_outlive_dir,
                        );
                    }
                }
                (AnyGeneric::Ty(generic), TyOrRe::Ty(target)) => {
                    let clauses = self.importer(env).fold_preserved(*generic.r(s).clauses);

                    for clause in clauses.iter(tcx) {
                        let reason = gen_reason(self, i, clause.own_span());

                        match clause.value {
                            TraitClause::Outlives(must_outlive_dir, must_outlive) => {
                                self.oblige_general_outlives(
                                    reason,
                                    TyOrRe::Ty(target),
                                    must_outlive,
                                    must_outlive_dir,
                                );
                            }
                            TraitClause::Trait(rhs) => {
                                self.oblige_ty_meets_trait(reason, target, rhs);
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

        // Bring the binder into scope.
        let new_range = self.hrtb_top.move_inwards_by(binder_count);
        let old_range = self.hrtb_binder_ranges.insert(binder, new_range);

        // Fold the inner value and definitions list with a new generic binder available as an HRTB
        // binder.
        let inner = self.fold_spanned(inner);
        let defs = binder
            .r(s)
            .defs
            .iter()
            .map(|def| HrtbDebruijnDef {
                spawned_from: def.span(s),
                kind: def.kind(),
                clauses: self.fold_spanned(def.clauses(s)),
            })
            .collect::<Vec<_>>();

        let defs = tcx.intern_list(&defs);

        // Update the `binder_count` only after we've imported the `defs` since the definition
        // indexing scheme is relative to `binder.inner` to allow mutual recursion among generic
        // definitions.
        match old_range {
            Some(old_range) => {
                *self.hrtb_binder_ranges.get_mut(&binder).unwrap() = old_range;
            }
            None => {
                self.hrtb_binder_ranges.remove(&binder);
            }
        }

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

                self.ccx.oblige_ty_meets_trait_instantiated(
                    CheckOrigin::new(
                        None,
                        CheckOriginKind::InstantiatedProjection {
                            span: projection.own_span(),
                        },
                    ),
                    target.value,
                    spec,
                );

                assoc_infer_ty
            }

            SpannedTyView::Simple(_)
            | SpannedTyView::Reference(_, _, _)
            | SpannedTyView::Adt(_)
            | SpannedTyView::Trait(_, _, _)
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
