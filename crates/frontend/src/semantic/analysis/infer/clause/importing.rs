//! Logic to import a user-written type in a signature or function body into a form the inference
//! context can understand.

use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag,
        analysis::{DebruijnAbsoluteRange, DebruijnTop, Spanned},
        arena::{HasInterner, HasListInterner, Obj},
        syntax::Span,
    },
    semantic::{
        analysis::{
            ClauseCx, ClauseOrigin, ClauseOriginKind, TyCtxt, TyFoldable, TyFolder, TyFolderExt,
            TyFolderInfallibleExt, TyFolderPreservesSpans, TyVisitorInfallibleExt, UnifyCxMode,
        },
        syntax::{
            AdtInstance, AdtItem, AnyGeneric, FnDef, FnInstance, FnInstanceInner, FnOwner,
            FuncDefOwner, GenericBinder, GenericSubst, HrtbBinder, HrtbBinderKind, HrtbDebruijn,
            HrtbDebruijnDef, HrtbUniverse, ImplItem, Re, RelationMode, SpannedHrtbBinder,
            SpannedHrtbBinderView, SpannedRe, SpannedTy, SpannedTyView, TraitClause, TraitItem,
            TraitParam, TraitSpec, Ty, TyKind, TyList, TyOrRe, TyOrReKind, TyProjection,
            TypeAliasItem, UniversalReVarSourceInfo, UniversalTyVarSourceInfo,
        },
    },
    utils::hash::FxHashMap,
};
use hashbrown::hash_map;
use std::{convert::Infallible, mem};

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

    pub fn to_owned(self) -> ClauseImportEnv {
        ClauseImportEnv {
            self_ty: self.self_ty,
            sig_generic_substs: self.sig_generic_substs.to_vec(),
        }
    }
}

impl<'tcx> ClauseCx<'tcx> {
    pub fn importer<'a>(
        &'a mut self,
        env: ClauseImportEnvRef<'a>,
        universe: HrtbUniverse,
    ) -> ClauseCxImporter<'a, 'tcx> {
        ClauseCxImporter {
            ccx: self,
            env: env.to_owned(),
            hrtb_top: DebruijnTop::default(),
            hrtb_binder_ranges: FxHashMap::default(),
            reentrant_aliases: FxHashMap::default(),
            universe,
        }
    }

    // === Universal === //

    pub fn import_binder_list_as_universal(
        &mut self,
        self_ty: Ty,
        binders: &[Obj<GenericBinder>],
        universe: &HrtbUniverse,
    ) -> Vec<GenericSubst> {
        let substs = self.create_blank_universal_vars_from_binder_list(binders, universe);

        self.init_universal_var_clauses_from_binder(
            ClauseImportEnvRef {
                self_ty,
                sig_generic_substs: &substs,
            },
            universe,
        );

        substs
    }

    pub fn create_blank_universal_vars_from_binder_list(
        &mut self,
        binders: &[Obj<GenericBinder>],
        universe: &HrtbUniverse,
    ) -> Vec<GenericSubst> {
        binders
            .iter()
            .map(|&binder| self.create_blank_universal_vars_from_binder(binder, universe))
            .collect()
    }

    pub fn create_blank_universal_vars_from_binder(
        &mut self,
        binder: Obj<GenericBinder>,
        universe: &HrtbUniverse,
    ) -> GenericSubst {
        let s = self.session();
        let tcx = self.tcx();

        let substs =
            binder
                .r(s)
                .defs
                .iter()
                .map(|&generic| match generic {
                    AnyGeneric::Re(generic) => {
                        TyOrRe::Re(self.fresh_re_universal(UniversalReVarSourceInfo::Root(generic)))
                    }
                    AnyGeneric::Ty(generic) => TyOrRe::Ty(self.fresh_ty_universal(
                        UniversalTyVarSourceInfo::Root(generic),
                        universe.clone(),
                    )),
                })
                .collect::<Vec<_>>();

        let substs = tcx.intern_list(&substs);

        GenericSubst { binder, substs }
    }

    pub fn init_universal_var_clauses_from_binder(
        &mut self,
        env: ClauseImportEnvRef<'_>,
        universe: &HrtbUniverse,
    ) {
        let s = self.session();

        for &subst in env.sig_generic_substs {
            for (&generic, &subst) in subst.binder.r(s).defs.iter().zip(subst.substs.r(s)) {
                match (generic, subst) {
                    (AnyGeneric::Re(generic), TyOrRe::Re(target)) => {
                        for &clause in generic.r(s).clauses.value.r(s) {
                            let clause = self.importer(env, universe.clone()).fold(clause);

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

                        let clauses = self
                            .importer(env, universe.clone())
                            .fold(generic.r(s).clauses.value);

                        self.init_ty_universal_var_direct_clauses(target, clauses);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    // === Specialized universal imports === //

    pub fn import_trait_def_env_as_universal(
        &mut self,
        def: Obj<TraitItem>,
        universe: &HrtbUniverse,
    ) -> ClauseImportEnv {
        let s = self.session();
        let tcx = self.tcx();

        // Create a universal variable representing `Self`
        let self_var =
            self.fresh_ty_universal_var(UniversalTyVarSourceInfo::TraitSelf, universe.clone());

        let self_ty = tcx.intern(TyKind::UniversalVar(self_var));

        // Create universal variables for each parameter.
        let sig_generic_substs =
            self.import_binder_list_as_universal(self_ty, &[*def.r(s).generics], universe);

        let generic_params = sig_generic_substs[0].substs;

        // Make `Self` implement the trait with these synthesized parameters.
        self.init_ty_universal_var_direct_clauses(
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
    }

    pub fn import_adt_def_env_as_universal(
        &mut self,
        def: Obj<AdtItem>,
        universe: &HrtbUniverse,
    ) -> ClauseImportEnv {
        let s = self.session();
        let tcx = self.tcx();

        // Create universal parameters.
        let sig_generic_substs =
            self.create_blank_universal_vars_from_binder_list(&[def.r(s).generics], universe);

        // Create the `Self` type.
        let self_ty = tcx.intern(TyKind::Adt(AdtInstance {
            def,
            params: sig_generic_substs[0].substs,
        }));

        // Initialize the clauses.
        self.init_universal_var_clauses_from_binder(
            ClauseImportEnvRef {
                self_ty,
                sig_generic_substs: &sig_generic_substs,
            },
            universe,
        );

        ClauseImportEnv::new(self_ty, sig_generic_substs)
    }

    pub fn import_impl_block_env_as_universal(
        &mut self,
        def: Obj<ImplItem>,
        universe: &HrtbUniverse,
    ) -> ClauseImportEnv {
        let s = self.session();
        let tcx = self.tcx();

        // Create universal parameters.
        let sig_generic_substs =
            self.create_blank_universal_vars_from_binder_list(&[def.r(s).generics], universe);

        // Create the `Self` type. This type cannot contain `Self` so we give a dummy self type.
        let self_ty = self
            .importer(
                ClauseImportEnvRef::new(tcx.intern(TyKind::SigThis), &sig_generic_substs),
                universe.clone(),
            )
            .fold(def.r(s).target.value);

        // Initialize the clauses.
        self.init_universal_var_clauses_from_binder(
            ClauseImportEnvRef::new(self_ty, &sig_generic_substs),
            universe,
        );

        ClauseImportEnv::new(self_ty, sig_generic_substs)
    }

    pub fn import_fn_item_generics_as_universal(
        &mut self,
        self_ty: Ty,
        def: Obj<FnDef>,
        universe: &HrtbUniverse,
    ) -> Vec<GenericSubst> {
        self.import_binder_list_as_universal(self_ty, &[def.r(self.session()).generics], universe)
    }

    pub fn import_fn_def_env_as_universal(
        &mut self,
        def: Obj<FnDef>,
        universe: &HrtbUniverse,
    ) -> ClauseImportEnv {
        let s = self.session();
        let tcx = self.tcx();

        let mut env = match def.r(s).owner {
            FuncDefOwner::Func(_item) => ClauseImportEnv {
                self_ty: tcx.intern(TyKind::SigThis),
                sig_generic_substs: Vec::new(),
            },
            FuncDefOwner::TraitMethod(def, _idx) => {
                self.import_trait_def_env_as_universal(def, universe)
            }
            FuncDefOwner::ImplMethod(def, _idx) => {
                self.import_impl_block_env_as_universal(def, universe)
            }
        };

        env.sig_generic_substs
            .extend_from_slice(&self.import_fn_item_generics_as_universal(
                env.self_ty,
                def,
                universe,
            ));

        env
    }

    pub fn import_type_alias_def_env_as_universal(
        &mut self,
        def: Obj<TypeAliasItem>,
        universe: &HrtbUniverse,
    ) -> ClauseImportEnv {
        let s = self.session();
        let tcx = self.tcx();

        let this_ty = tcx.intern(TyKind::SigThis);

        ClauseImportEnv::new(
            this_ty,
            self.import_binder_list_as_universal(this_ty, &[def.r(s).generics], universe),
        )
    }

    // === Existential === //

    pub fn instantiate_binder_list_as_infer(
        &mut self,
        origin: &ClauseOrigin,
        mut base_env: ClauseImportEnv,
        binders: &[Obj<GenericBinder>],
        universe: &HrtbUniverse,
    ) -> ClauseImportEnv {
        // Produce a substitution for each binder.
        let substs = self.instantiate_blank_infer_vars_from_binder_list(binders, universe);
        base_env.sig_generic_substs.extend_from_slice(&substs);

        // Register clause obligations.
        self.oblige_import_env_meets_own_binder_clauses(origin, base_env.as_ref(), universe);

        base_env
    }

    pub fn instantiate_blank_infer_vars_from_binder_list(
        &mut self,
        binders: &[Obj<GenericBinder>],
        universe: &HrtbUniverse,
    ) -> Vec<GenericSubst> {
        binders
            .iter()
            .map(|&binder| self.instantiate_blank_infer_vars_from_binder(binder, universe))
            .collect()
    }

    pub fn instantiate_blank_infer_vars_from_binder(
        &mut self,
        binder: Obj<GenericBinder>,
        universe: &HrtbUniverse,
    ) -> GenericSubst {
        let s = self.session();
        let tcx = self.tcx();

        let substs = binder
            .r(s)
            .defs
            .iter()
            .map(|&generic| match generic {
                AnyGeneric::Re(_) => TyOrRe::Re(self.fresh_re_infer()),
                AnyGeneric::Ty(_) => TyOrRe::Ty(self.fresh_ty_infer(universe.clone())),
            })
            .collect::<Vec<_>>();

        let substs = tcx.intern_list(&substs);

        GenericSubst { binder, substs }
    }

    pub fn oblige_import_env_meets_own_binder_clauses(
        &mut self,
        origin: &ClauseOrigin,
        env: ClauseImportEnvRef<'_>,
        universe: &HrtbUniverse,
    ) {
        let s = self.session();

        for &subst in env.sig_generic_substs {
            self.oblige_args_meet_binder_clauses(
                env,
                &subst.binder.r(s).defs,
                subst.substs.r(s),
                universe,
                |_this, _idx, clause| {
                    ClauseOrigin::new(
                        Some(origin.clone()),
                        ClauseOriginKind::GenericRequirements { clause },
                    )
                },
            );
        }
    }

    pub fn oblige_args_meet_binder_clauses(
        &mut self,
        def_env: ClauseImportEnvRef<'_>,
        defs: &[AnyGeneric],
        args: &[TyOrRe],
        universe: &HrtbUniverse,
        mut gen_reason: impl FnMut(&mut Self, usize, Span) -> ClauseOrigin,
    ) {
        let s = self.session();
        let tcx = self.tcx();

        for (i, (&generic, &subst)) in defs.iter().zip(args).enumerate() {
            match (generic, subst) {
                (AnyGeneric::Re(generic), TyOrRe::Re(target)) => {
                    for clause in generic.r(s).clauses.iter(tcx) {
                        let clause_span = clause.own_span();
                        let clause = self.importer(def_env, universe.clone()).fold(clause.value);

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
                    let clauses = self
                        .importer(def_env, universe.clone())
                        .fold_preserved(*generic.r(s).clauses);

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
                                self.oblige_ty_meets_trait(reason, target, rhs, universe.clone());
                            }
                        }
                    }
                }
                _ => unreachable!(),
            }
        }
    }

    // === Specialized existential imports === //

    pub fn instantiate_fn_owner_as_infer(
        &mut self,
        origin: &ClauseOrigin,
        owner: FnOwner,
        universe: &HrtbUniverse,
    ) -> ClauseImportEnv {
        let s = self.session();
        let tcx = self.tcx();

        match owner {
            FnOwner::Item(_) => ClauseImportEnv::new(tcx.intern(TyKind::SigThis), Vec::new()),
            FnOwner::Trait {
                instance,
                self_ty,
                method_idx: _,
            } => {
                let substs = instance
                    .params
                    .r(s)
                    .iter()
                    .map(|&param| match param {
                        TraitParam::Equals(value) => value,
                        TraitParam::Unspecified(clauses) => {
                            let ty = self.fresh_ty_infer(universe.clone());
                            self.oblige_ty_meets_clauses(origin, ty, clauses, universe);

                            TyOrRe::Ty(ty)
                        }
                    })
                    .collect::<Vec<_>>();

                let substs = tcx.intern_list(&substs);

                let params = substs
                    .r(s)
                    .iter()
                    .copied()
                    .map(TraitParam::Equals)
                    .collect::<Vec<_>>();

                let params = tcx.intern_list(&params);

                self.oblige_ty_meets_trait_instantiated(
                    origin.clone(),
                    self_ty,
                    TraitSpec {
                        def: instance.def,
                        params,
                    },
                    universe.clone(),
                );

                ClauseImportEnv::new(
                    self_ty,
                    vec![GenericSubst {
                        binder: *instance.def.r(s).generics,
                        substs,
                    }],
                )
            }
            FnOwner::Inherent {
                self_ty,
                block,
                method_idx: _,
            } => {
                let env = self.instantiate_binder_list_as_infer(
                    origin,
                    ClauseImportEnv::new(self_ty, Vec::new()),
                    &[block.r(s).generics],
                    universe,
                );

                let expected_self_ty = self
                    .importer(env.as_ref(), universe.clone())
                    .fold(block.r(s).target.value);

                self.oblige_ty_unifies_ty(
                    origin.clone(),
                    self_ty,
                    expected_self_ty,
                    RelationMode::Equate,
                );

                env
            }
        }
    }

    pub fn instantiate_fn_instance_sig(
        &mut self,
        origin: &ClauseOrigin,
        instance: FnInstance,
        universe: &HrtbUniverse,
    ) -> (TyList, Ty) {
        let tcx = self.tcx();
        let s = self.session();

        let FnInstanceInner { owner, early_args } = *instance.r(s);

        let mut env = self.instantiate_fn_owner_as_infer(origin, owner, universe);

        let def = match owner {
            FnOwner::Item(def) => *def.r(s).def,
            FnOwner::Trait {
                instance,
                self_ty: _,
                method_idx,
            } => instance.def.r(s).methods[method_idx as usize],
            FnOwner::Inherent {
                self_ty: _,
                block,
                method_idx,
            } => block.r(s).methods[method_idx as usize],
        };

        if let Some(early_args) = early_args {
            env.sig_generic_substs.push(GenericSubst {
                binder: def.r(s).generics,
                substs: early_args,
            });
        } else {
            env =
                self.instantiate_binder_list_as_infer(origin, env, &[def.r(s).generics], universe);
        }

        let args = def
            .r(s)
            .args
            .r(s)
            .iter()
            .map(|v| v.ty.value)
            .collect::<Vec<_>>();

        let args = tcx.intern_list(&args);

        let args = self.importer(env.as_ref(), universe.clone()).fold(args);
        let ret_ty = self
            .importer(env.as_ref(), universe.clone())
            .fold(def.r(s).ret_ty.value);

        (args, ret_ty)
    }
}

pub struct ClauseCxImporter<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    env: ClauseImportEnv,
    hrtb_top: DebruijnTop,
    hrtb_binder_ranges: FxHashMap<Obj<GenericBinder>, DebruijnAbsoluteRange>,
    reentrant_aliases: FxHashMap<Obj<TypeAliasItem>, ReentrantAliasState>,
    universe: HrtbUniverse,
}

#[derive(Debug, Copy, Clone)]
enum ReentrantAliasState {
    WaitingForViolation,
    Violated(Span),
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
            SpannedTyView::SigInfer => self.ccx.fresh_ty_infer(self.universe.clone()),
            SpannedTyView::SigGeneric(generic) => {
                self.lookup_generic(AnyGeneric::Ty(generic)).unwrap_ty()
            }
            SpannedTyView::SigProject(TyProjection {
                target,
                spec,
                assoc,
            }) => {
                let target = self.fold(target);
                let spec = self.fold(spec);

                let assoc_infer_ty = self.ccx.fresh_ty_infer(self.universe.clone());
                let spec = {
                    let mut args = spec.params.r(s).to_vec();
                    args[assoc as usize] = TraitParam::Equals(TyOrRe::Ty(assoc_infer_ty));

                    TraitSpec {
                        def: spec.def,
                        params: tcx.intern_list(&args),
                    }
                };

                self.ccx
                    .wf_visitor(self.universe.clone())
                    .with_clause_applies_to(target)
                    .visit_spanned(Spanned::new_saturated(spec, ty.own_span(), tcx));

                self.ccx.oblige_ty_meets_trait_instantiated(
                    ClauseOrigin::root(ClauseOriginKind::InstantiatedProjection {
                        span: ty.own_span(),
                    }),
                    target,
                    spec,
                    self.universe.clone(),
                );

                assoc_infer_ty
            }
            SpannedTyView::SigAlias(def, args) => 'alias: {
                match self.reentrant_aliases.entry(def) {
                    hash_map::Entry::Occupied(entry) => {
                        let entry = entry.into_mut();

                        if matches!(entry, ReentrantAliasState::WaitingForViolation) {
                            *entry = ReentrantAliasState::Violated(ty.own_span());
                        }

                        break 'alias tcx.intern(TyKind::Error(ErrorGuaranteed::new_unchecked()));
                    }
                    hash_map::Entry::Vacant(entry) => {
                        entry.insert(ReentrantAliasState::WaitingForViolation);
                    }
                }

                let args = self.fold(args);

                let old_env = mem::replace(
                    &mut self.env,
                    ClauseImportEnv::new(
                        tcx.intern(TyKind::SigThis),
                        vec![GenericSubst {
                            binder: def.r(s).generics,
                            substs: args,
                        }],
                    ),
                );

                let body = self.fold_spanned(*def.r(s).body);

                self.env = old_env;

                match self.reentrant_aliases.remove(&def).unwrap() {
                    ReentrantAliasState::WaitingForViolation => {
                        // (no violation occurred)
                    }
                    ReentrantAliasState::Violated(span) => {
                        Diag::span_err(ty.own_span(), "attempted to expand recursive type alias")
                            .child(LeafDiag::span_note(span, "reentered here"))
                            .emit();
                    }
                }

                body
            }

            SpannedTyView::Simple(_)
            | SpannedTyView::Reference(_, _, _)
            | SpannedTyView::Adt(_)
            | SpannedTyView::Trait(_, _, _)
            | SpannedTyView::Tuple(_)
            | SpannedTyView::FnDef(_)
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
        if self.ccx.mode() == UnifyCxMode::RegionBlind {
            return Ok(Re::Erased);
        }

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
