use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Session,
        analysis::{DebruijnMap, DebruijnTop},
        arena::{HasInterner, HasListInterner, LateInit, Obj},
        syntax::Span,
    },
    semantic::{
        infer::{
            ClauseCx, HrtbUniverse, HrtbUniverseInfo, ObligeCause, ObligeCauseFrame,
            ObligeCauseOrigin, ObligeCauseStep, UnifyCxMode,
        },
        lower::generics::normalize_positional_generic_arity,
        syntax::{
            AdtInstance, AnyGeneric, FnInstance, FnInstanceInner, FnOwner, FnOwnerAdtCtor,
            FnOwnerInherent, FnOwnerTrait, GenericBinder, HrtbBinder, HrtbDebruijnDef,
            HrtbProjection, InferTyVarSourceInfo, Re, RegionGeneric, RelationDirection,
            SigAdtInstance, SigGenericList, SigHrtbBinder, SigProjectType, SigRe, SigReKind,
            SigTraitClause, SigTraitClauseKind, SigTraitClauseList, SigTraitInstance,
            SigTraitParamKind, SigTraitSpec, SigTy, SigTyKind, SigTyList, SigTyOrRe, SigTyOrReList,
            TraitClause, TraitClauseList, TraitInstance, TraitParam, TraitSpec, Ty, TyCtxt,
            TyFolder, TyFolderInfallibleExt, TyKind, TyList, TyOrRe, TyOrReKind, TyOrReList,
            TypeAliasItem, TypeGeneric, UniversalReVarSourceInfo, UniversalTyVarSourceInfo,
        },
    },
    utils::hash::FxHashMap,
};
use hashbrown::hash_map;
use smallvec::SmallVec;
use std::{convert::Infallible, mem};

// === Environment === //

#[derive(Debug, Clone)]
pub struct ClauseImportEnv {
    _private: (),
    pub self_ty: Option<Ty>,
    pub substs: SmallVec<[GenericSubst; Self::SMALL_CAP]>,
}

impl ClauseImportEnv {
    pub const SMALL_CAP: usize = 2;

    pub fn new(self_ty: Option<Ty>, substs: impl IntoIterator<Item = GenericSubst>) -> Self {
        Self {
            _private: (),
            self_ty,
            substs: substs.into_iter().collect(),
        }
    }

    pub fn push_subst(&mut self, subst: GenericSubst) {
        self.substs.push(subst);
    }

    pub fn with_subst(mut self, subst: GenericSubst) -> Self {
        self.push_subst(subst);
        self
    }

    pub fn unwrap_self_ty(&self) -> Ty {
        self.self_ty.expect("no self type specified")
    }

    pub fn lookup_generic(&self, s: &Session, generic: AnyGeneric) -> TyOrRe {
        let pos = generic.binder(s);

        let binder = self
            .substs
            .iter()
            .find(|v| v.binder == pos.def)
            .unwrap_or_else(|| {
                panic!("no substitutions provided for signature generic {generic:?}")
            });

        binder.substs.r(s)[pos.idx as usize]
    }

    pub fn lookup_re(&self, s: &Session, generic: Obj<RegionGeneric>) -> Re {
        self.lookup_generic(s, AnyGeneric::Re(generic)).unwrap_re()
    }

    pub fn lookup_ty(&self, s: &Session, generic: Obj<TypeGeneric>) -> Ty {
        self.lookup_generic(s, AnyGeneric::Ty(generic)).unwrap_ty()
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct GenericSubst {
    _private: (),
    pub binder: Obj<GenericBinder>,
    pub substs: TyOrReList,
}

impl GenericSubst {
    pub fn new(binder: Obj<GenericBinder>, substs: TyOrReList) -> Self {
        Self {
            _private: (),
            binder,
            substs,
        }
    }
}

// === SigImporter === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum SigImporterWfMode {
    Skip,
    DelayBug,
    ReportHere,
}

impl<'tcx> ClauseCx<'tcx> {
    pub fn importer(
        &mut self,
        cause: ObligeCause,
        universe: HrtbUniverse,
        env: ClauseImportEnv,
        wf_mode: SigImporterWfMode,
    ) -> SigImporter<'_, 'tcx> {
        SigImporter {
            ccx: self,
            cause: match wf_mode {
                SigImporterWfMode::Skip | SigImporterWfMode::ReportHere => cause,
                SigImporterWfMode::DelayBug => cause.into_delay_bug(),
            },
            opts: SigImporterOpts {
                universe,
                env,
                create_wf_obligations: match wf_mode {
                    SigImporterWfMode::Skip => false,
                    SigImporterWfMode::DelayBug | SigImporterWfMode::ReportHere => true,
                },
                // We're not in a binder.
                defer_project_in_binder: false,
            },
            reentrant_aliases: FxHashMap::default(),
            hrtb_substs: DebruijnMap::default(),
        }
    }

    pub fn importer_here(&mut self, env: &ClauseImportEnv) -> SigImporter<'_, 'tcx> {
        self.importer(
            ObligeCause::new_empty_report(),
            HrtbUniverse::ROOT,
            env.clone(),
            SigImporterWfMode::ReportHere,
        )
    }

    pub fn importer_elsewhere(&mut self, env: &ClauseImportEnv) -> SigImporter<'_, 'tcx> {
        self.importer(
            ObligeCause::new_empty_report(),
            HrtbUniverse::ROOT,
            env.clone(),
            SigImporterWfMode::DelayBug,
        )
    }

    pub fn import_report_here<I: SigImportable>(
        &mut self,
        env: &ClauseImportEnv,
        target: I,
    ) -> I::Output {
        self.importer_here(env).import(target)
    }

    pub fn import_report_elsewhere<I: SigImportable>(
        &mut self,
        env: &ClauseImportEnv,
        target: I,
    ) -> I::Output {
        self.importer_elsewhere(env).import(target)
    }
}

pub trait SigImportable {
    type Output;

    fn import(me: Self, importer: &mut SigImporter<'_, '_>) -> Self::Output;
}

macro_rules! impl_sig_importable {
    ( $( $method:ident: $src:ty => $dest:ty; )* ) => {$(
        impl SigImportable for $src {
            type Output = $dest;

            fn import(me: Self, importer: &mut SigImporter<'_, '_>) -> Self::Output {
                importer.$method(me)
            }
        }
    )*};
}

impl_sig_importable! {
    // TODO
    // import_ty_list: SigTyList => TyList;
    // import_ty_or_re_list: SigTyOrReList => TyOrReList;
    import_ty_or_re: SigTyOrRe => TyOrRe;
    import_ty: SigTy => Ty;
    import_re: SigRe => Re;
    import_adt: SigAdtInstance => AdtInstance;
    import_trait_clause_list: SigTraitClauseList => TraitClauseList;
    import_trait_clause: SigTraitClause => TraitClause;
    import_hrtb_binder: SigHrtbBinder => HrtbBinder;
    import_trait_spec: SigTraitSpec => TraitSpec;
}

pub struct SigImporter<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    cause: ObligeCause,
    opts: SigImporterOpts,
    reentrant_aliases: FxHashMap<Obj<TypeAliasItem>, ReentrantAliasState>,
    hrtb_substs: DebruijnMap<Option<TyOrRe>>,
}

struct SigImporterOpts {
    universe: HrtbUniverse,
    env: ClauseImportEnv,
    create_wf_obligations: bool,
    defer_project_in_binder: bool,
}

#[derive(Debug, Copy, Clone)]
enum ReentrantAliasState {
    WaitingForViolation,
    Violated(Span),
}

#[derive(Debug, Copy, Clone)]
pub enum FixArity {
    Normalize,
    AssumeCorrect,
}

impl FixArity {
    pub fn should_fix(self) -> bool {
        matches!(self, Self::Normalize)
    }
}

/// Types
impl<'a, 'tcx> SigImporter<'a, 'tcx> {
    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn session(&self) -> &'tcx Session {
        self.ccx.session()
    }

    pub fn import<I: SigImportable>(&mut self, item: I) -> I::Output {
        I::import(item, self)
    }

    pub fn import_ty_list(&mut self, tys: SigTyList) -> TyList {
        let s = self.session();
        let tcx = self.tcx();

        tcx.intern_list(
            &tys.r(s)
                .iter()
                .map(|ty| self.import_ty(*ty))
                .collect::<Vec<_>>(),
        )
    }

    pub fn import_ty_or_re_list(&mut self, ty_or_res: SigTyOrReList) -> TyOrReList {
        let s = self.session();
        let tcx = self.tcx();

        tcx.intern_list(
            &ty_or_res
                .r(s)
                .iter()
                .map(|ty| self.import_ty_or_re(*ty))
                .collect::<Vec<_>>(),
        )
    }

    pub fn import_ty_or_re(&mut self, ty_or_re: SigTyOrRe) -> TyOrRe {
        match ty_or_re {
            SigTyOrRe::Re(re) => TyOrRe::Re(self.import_re(re)),
            SigTyOrRe::Ty(ty) => TyOrRe::Ty(self.import_ty(ty)),
        }
    }

    pub fn import_ty(&mut self, ty: SigTy) -> Ty {
        let s = self.session();
        let tcx = self.tcx();

        match ty.r(s).kind {
            // Parameterized (may require WF)
            SigTyKind::Alias(def, args) => {
                let s = self.session();
                let tcx = self.tcx();

                // Import the type alias's arguments.
                let args = self.import_simple_generic_args(
                    def.r(s).generics,
                    args,
                    FixArity::AssumeCorrect,
                );

                // Prevent reentrant alias resolution (preorder).
                match self.reentrant_aliases.entry(def) {
                    hash_map::Entry::Occupied(entry) => {
                        let entry = entry.into_mut();

                        if matches!(entry, ReentrantAliasState::WaitingForViolation) {
                            *entry = ReentrantAliasState::Violated(ty.r(s).span);
                        }

                        return tcx.intern(TyKind::Error(ErrorGuaranteed::new_unchecked()));
                    }
                    hash_map::Entry::Vacant(entry) => {
                        entry.insert(ReentrantAliasState::WaitingForViolation);
                    }
                }

                // Import the alias's inner contents.
                let env = ClauseImportEnv::new(None, [GenericSubst::new(def.r(s).generics, args)]);

                let parent_universe = self.opts.universe.clone();
                let parent_defer_project_in_binder = self.opts.defer_project_in_binder;
                let old_opts = mem::replace(
                    &mut self.opts,
                    SigImporterOpts {
                        universe: parent_universe,
                        env,
                        // Parameters already constrained by parent WF checks.
                        create_wf_obligations: false,
                        defer_project_in_binder: parent_defer_project_in_binder,
                    },
                );

                let body = self.import_ty(*def.r(s).body);

                self.opts = old_opts;

                // Prevent reentrant alias resolution (postorder).
                match self.reentrant_aliases.remove(&def).unwrap() {
                    ReentrantAliasState::WaitingForViolation => {
                        // (no violation occurred)
                    }
                    ReentrantAliasState::Violated(span) => {
                        let mut diag = Diag::span_err(
                            ty.r(s).span,
                            "attempted to expand recursive type alias",
                        );

                        if ty.r(s).span != span {
                            diag.push_child(LeafDiag::span_note(span, "reentered here"));
                        }

                        diag.emit();
                    }
                }

                body
            }
            SigTyKind::Reference(re, muta, pointee) => {
                let pointee_span = pointee.r(s).span;

                let re = self.import_re(re);
                let pointee = self.import_ty(pointee);

                if self.opts.create_wf_obligations {
                    self.ccx.oblige_ty_outlives_re(
                        self.cause.clone().child(ObligeCauseFrame::Origin(
                            ObligeCauseOrigin::ImportWfForReference {
                                pointee: pointee_span,
                            },
                        )),
                        pointee,
                        re,
                        RelationDirection::LhsOntoRhs,
                    );
                }

                tcx.intern(TyKind::Reference(re, muta, pointee))
            }
            SigTyKind::Adt(adt) => tcx.intern(TyKind::Adt(self.import_adt(adt))),
            SigTyKind::Trait(re, muta, clauses) => {
                let re = self.import_re(re);
                let clauses = self.import_trait_clause_list(clauses);
                let object_ty = tcx.intern(TyKind::Trait(re, muta, clauses));

                object_ty
            }
            SigTyKind::Tuple(tys) => {
                let tys = self.import_ty_list(tys);

                if self.opts.create_wf_obligations {
                    // TODO: sizedness checks
                }

                tcx.intern(TyKind::Tuple(tys))
            }

            // Unparameterized
            SigTyKind::SelfTy => self.opts.env.unwrap_self_ty(),

            SigTyKind::Generic(generic) => self.opts.env.lookup_ty(s, generic),

            SigTyKind::Infer => self.ccx.fresh_ty_infer(
                self.opts.universe.clone(),
                InferTyVarSourceInfo::DirectlyImported { span: ty.r(s).span },
            ),

            SigTyKind::Simple(kind) => tcx.intern(TyKind::Simple(kind)),

            SigTyKind::HrtbVar(idx) => match self.hrtb_substs.lookup(idx.0) {
                Some(real_subst) => real_subst.unwrap_ty(),
                None => tcx.intern(TyKind::HrtbVar(idx)),
            },

            SigTyKind::Project(SigProjectType {
                target,
                spec,
                assoc_span: _,
                assoc_idx,
            }) => {
                let target = self.import_ty(target);

                let spec_imported = self.import_trait_spec(spec);

                if self.opts.defer_project_in_binder {
                    return tcx.intern(TyKind::HrtbProjection(HrtbProjection {
                        target: target,
                        spec: spec_imported,
                        assoc_idx,
                    }));
                }

                let instance = self.ccx.instantiate_infer().resolve_trait_spec(
                    &self.cause,
                    &self.opts.universe,
                    target,
                    spec_imported,
                );

                // We don't do a `ensure_trait_instance_args_wf_no_self_obligation` here because the
                // diagnostic produced by `instantiate_trait_spec` should be enough to warn users.

                instance.params.r(s)[assoc_idx as usize].unwrap_ty()
            }

            SigTyKind::Error(err) => tcx.intern(TyKind::Error(err)),
        }
    }

    pub fn import_re(&mut self, re: SigRe) -> Re {
        let s = self.session();

        if self.ccx.mode() == UnifyCxMode::RegionBlind {
            return Re::Erased;
        }

        match re.kind {
            SigReKind::Gc => Re::Gc,
            SigReKind::HrtbVar(idx) => match self.hrtb_substs.lookup(idx.0) {
                Some(real_subst) => real_subst.unwrap_re(),
                None => Re::HrtbVar(idx),
            },
            SigReKind::Infer => self.ccx.fresh_re_infer(),
            SigReKind::Generic(generic) => self.opts.env.lookup_re(s, generic),
            SigReKind::Error(err) => Re::Error(err),
        }
    }

    pub fn import_adt(&mut self, adt: SigAdtInstance) -> AdtInstance {
        let s = self.session();

        AdtInstance {
            def: adt.def,
            params: self.import_simple_generic_args(
                adt.def.r(s).generics,
                adt.params,
                FixArity::AssumeCorrect,
            ),
        }
    }

    pub fn import_fn_instance_from_owner(
        &mut self,
        owner: FnOwner,
        args: Option<SigGenericList>,
        fix_arity: FixArity,
    ) -> FnInstance {
        let s = self.session();
        let tcx = self.tcx();

        let early_args = args.map(|args| match owner {
            FnOwner::Item(def) => {
                self.import_simple_generic_args(def.r(s).def.r(s).generics, args, fix_arity)
            }
            FnOwner::Trait(FnOwnerTrait {
                instance,
                self_ty,
                method_idx,
            }) => {
                let instance = self.ccx.instantiate_infer().resolve_trait_spec(
                    &self.cause,
                    &self.opts.universe,
                    self_ty,
                    instance,
                );

                let instance_binder = *instance.def.r(s).generics;
                let method_def = instance.def.r(s).methods[method_idx as usize];
                let method_binder = method_def.r(s).generics;

                self.import_generic_args(method_binder, args, fix_arity, |args_imported| {
                    ClauseImportEnv::new(
                        Some(self_ty),
                        [
                            GenericSubst::new(instance_binder, instance.params),
                            GenericSubst::new(method_binder, args_imported),
                        ],
                    )
                })
            }
            FnOwner::Inherent(FnOwnerInherent {
                self_ty,
                block,
                method_idx,
            }) => {
                let block_args = self
                    .ccx
                    .instantiate_infer()
                    .resolve_inherent_impl_block_env(
                        &self.cause,
                        &self.opts.universe,
                        block,
                        self_ty,
                    )
                    .params;

                let method_def = block.r(s).methods[method_idx as usize].unwrap();
                let method_binder = method_def.r(s).generics;

                self.import_generic_args(method_binder, args, fix_arity, |args_imported| {
                    ClauseImportEnv::new(
                        Some(self_ty),
                        [
                            GenericSubst::new(block.r(s).generics, block_args),
                            GenericSubst::new(method_binder, args_imported),
                        ],
                    )
                })
            }
            FnOwner::AdtCtor(FnOwnerAdtCtor { ctor }) => self.import_simple_generic_args(
                ctor.r(s).owner.item(s).r(s).generics,
                args,
                fix_arity,
            ),
        });

        tcx.intern(FnInstanceInner { owner, early_args })
    }

    fn import_simple_generic_args(
        &mut self,
        binder: Obj<GenericBinder>,
        args: SigGenericList,
        fix_arity: FixArity,
    ) -> TyOrReList {
        self.import_generic_args(binder, args, fix_arity, |args_imported| {
            ClauseImportEnv::new(None, [GenericSubst::new(binder, args_imported)])
        })
    }

    fn import_generic_args(
        &mut self,
        binder: Obj<GenericBinder>,
        args: SigGenericList,
        fix_arity: FixArity,
        make_env: impl FnOnce(TyOrReList) -> ClauseImportEnv,
    ) -> TyOrReList {
        let tcx = self.tcx();
        let s = self.session();

        let args = if fix_arity.should_fix() {
            normalize_positional_generic_arity(
                tcx,
                binder,
                None,
                args.segment_span,
                args.elems.r(s),
            )
        } else {
            debug_assert_eq!(binder.r(s).defs.len(), args.elems.r(s).len());

            args
        };

        let args_imported = self.import_ty_or_re_list(args.elems);

        if self.opts.create_wf_obligations {
            let env = make_env(args_imported);

            let args_spanned = args_imported
                .r(s)
                .iter()
                .zip(args.elems.r(s))
                .zip(&binder.r(s).defs)
                .map(|((&ty_or_re, sig), generic)| {
                    let cause = self.cause.clone().child(ObligeCauseFrame::Origin(
                        ObligeCauseOrigin::ImportWfForGenericParam {
                            use_span: sig.span(s),
                            clause_span: generic.span(s),
                        },
                    ));

                    (cause, ty_or_re)
                });

            self.ccx.instantiate_infer().ensure_binder_params_wf(
                &self.opts.universe,
                binder,
                env.clone(),
                None,
                args_spanned,
            );
        }

        args_imported
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
enum AssocParamWfMode {
    Check,
    Ignore,
}

/// Traits
impl<'a, 'tcx> SigImporter<'a, 'tcx> {
    // === Instance logic === //

    pub fn import_trait_instance(
        &mut self,
        instance_applies_to: Ty,
        instance: SigTraitInstance,
    ) -> TraitInstance {
        let s = self.session();
        let tcx = self.tcx();

        let instance_imported = TraitInstance {
            def: instance.def,
            params: tcx.intern_list(
                &instance
                    .params
                    .r(s)
                    .iter()
                    .map(|&ty_or_re| self.import_ty_or_re(ty_or_re))
                    .collect::<Vec<_>>(),
            ),
        };

        if self.opts.create_wf_obligations {
            self.ensure_trait_instance_args_wf_no_self_obligation(
                &self.cause.clone(),
                &self.opts.universe.clone(),
                instance_applies_to,
                instance.params.r(s).iter().map(|v| v.span(s)),
                instance_imported,
                AssocParamWfMode::Check,
            );
        }

        instance_imported
    }

    fn ensure_trait_instance_args_wf_no_self_obligation(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        applies_to: Ty,
        spans: impl IntoIterator<Item = Span>,
        instance: TraitInstance,
        assoc_wf_mode: AssocParamWfMode,
    ) {
        let s = self.ccx.session();

        let binder = *instance.def.r(s).generics;

        let binder_env = ClauseImportEnv::new(
            Some(applies_to),
            [GenericSubst::new(binder, instance.params)],
        );

        let params_wf = instance
            .params
            .r(s)
            .iter()
            .zip(spans)
            .zip(&binder.r(s).defs)
            .map(|((&para, span), generic)| {
                let cause = cause.clone().child(ObligeCauseFrame::Origin(
                    ObligeCauseOrigin::ImportWfForGenericParam {
                        use_span: span,
                        clause_span: generic.span(s),
                    },
                ));

                (cause, para)
            });

        let param_truncation = match assoc_wf_mode {
            AssocParamWfMode::Check => None,
            AssocParamWfMode::Ignore => Some(*instance.def.r(s).regular_generic_count),
        };

        self.ccx.instantiate_infer().ensure_binder_params_wf(
            universe,
            binder,
            binder_env,
            param_truncation,
            params_wf,
        );
    }

    // === Spec drivers === //

    pub fn import_trait_clause_list(&mut self, clauses: SigTraitClauseList) -> TraitClauseList {
        let s = self.session();

        self.import_trait_clause_list_inner(clauses.elems.r(s))
    }

    pub fn import_trait_clause(&mut self, clause: SigTraitClause) -> TraitClause {
        let s = self.session();

        self.import_trait_clause_list_inner(&[clause]).r(s)[0]
    }

    pub fn import_hrtb_binder(&mut self, clause: SigHrtbBinder) -> HrtbBinder {
        let TraitClause::Trait(clause) = self.import_trait_clause(SigTraitClause {
            span: clause.defs_span,
            kind: SigTraitClauseKind::Trait(clause),
        }) else {
            unreachable!();
        };

        clause
    }

    pub fn import_trait_spec(&mut self, clause: SigTraitSpec) -> TraitSpec {
        let s = self.session();

        self.import_hrtb_binder(SigHrtbBinder {
            defs_span: clause.span,
            defs: Obj::new_slice(&[], s),
            inner: clause,
        })
        .inner
    }

    // === Inner === //

    fn should_do_clause_wf(&self) -> bool {
        // TODO: Not necessary if origin is delay bug
        self.opts.create_wf_obligations
    }

    fn import_trait_clause_list_inner(&mut self, clauses: &[SigTraitClause]) -> TraitClauseList {
        let s = self.session();
        let tcx = self.tcx();

        let wf_self_var = self.should_do_clause_wf().then(|| {
            self.ccx.fresh_ty_universal_var(
                self.opts.universe.clone(),
                UniversalTyVarSourceInfo::ClauseWfHelper {
                    clauses: Obj::new_slice(clauses, s),
                },
            )
        });

        let wf_self_ty = wf_self_var.map(|var| tcx.intern(TyKind::UniversalVar(var)));

        let clauses = self.import_trait_clause_list_with_self_ty(wf_self_ty, clauses);

        if let Some(wf_self_ty) = wf_self_var {
            self.ccx
                .init_ty_universal_var_direct_clauses(wf_self_ty, clauses);
        }

        clauses
    }

    fn import_trait_clause_list_with_self_ty(
        &mut self,
        wf_self_ty: Option<Ty>,
        clauses: &[SigTraitClause],
    ) -> TraitClauseList {
        let tcx = self.tcx();

        let clauses = clauses
            .iter()
            .map(|&clause| self.import_trait_clause_with_self_ty(wf_self_ty, clause))
            .collect::<Vec<_>>();

        tcx.intern_list(&clauses)
    }

    fn import_trait_clause_with_self_ty(
        &mut self,
        wf_self_ty: Option<Ty>,
        clause: SigTraitClause,
    ) -> TraitClause {
        match clause.kind {
            SigTraitClauseKind::Outlives(dir, rhs) => {
                TraitClause::Outlives(dir, self.import_ty_or_re(rhs))
            }
            SigTraitClauseKind::Trait(binder) => {
                TraitClause::Trait(self.import_hrtb_binder_with_self_ty(wf_self_ty, binder))
            }
        }
    }

    fn import_hrtb_binder_with_self_ty(
        &mut self,
        wf_self_ty: Option<Ty>,
        binder: SigHrtbBinder,
    ) -> HrtbBinder {
        let s = self.session();
        let tcx = self.tcx();

        if binder.defs.r(s).is_empty() {
            return HrtbBinder {
                defs: tcx.intern_list(&[]),
                inner: self.import_trait_spec_with_self_ty(wf_self_ty, binder.inner),
            };
        }

        if let Some(wf_self_ty) = wf_self_ty {
            self.check_hrtb_binder_wf(wf_self_ty, binder);
        }

        // Enter nested universe
        let parent_env = self.opts.env.clone();
        let parent_universe = self.opts.universe.clone();
        let old_opts = mem::replace(
            &mut self.opts,
            SigImporterOpts {
                universe: parent_universe,
                env: parent_env,
                // Can't push WF obligations for types involving unsubstituted HRTB variables.
                create_wf_obligations: false,
                // Can't project until this HRTB binder is alleviated.
                defer_project_in_binder: true,
            },
        );

        let binders_pushed = self.hrtb_substs.push(binder.defs.r(s).iter().map(|_| None));

        // Import everything.
        let imported_binder = HrtbBinder {
            defs: tcx.intern_list(
                &binder
                    .defs
                    .r(s)
                    .iter()
                    .map(|def| HrtbDebruijnDef {
                        span: def.span,
                        name: def.name,
                        kind: def.kind,
                        clauses: self.import_trait_clause_list(def.clauses),
                    })
                    .collect::<Vec<_>>(),
            ),
            inner: self.import_trait_spec(binder.inner),
        };

        // Exit nested universe
        self.opts = old_opts;
        self.hrtb_substs.pop(binders_pushed);

        imported_binder
    }

    fn check_hrtb_binder_wf(&mut self, wf_self_ty: Ty, binder: SigHrtbBinder) {
        let s = self.session();

        let nested_universe = self.opts.universe.clone().nest(HrtbUniverseInfo {});

        // Spawn universals for each bound variable
        let hrtb_universals = binder
            .defs
            .r(s)
            .iter()
            .enumerate()
            .map(|(idx, def)| match def.kind {
                TyOrReKind::Re => TyOrRe::Re(self.ccx.fresh_re_universal(
                    UniversalReVarSourceInfo::HrtbWf {
                        binder,
                        idx: idx as u32,
                    },
                )),
                TyOrReKind::Ty => TyOrRe::Ty(self.ccx.fresh_ty_universal(
                    nested_universe.clone(),
                    UniversalTyVarSourceInfo::HrtbWf {
                        binder,
                        idx: idx as u32,
                    },
                )),
            })
            .collect::<Vec<_>>();

        // Enter nested universe
        let parent_env = self.opts.env.clone();
        let old_opts = mem::replace(
            &mut self.opts,
            SigImporterOpts {
                universe: nested_universe.clone(),
                env: parent_env,
                // We went through all this effort to spawn WF obligations, after all.
                create_wf_obligations: true,
                // We want to reveal projection errors.
                defer_project_in_binder: false,
            },
        );

        let binders_pushed = self
            .hrtb_substs
            .push(hrtb_universals.iter().map(|&v| Some(v)));

        // WF-check each bound variable, initializing their corresponding universal.
        for (def, &var) in binder.defs.r(s).iter().zip(&hrtb_universals) {
            let clauses = self.import_trait_clause_list_with_self_ty(
                // N.B. if we're working with a region, it is safe not to pass an `wf_self_ty` because
                // it will never be used because we'll never try to expand an HRTB binder. It also just
                // wouldn't make any sense to pass.
                var.as_ty(),
                def.clauses.elems.r(s),
            );

            self.ccx.init_any_universal_var_direct_clauses(var, clauses);
        }

        // WF-check the main body.
        let bound = self.import_trait_spec_with_self_ty(Some(wf_self_ty), binder.inner);

        self.ccx.oblige_covered(
            self.cause.clone(),
            /* must_mention */
            hrtb_universals
                .iter()
                .filter_map(|ty_or_re| ty_or_re.as_ty())
                .map(|ty| {
                    let TyKind::UniversalVar(var) = *ty.r(s) else {
                        unreachable!()
                    };

                    var
                }),
            /* in_type */ None,
            /* in_trait */ Some(bound),
        );

        // Exit nested universe
        self.opts = old_opts;
        self.hrtb_substs.pop(binders_pushed);
    }

    fn import_trait_spec_with_self_ty(
        &mut self,
        wf_self_ty: Option<Ty>,
        spec: SigTraitSpec,
    ) -> TraitSpec {
        let s = self.session();
        let tcx = self.tcx();

        // Let's begin by importing this spec directly.
        let spec_imported = TraitSpec {
            def: spec.def,
            params: tcx.intern_list(
                &spec
                    .params
                    .r(s)
                    .iter()
                    .map(|para| match para.kind {
                        SigTraitParamKind::Equals(ty_or_re) => {
                            TraitParam::Equals(self.import_ty_or_re(ty_or_re))
                        }
                        SigTraitParamKind::Unspecified(clauses) => {
                            TraitParam::Unspecified(self.import_trait_clause_list(clauses))
                        }
                    })
                    .collect::<Vec<_>>(),
            ),
        };

        // Now, we can optionally perform WF checks on it.
        let Some(wf_self_ty) = wf_self_ty else {
            return spec_imported;
        };

        // We instantiate the `spec` as an instance to ensure that each associated type inference
        // variable is bound such that it projects to `applies_to`'s substitution.
        //
        // Consider the following program...
        //
        // ```
        // trait Meow<T: Thump<Self::Other>> {
        //     type Other;
        // }
        //
        // trait Thump<T> {}
        //
        // impl Thump<i32> for u32 {}
        // impl Thump<u32> for u32 {}
        //
        // trait Funny {
        //     type Hehe: Meow<u32>;
        // }
        // ```
        //
        // It should be rejected because an implementation of `Funny` could set `Hehe` to a type
        // that implements `Meow` with an `Other` which is neither `i32` nor `u32`.
        //
        // Meanwhile, a program like this should pass...
        //
        // ```
        // // --- snip ---
        //
        // trait Funny {
        //     type Hehe: Meow<u32> + Meow<u32, Other = u32>;
        // }
        // ```
        //
        // If we didn't bind the inference variable in the first `Meow<u32, Other: <unspec>>` spec,
        // we would fail to prove that `u32: Thump<?infer helper>` with an ambiguity error. However,
        // by binding the projection, we gain knowledge of `Other`'s binding within another clause.
        //
        // Note that obligation alone is not sufficient for well-formedness because the universal
        // type we synthesize for WF-checking the `Funny` trait has the universal specification
        // `Self: Funny<u32, Other: <existential>>`, which would allow this `impl` to trivially pass
        // using inherent type impl rules.
        //
        // We can't make `cause` a delay bug because we could construct edge cases such as...
        //
        // ```
        // // --- snip ---
        //
        // trait Funny {
        //     type Hehe: Meow<u32> + Meow<u32, Other = u32> + Meow<u32, Other = i32>;
        // }
        // ```
        //
        // ...where the last clause fails to pass its self obligation because the earlier clause
        // takes priority.
        let instance = self.ccx.instantiate_infer().resolve_trait_spec(
            &self.cause,
            &self.opts.universe,
            wf_self_ty,
            spec_imported,
        );

        // Check the parameters.
        let spans = spec
            .params
            .r(s)
            .iter()
            .take(*spec.def.r(s).regular_generic_count as usize)
            .map(|v| v.span);

        self.ensure_trait_instance_args_wf_no_self_obligation(
            &self.cause.clone(),
            &self.opts.universe.clone(),
            wf_self_ty,
            spans,
            instance,
            // We don't verify the well-formedness of the associated types within a spec to be
            // consistent with rustc's behavior, which seems to exist to make a few common patterns
            // work. This is fine because, if the associated type is not WF, no impl for it will
            // exist.
            AssocParamWfMode::Ignore,
        );

        spec_imported
    }
}

// === HrtbInstantiator === //

impl ClauseCx<'_> {
    pub fn instantiate_hrtb_universal(
        &mut self,
        cause: &ObligeCause,
        universe: HrtbUniverse,
        value: HrtbBinder,
    ) -> TraitSpec {
        let s = self.session();
        let tcx = self.tcx();

        let HrtbBinder { defs, inner } = value;

        // Make up new universal variables for our binder.
        let vars = defs
            .r(s)
            .iter()
            .map(|def| match def.kind {
                TyOrReKind::Re => {
                    TyOrRe::Re(self.fresh_re_universal(UniversalReVarSourceInfo::HrtbVar))
                }
                TyOrReKind::Ty => TyOrRe::Ty(
                    self.fresh_ty_universal(universe.clone(), UniversalTyVarSourceInfo::HrtbVar),
                ),
            })
            .collect::<Vec<_>>();

        let vars = tcx.intern_list(&vars);

        // Initialize their clauses.
        for (&def, &var) in defs.r(s).iter().zip(vars.r(s)) {
            let clauses = HrtbInstantiator::new(self, cause, vars).fold(def.clauses);

            self.init_any_universal_var_direct_clauses(var, clauses);
        }

        HrtbInstantiator::new(self, cause, vars).fold(inner)
    }

    pub fn instantiate_hrtb_infer(
        &mut self,
        cause: ObligeCause,
        universe: HrtbUniverse,
        value: HrtbBinder,
    ) -> TraitSpec {
        let tcx = self.tcx();
        let s = self.session();

        let HrtbBinder { defs, inner } = value;

        // Make up new inference variables for our binder.
        let vars = defs
            .r(s)
            .iter()
            .map(|def| match def.kind {
                TyOrReKind::Re => TyOrRe::Re(self.fresh_re_infer()),
                TyOrReKind::Ty => TyOrRe::Ty(self.fresh_ty_infer(
                    universe.clone(),
                    InferTyVarSourceInfo::HrtbLhsInstantiation {
                        span: def.span,
                        clauses: LateInit::uninit(),
                    },
                )),
            })
            .collect::<Vec<_>>();

        let vars = tcx.intern_list(&vars);

        // Constrain the new inference variables with their obligations.
        for (&def, &var) in defs.r(s).iter().zip(vars.r(s)) {
            let clauses = HrtbInstantiator::new(self, &cause, vars).fold(def.clauses);

            let cause = cause.clone().child(
                ObligeCauseStep::HrtbExistentialInferenceIsPossible {
                    lhs: var,
                    rhs: clauses,
                }
                .into(),
            );

            match var {
                TyOrRe::Re(var) => {
                    self.oblige_re_meets_clauses(&cause, var, clauses);
                }
                TyOrRe::Ty(var) => {
                    self.oblige_ty_meets_clauses(&cause, &universe, var, clauses);

                    let TyKind::InferVar(var) = *var.r(s) else {
                        unreachable!()
                    };

                    let InferTyVarSourceInfo::HrtbLhsInstantiation {
                        clauses: clauses_late_init,
                        ..
                    } = self.lookup_infer_ty_src_info(var)
                    else {
                        unreachable!()
                    };

                    LateInit::init(&clauses_late_init, clauses);
                }
            }
        }

        // Fold the inner type
        HrtbInstantiator::new(self, &cause, vars).fold(inner)
    }
}

struct HrtbInstantiator<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    cause: &'a ObligeCause,
    replace_with: TyOrReList,
    top: DebruijnTop,
}

impl<'a, 'tcx> HrtbInstantiator<'a, 'tcx> {
    pub fn new(
        ccx: &'a mut ClauseCx<'tcx>,
        cause: &'a ObligeCause,
        replace_with: TyOrReList,
    ) -> Self {
        let s = ccx.session();

        Self {
            ccx,
            cause,
            replace_with,
            top: DebruijnTop::new(replace_with.r(s).len()),
        }
    }

    pub fn replace_with(&self) -> TyOrReList {
        self.replace_with
    }
}

impl<'tcx> TyFolder<'tcx> for HrtbInstantiator<'_, 'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn fold_hrtb_binder(&mut self, binder: HrtbBinder) -> Result<HrtbBinder, Self::Error> {
        let s = self.session();

        let bind_count = binder.defs.r(s).len();

        self.top.move_inwards_by(bind_count);
        let inner = self.super_(binder.inner);
        self.top.move_outwards_by(bind_count);

        Ok(HrtbBinder {
            defs: binder.defs,
            inner,
        })
    }

    fn fold_ty(&mut self, ty: Ty) -> Result<Ty, Self::Error> {
        let s = self.session();

        let ty = self.super_(ty);

        match *ty.r(s) {
            TyKind::HrtbVar(var) => {
                let abs = self.top.lookup_relative(var.0).index();

                if abs < self.replace_with.r(s).len() {
                    return Ok(self.replace_with.r(s)[abs].unwrap_ty());
                }
            }
            TyKind::HrtbProjection(HrtbProjection {
                target,
                spec,
                assoc_idx,
            }) if self.top.len() == self.replace_with.r(s).len() => {
                let instance = self.ccx.instantiate_infer().resolve_trait_spec(
                    &self.cause.clone().into_delay_bug(),
                    HrtbUniverse::ROOT_REF,
                    target,
                    spec,
                );

                return Ok(instance.params.r(s)[assoc_idx as usize].unwrap_ty());
            }
            _ => {
                // (fallthrough)
            }
        }

        Ok(self.super_(ty))
    }

    fn fold_re(&mut self, re: Re) -> Result<Re, Self::Error> {
        let s = self.session();

        if let Re::HrtbVar(var) = re {
            let abs = self.top.lookup_relative(var.0).index();

            if abs < self.replace_with.r(s).len() {
                return Ok(self.replace_with.r(s)[abs].unwrap_re());
            }
        }

        Ok(self.super_(re))
    }
}
