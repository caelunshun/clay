use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Session,
        analysis::{DebruijnMap, DebruijnTop},
        arena::{HasInterner, HasListInterner, LateInit, Obj},
        syntax::Span,
    },
    semantic::{
        infer::{
            ClauseCx, ClauseFuel, HrtbInferParamNotValid, HrtbInferParamNotValidKind, HrtbUniverse,
            HrtbUniverseInfo, ImportError, InstantiateHrtbInferError,
            InstantiateHrtbUniversalError, MultiPromise, MultiPromiseBuilder, MultiPromiseValue,
            PromiseValue, TraitSpecResolutionError, UnifyCxMode,
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
    typed_joiner,
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

pub type ImportPromise<'tcx, T> = MultiPromiseValue<'tcx, T, ImportError>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ImportWfMode {
    ReportHere,
    ReportElsewhere,
}

impl ImportWfMode {
    pub fn do_wf(self) -> bool {
        matches!(self, Self::ReportHere)
    }
}

impl<'tcx> ClauseCx<'tcx> {
    pub fn importer(
        &mut self,
        fuel: ClauseFuel,
        universe: HrtbUniverse,
        env: ClauseImportEnv,
        wf_mode: ImportWfMode,
    ) -> SigImporter<'_, 'tcx> {
        SigImporter {
            ccx: self,
            fuel,
            opts: SigImporterOpts {
                universe,
                env,
                wf_mode,
                // We're not in a binder.
                defer_project_in_binder: false,
            },
            reentrant_aliases: FxHashMap::default(),
            hrtb_substs: DebruijnMap::default(),
        }
    }

    pub fn importer_here(&mut self, env: &ClauseImportEnv) -> SigImporter<'_, 'tcx> {
        self.importer(
            ClauseFuel::new(),
            HrtbUniverse::ROOT,
            env.clone(),
            ImportWfMode::ReportHere,
        )
    }

    pub fn importer_elsewhere(&mut self, env: &ClauseImportEnv) -> SigImporter<'_, 'tcx> {
        self.importer(
            ClauseFuel::new(),
            HrtbUniverse::ROOT,
            env.clone(),
            ImportWfMode::ReportElsewhere,
        )
    }

    pub fn import_here<I: SigImportable<'tcx>>(
        &mut self,
        env: &ClauseImportEnv,
        target: I,
    ) -> I::Output {
        self.importer_here(env).import(target).report_loud()
    }

    pub fn import_elsewhere<I: SigImportable<'tcx>>(
        &mut self,
        env: &ClauseImportEnv,
        target: I,
    ) -> I::Output {
        self.importer_elsewhere(env)
            .import(target)
            // We're performing this import with zero spent fuel so it should succeed *iff* the WF
            // import also succeeds.
            .report_delay_bug()
    }
}

pub trait SigImportable<'tcx>: Sized {
    type Output;

    fn import(
        me: Self,
        importer: &mut SigImporter<'_, 'tcx>,
    ) -> MultiPromiseValue<'tcx, Self::Output, ImportError>;
}

macro_rules! impl_sig_importable {
    ( $( $method:ident: $src:ty => $dest:ty; )* ) => {$(
        impl<'tcx> SigImportable<'tcx> for $src {
            type Output = $dest;

            fn import(
                me: Self,
                importer: &mut SigImporter<'_, 'tcx>,
            ) -> MultiPromiseValue<'tcx, Self::Output, ImportError> {
                importer.$method(me)
            }
        }
    )*};
}

impl_sig_importable! {
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
    fuel: ClauseFuel,
    opts: SigImporterOpts,
    reentrant_aliases: FxHashMap<Obj<TypeAliasItem>, ReentrantAliasState>,
    hrtb_substs: DebruijnMap<Option<TyOrRe>>,
}

struct SigImporterOpts {
    universe: HrtbUniverse,
    env: ClauseImportEnv,
    wf_mode: ImportWfMode,
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

    pub fn import<I: SigImportable<'tcx>>(&mut self, item: I) -> ImportPromise<'tcx, I::Output> {
        I::import(item, self)
    }

    pub fn import_ty_list(&mut self, tys: SigTyList) -> ImportPromise<'tcx, TyList> {
        let s = self.session();
        let tcx = self.tcx();

        let mut collector = MultiPromiseBuilder::new();

        let output = tcx.intern_list(
            &tys.r(s)
                .iter()
                .map(|ty| self.import_ty(*ty).flat_join(&mut collector))
                .collect::<Vec<_>>(),
        );

        collector.finish().and_value(output)
    }

    pub fn import_ty_or_re_list(
        &mut self,
        ty_or_res: SigTyOrReList,
    ) -> ImportPromise<'tcx, TyOrReList> {
        let s = self.session();
        let tcx = self.tcx();

        let mut collector = MultiPromiseBuilder::new();

        let output = tcx.intern_list(
            &ty_or_res
                .r(s)
                .iter()
                .map(|ty| self.import_ty_or_re(*ty).flat_join(&mut collector))
                .collect::<Vec<_>>(),
        );

        collector.finish().and_value(output)
    }

    pub fn import_ty_or_re(&mut self, ty_or_re: SigTyOrRe) -> ImportPromise<'tcx, TyOrRe> {
        match ty_or_re {
            SigTyOrRe::Re(re) => self.import_re(re).map_value(TyOrRe::Re),
            SigTyOrRe::Ty(ty) => self.import_ty(ty).map_value(TyOrRe::Ty),
        }
    }

    pub fn import_ty(&mut self, ty: SigTy) -> ImportPromise<'tcx, Ty> {
        let s = self.session();
        let tcx = self.tcx();

        let mut collector = MultiPromiseBuilder::new();

        let output = match ty.r(s).kind {
            // Parameterized (may require WF)
            SigTyKind::Alias(def, args) => 'output: {
                let s = self.session();
                let tcx = self.tcx();

                // Import the type alias's arguments.
                let args = self
                    .import_simple_generic_args(def.r(s).generics, args, FixArity::AssumeCorrect)
                    .flat_join(&mut collector);

                // Prevent reentrant alias resolution (preorder).
                match self.reentrant_aliases.entry(def) {
                    hash_map::Entry::Occupied(entry) => {
                        let entry = entry.into_mut();

                        if matches!(entry, ReentrantAliasState::WaitingForViolation) {
                            *entry = ReentrantAliasState::Violated(ty.r(s).span);
                        }

                        break 'output tcx.intern(TyKind::Error(ErrorGuaranteed::new_unchecked()));
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
                        wf_mode: ImportWfMode::ReportElsewhere,
                        defer_project_in_binder: parent_defer_project_in_binder,
                    },
                );

                // Subtle: we defer emission of reentrancy errors into the root context to ensure
                // that they're aren't accidentally suppressed by the delay bug.
                let body = self.import_ty(*def.r(s).body).flat_join(&mut collector);

                self.opts = old_opts;

                // Prevent reentrant alias resolution (postorder).
                // TODO: integrate with promises
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
                let re = self.import_re(re).flat_join(&mut collector);
                let pointee = self.import_ty(pointee).flat_join(&mut collector);

                if self.opts.wf_mode.do_wf() {
                    self.ccx
                        .oblige_ty_outlives_re(pointee, re, RelationDirection::LhsOntoRhs)
                        .map(move |_ccx, error| ImportError::BadRefPointee {
                            ty,
                            error: Box::new(error),
                        })
                        .join(&mut collector);
                }

                tcx.intern(TyKind::Reference(re, muta, pointee))
            }
            SigTyKind::Adt(adt) => {
                tcx.intern(TyKind::Adt(self.import_adt(adt).flat_join(&mut collector)))
            }
            SigTyKind::Trait(re, muta, clauses) => {
                let re = self.import_re(re).flat_join(&mut collector);

                let clauses = self
                    .import_trait_clause_list(clauses)
                    .flat_join(&mut collector);

                let object_ty = tcx.intern(TyKind::Trait(re, muta, clauses));

                object_ty
            }
            SigTyKind::Tuple(tys) => {
                let tys = self.import_ty_list(tys).flat_join(&mut collector);

                if self.opts.wf_mode.do_wf() {
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

            SigTyKind::Project(
                ty @ SigProjectType {
                    target,
                    spec,
                    assoc_span: _,
                    assoc_idx,
                },
            ) => 'output: {
                let target = self.import_ty(target).flat_join(&mut collector);

                let spec_imported = self.import_trait_spec(spec).flat_join(&mut collector);

                if self.opts.defer_project_in_binder {
                    break 'output tcx.intern(TyKind::HrtbProjection(HrtbProjection {
                        target: target,
                        spec: spec_imported,
                        assoc_idx,
                    }));
                }

                let instance = self
                    .ccx
                    .resolve_trait_spec(self.fuel, &self.opts.universe, target, spec_imported)
                    .filter_map(move |_ccx, error| {
                        // TODO: filter if we're in no-WF mode

                        Ok(ImportError::Projection {
                            ty,
                            error: Box::new(error),
                        })
                    })
                    .join(&mut collector);

                // We don't do a `ensure_trait_instance_args_wf_no_self_obligation` here because the
                // diagnostic produced by `instantiate_trait_spec` should be enough to warn users.

                instance.params.r(s)[assoc_idx as usize].unwrap_ty()
            }

            SigTyKind::Error(err) => tcx.intern(TyKind::Error(err)),
        };

        collector.finish().and_value(output)
    }

    pub fn import_re(&mut self, re: SigRe) -> ImportPromise<'tcx, Re> {
        let s = self.session();

        if self.ccx.mode() == UnifyCxMode::RegionBlind {
            return PromiseValue::trivial(Re::Erased);
        }

        let output = match re.kind {
            SigReKind::Gc => Re::Gc,
            SigReKind::HrtbVar(idx) => match self.hrtb_substs.lookup(idx.0) {
                Some(real_subst) => real_subst.unwrap_re(),
                None => Re::HrtbVar(idx),
            },
            SigReKind::Infer => self.ccx.fresh_re_infer(),
            SigReKind::Generic(generic) => self.opts.env.lookup_re(s, generic),
            SigReKind::Error(err) => Re::Error(err),
        };

        PromiseValue::trivial(output)
    }

    pub fn import_adt(&mut self, adt: SigAdtInstance) -> ImportPromise<'tcx, AdtInstance> {
        let s = self.session();

        let mut collector = MultiPromiseBuilder::new();

        let output = AdtInstance {
            def: adt.def,
            params: self
                .import_simple_generic_args(
                    adt.def.r(s).generics,
                    adt.params,
                    FixArity::AssumeCorrect,
                )
                .flat_join(&mut collector),
        };

        collector.finish().and_value(output)
    }

    pub fn import_fn_instance_from_owner(
        &mut self,
        owner: FnOwner,
        args: Option<SigGenericList>,
        fix_arity: FixArity,
    ) -> ImportPromise<'tcx, FnInstance> {
        let s = self.session();
        let tcx = self.tcx();

        let mut collector = MultiPromiseBuilder::new();

        let early_args = args.map(|args| match owner {
            FnOwner::Item(def) => self
                .import_simple_generic_args(def.r(s).def.r(s).generics, args, fix_arity)
                .flat_join(&mut collector),
            FnOwner::Trait(
                owner @ FnOwnerTrait {
                    instance,
                    self_ty,
                    method_idx,
                },
            ) => {
                let instance = self
                    .ccx
                    .resolve_trait_spec(self.fuel, &self.opts.universe, self_ty, instance)
                    .filter_map(move |_ccx, error| {
                        // TODO: filter if we're in no-WF mode

                        Ok(ImportError::TraitFnOwner {
                            owner,
                            error: Box::new(error),
                        })
                    })
                    .join(&mut collector);

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
                .flat_join(&mut collector)
            }
            FnOwner::Inherent(
                owner @ FnOwnerInherent {
                    self_ty,
                    block,
                    method_idx,
                },
            ) => {
                let block_args = self
                    .ccx
                    .resolve_inherent_impl_block_env(self.fuel, &self.opts.universe, block, self_ty)
                    .filter_map(move |_ccx, error| {
                        // TODO: filter if we're in no-WF mode

                        Ok(ImportError::InherentBlockEnv {
                            owner,
                            error: Box::new(error),
                        })
                    })
                    .join(&mut collector)
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
                .flat_join(&mut collector)
            }
            FnOwner::AdtCtor(FnOwnerAdtCtor { ctor }) => self
                .import_simple_generic_args(ctor.r(s).owner.item(s).r(s).generics, args, fix_arity)
                .flat_join(&mut collector),
        });

        collector
            .finish()
            .and_value(tcx.intern(FnInstanceInner { owner, early_args }))
    }

    fn import_simple_generic_args(
        &mut self,
        binder: Obj<GenericBinder>,
        args: SigGenericList,
        fix_arity: FixArity,
    ) -> ImportPromise<'tcx, TyOrReList> {
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
    ) -> ImportPromise<'tcx, TyOrReList> {
        let tcx = self.tcx();
        let s = self.session();

        let mut collector = MultiPromiseBuilder::new();

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

        let args_imported = self
            .import_ty_or_re_list(args.elems)
            .flat_join(&mut collector);

        if self.opts.wf_mode.do_wf() {
            let env = make_env(args_imported);

            self.ccx
                .ensure_binder_params_wf(
                    self.fuel,
                    &self.opts.universe,
                    binder,
                    env.clone(),
                    None,
                    args_imported,
                )
                .map(move |_ccx, error| ImportError::BadGenerics {
                    binder,
                    env,
                    args,
                    error: Box::new(error),
                })
                .join(&mut collector);
        }

        collector.finish().and_value(args_imported)
    }
}

/// Traits
impl<'a, 'tcx> SigImporter<'a, 'tcx> {
    // === Instance logic === //

    pub fn import_trait_instance(
        &mut self,
        instance_applies_to: Ty,
        instance: SigTraitInstance,
    ) -> ImportPromise<'tcx, TraitInstance> {
        let s = self.session();

        let binder = *instance.def.r(s).generics;

        self.import_generic_args(binder, instance.params, FixArity::AssumeCorrect, |args| {
            ClauseImportEnv::new(Some(instance_applies_to), [GenericSubst::new(binder, args)])
        })
        .map_value(|params| TraitInstance {
            def: instance.def,
            params,
        })
    }

    // === Spec drivers === //

    pub fn import_trait_clause_list(
        &mut self,
        clauses: SigTraitClauseList,
    ) -> ImportPromise<'tcx, TraitClauseList> {
        let s = self.session();

        self.import_trait_clause_list_inner(clauses.elems.r(s))
    }

    pub fn import_trait_clause(
        &mut self,
        clause: SigTraitClause,
    ) -> ImportPromise<'tcx, TraitClause> {
        let s = self.session();

        self.import_trait_clause_list_inner(&[clause])
            .map_value(|v| v.r(s)[0])
    }

    pub fn import_hrtb_binder(&mut self, clause: SigHrtbBinder) -> ImportPromise<'tcx, HrtbBinder> {
        self.import_trait_clause(SigTraitClause {
            span: clause.defs_span,
            kind: SigTraitClauseKind::Trait(clause),
        })
        .map_value(|v| {
            let TraitClause::Trait(clause) = v else {
                unreachable!()
            };

            clause
        })
    }

    pub fn import_trait_spec(&mut self, clause: SigTraitSpec) -> ImportPromise<'tcx, TraitSpec> {
        let s = self.session();

        self.import_hrtb_binder(SigHrtbBinder {
            defs_span: clause.span,
            defs: Obj::new_slice(&[], s),
            inner: clause,
        })
        .map_value(|v| v.inner)
    }

    // === Inner === //

    fn import_trait_clause_list_inner(
        &mut self,
        clauses: &[SigTraitClause],
    ) -> ImportPromise<'tcx, TraitClauseList> {
        let s = self.session();
        let tcx = self.tcx();

        let mut collector = MultiPromiseBuilder::new();

        let wf_self_var = self.opts.wf_mode.do_wf().then(|| {
            self.ccx.fresh_ty_universal_var(
                self.opts.universe.clone(),
                UniversalTyVarSourceInfo::ClauseWfHelper {
                    clauses: Obj::new_slice(clauses, s),
                },
            )
        });

        let wf_self_ty = wf_self_var.map(|var| tcx.intern(TyKind::UniversalVar(var)));

        let clauses = self
            .import_trait_clause_list_with_self_ty(wf_self_ty, clauses)
            .flat_join(&mut collector);

        if let Some(wf_self_ty) = wf_self_var {
            self.ccx
                .init_ty_universal_var_direct_clauses(wf_self_ty, clauses);
        }

        collector.finish().and_value(clauses)
    }

    fn import_trait_clause_list_with_self_ty(
        &mut self,
        wf_self_ty: Option<Ty>,
        clauses: &[SigTraitClause],
    ) -> ImportPromise<'tcx, TraitClauseList> {
        let tcx = self.tcx();

        let mut collector = MultiPromiseBuilder::new();

        let clauses = clauses
            .iter()
            .map(|&clause| {
                self.import_trait_clause_with_self_ty(wf_self_ty, clause)
                    .flat_join(&mut collector)
            })
            .collect::<Vec<_>>();

        collector.finish().and_value(tcx.intern_list(&clauses))
    }

    fn import_trait_clause_with_self_ty(
        &mut self,
        wf_self_ty: Option<Ty>,
        clause: SigTraitClause,
    ) -> ImportPromise<'tcx, TraitClause> {
        match clause.kind {
            SigTraitClauseKind::Outlives(dir, rhs) => self
                .import_ty_or_re(rhs)
                .map_value(|v| TraitClause::Outlives(dir, v)),
            SigTraitClauseKind::Trait(binder) => self
                .import_hrtb_binder_with_self_ty(wf_self_ty, binder)
                .map_value(TraitClause::Trait),
        }
    }

    fn import_hrtb_binder_with_self_ty(
        &mut self,
        wf_self_ty: Option<Ty>,
        binder: SigHrtbBinder,
    ) -> ImportPromise<'tcx, HrtbBinder> {
        let s = self.session();
        let tcx = self.tcx();

        if binder.defs.r(s).is_empty() {
            let PromiseValue {
                value: inner,
                promise: inner_promise,
            } = self.import_trait_spec_with_self_ty(wf_self_ty, binder.inner);

            return inner_promise.and_value(HrtbBinder {
                defs: tcx.intern_list(&[]),
                inner,
            });
        }

        let mut collector = MultiPromiseBuilder::new();

        if let Some(wf_self_ty) = wf_self_ty {
            self.check_hrtb_binder_wf(wf_self_ty, binder)
                .flat_join(&mut collector);
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
                wf_mode: ImportWfMode::ReportElsewhere,
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
                        clauses: self
                            .import_trait_clause_list(def.clauses)
                            .flat_join(&mut collector),
                    })
                    .collect::<Vec<_>>(),
            ),
            inner: self
                .import_trait_spec(binder.inner)
                .flat_join(&mut collector),
        };

        // Exit nested universe
        self.opts = old_opts;
        self.hrtb_substs.pop(binders_pushed);

        collector.finish().and_value(imported_binder)
    }

    fn check_hrtb_binder_wf(
        &mut self,
        wf_self_ty: Ty,
        binder: SigHrtbBinder,
    ) -> MultiPromise<'tcx, ImportError> {
        let s = self.session();

        let mut collector = MultiPromiseBuilder::new();

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
                wf_mode: ImportWfMode::ReportHere,
                // We want to reveal projection errors.
                defer_project_in_binder: false,
            },
        );

        let binders_pushed = self
            .hrtb_substs
            .push(hrtb_universals.iter().map(|&v| Some(v)));

        // WF-check each bound variable, initializing their corresponding universal.
        for (def, &var) in binder.defs.r(s).iter().zip(&hrtb_universals) {
            let clauses = self
                .import_trait_clause_list_with_self_ty(
                    // N.B. if we're working with a region, it is safe not to pass an `wf_self_ty` because
                    // it will never be used because we'll never try to expand an HRTB binder. It also just
                    // wouldn't make any sense to pass.
                    var.as_ty(),
                    def.clauses.elems.r(s),
                )
                .flat_join(&mut collector);

            self.ccx.init_any_universal_var_direct_clauses(var, clauses);
        }

        // WF-check the main body.
        let bound = self
            .import_trait_spec_with_self_ty(Some(wf_self_ty), binder.inner)
            .flat_join(&mut collector);

        self.ccx
            .oblige_covered(
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
            )
            .map(move |_ccx, error| ImportError::HrtbNotCovered {
                binder,
                error: Box::new(error),
            })
            .join(&mut collector);

        // Exit nested universe
        self.opts = old_opts;
        self.hrtb_substs.pop(binders_pushed);

        collector.finish()
    }

    fn import_trait_spec_with_self_ty(
        &mut self,
        wf_self_ty: Option<Ty>,
        spec: SigTraitSpec,
    ) -> ImportPromise<'tcx, TraitSpec> {
        let s = self.session();
        let tcx = self.tcx();

        let mut collector = MultiPromiseBuilder::new();

        // Let's begin by importing this spec directly.
        let spec_imported = TraitSpec {
            def: spec.def,
            params: tcx.intern_list(
                &spec
                    .params
                    .r(s)
                    .iter()
                    .map(|para| match para.kind {
                        SigTraitParamKind::Equals(ty_or_re) => TraitParam::Equals(
                            self.import_ty_or_re(ty_or_re).flat_join(&mut collector),
                        ),
                        SigTraitParamKind::Unspecified(clauses) => TraitParam::Unspecified(
                            self.import_trait_clause_list(clauses)
                                .flat_join(&mut collector),
                        ),
                    })
                    .collect::<Vec<_>>(),
            ),
        };

        // Now, we can optionally perform WF checks on it.
        let Some(wf_self_ty) = wf_self_ty else {
            return collector.finish().and_value(spec_imported);
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
        let instance = self
            .ccx
            .resolve_trait_spec(self.fuel, &self.opts.universe, wf_self_ty, spec_imported)
            .filter_map(move |_ccx, error| {
                // No filtering needed because we know we're in WF mode.
                Ok(ImportError::NoShadowImpl {
                    error: Box::new(error),
                })
            })
            .join(&mut collector);

        // Check the parameters.
        let binder = *instance.def.r(s).generics;

        self.ccx
            .ensure_binder_params_wf(
                self.fuel,
                &self.opts.universe,
                binder,
                ClauseImportEnv::new(
                    Some(wf_self_ty),
                    [GenericSubst::new(binder, instance.params)],
                ),
                Some(*instance.def.r(s).regular_generic_count),
                instance.params,
            )
            .map(move |_ccx, error| ImportError::BadTraitSpec {
                spec,
                error: Box::new(error),
            })
            .join(&mut collector);

        collector.finish().and_value(spec_imported)
    }
}

// === HrtbInstantiator === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn instantiate_hrtb_universal(
        &mut self,
        fuel: ClauseFuel,
        universe: HrtbUniverse,
        value: HrtbBinder,
    ) -> PromiseValue<'tcx, TraitSpec, InstantiateHrtbUniversalError> {
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

        let mut normalize_errors = MultiPromiseBuilder::new();

        // Initialize their clauses.
        for (&def, &var) in defs.r(s).iter().zip(vars.r(s)) {
            let clauses =
                HrtbInstantiator::new(self, &mut normalize_errors, fuel, vars).fold(def.clauses);

            self.init_any_universal_var_direct_clauses(var, clauses);
        }

        let output = HrtbInstantiator::new(self, &mut normalize_errors, fuel, vars).fold(inner);

        let promise = normalize_errors
            .finish()
            .map(
                move |_ccx, normalize_errors| InstantiateHrtbUniversalError {
                    value,
                    normalize_errors,
                },
            );

        promise.and_value(output)
    }

    pub fn instantiate_hrtb_infer(
        &mut self,
        fuel: ClauseFuel,
        universe: HrtbUniverse,
        value: HrtbBinder,
    ) -> PromiseValue<'tcx, TraitSpec, InstantiateHrtbInferError> {
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

        let mut param_not_valid_collector = MultiPromiseBuilder::new();
        let mut normalize_error_collector = MultiPromiseBuilder::new();

        // Constrain the new inference variables with their obligations.
        for (idx, (&def, &var)) in defs.r(s).iter().zip(vars.r(s)).enumerate() {
            let clauses = HrtbInstantiator::new(self, &mut normalize_error_collector, fuel, vars)
                .fold(def.clauses);

            match var {
                TyOrRe::Re(var) => {
                    self.oblige_re_meets_clauses(var, clauses)
                        .map(move |_ccx, error| HrtbInferParamNotValid {
                            idx: idx as u32,
                            kind: HrtbInferParamNotValidKind::RegionNotMet(error),
                        })
                        .join(&mut param_not_valid_collector);
                }
                TyOrRe::Ty(var) => {
                    self.oblige_ty_meets_clauses(fuel, &universe, var, clauses)
                        .map(move |_ccx, error| HrtbInferParamNotValid {
                            idx: idx as u32,
                            kind: HrtbInferParamNotValidKind::TyNotMet(error),
                        })
                        .join(&mut param_not_valid_collector);

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
        let output =
            HrtbInstantiator::new(self, &mut normalize_error_collector, fuel, vars).fold(inner);

        let promise = typed_joiner! {
            let param_not_valid = param_not_valid_collector.finish();
            let normalize_errors = normalize_error_collector.finish();

            |ccx| InstantiateHrtbInferError {
                value,
                param_not_valid: param_not_valid.unwrap_or_default(),
                normalize_errors: normalize_errors.unwrap_or_default(),
            }
        };

        promise.and_value(output)
    }
}

struct HrtbInstantiator<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    normalize_errors: &'a mut MultiPromiseBuilder<'tcx, TraitSpecResolutionError>,
    fuel: ClauseFuel,
    replace_with: TyOrReList,
    top: DebruijnTop,
}

impl<'a, 'tcx> HrtbInstantiator<'a, 'tcx> {
    fn new(
        ccx: &'a mut ClauseCx<'tcx>,
        normalize_errors: &'a mut MultiPromiseBuilder<'tcx, TraitSpecResolutionError>,
        fuel: ClauseFuel,
        replace_with: TyOrReList,
    ) -> Self {
        let s = ccx.session();

        Self {
            ccx,
            normalize_errors,
            fuel,
            replace_with,
            top: DebruijnTop::new(replace_with.r(s).len()),
        }
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
                let instance = self
                    .ccx
                    .resolve_trait_spec(self.fuel, HrtbUniverse::ROOT_REF, target, spec)
                    .filter_map(move |_ccx, error| {
                        // TODO: filter non-fuel errors

                        Ok(error)
                    })
                    .join(self.normalize_errors);

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
