use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Session,
        arena::{HasInterner, HasListInterner, Obj},
        syntax::Span,
    },
    semantic::{
        infer::{ClauseCx, HrtbUniverse, ObligeCause, UnifyCxMode},
        syntax::{
            AdtInstance, AnyGeneric, GenericBinder, HrtbBinder, InferTyVarSourceInfo, Re,
            RegionGeneric, SigAdtInstance, SigProjectType, SigRe, SigReKind, SigTraitClause,
            SigTraitClauseList, SigTraitInstance, SigTraitSpec, SigTy, SigTyKind, SigTyList,
            SigTyOrRe, SigTyOrReList, TraitClause, TraitClauseList, TraitInstance, TraitSpec, Ty,
            TyCtxt, TyKind, TyList, TyOrRe, TyOrReList, TypeAliasItem, TypeGeneric, UniversalTyVar,
        },
    },
    utils::hash::FxHashMap,
};
use hashbrown::hash_map;
use smallvec::SmallVec;
use std::mem;

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

// === Driver === //

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
            opts: SigImporterOpts {
                cause: match wf_mode {
                    SigImporterWfMode::Skip | SigImporterWfMode::ReportHere => cause,
                    SigImporterWfMode::DelayBug => cause.into_delay_bug(),
                },
                universe,
                env,
                create_wf_obligations: match wf_mode {
                    SigImporterWfMode::Skip => false,
                    SigImporterWfMode::DelayBug | SigImporterWfMode::ReportHere => true,
                },
            },
            reentrant_aliases: FxHashMap::default(),
        }
    }

    pub fn instantiate_hrtb_universal(
        &mut self,
        cause: ObligeCause,
        universe: HrtbUniverse,
        value: HrtbBinder,
    ) -> TraitSpec {
        todo!()
    }

    pub fn instantiate_hrtb_infer(
        &mut self,
        cause: ObligeCause,
        universe: HrtbUniverse,
        value: HrtbBinder,
    ) -> TraitSpec {
        todo!()
    }
}

// === SigImporter === //

pub struct SigImporter<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    opts: SigImporterOpts,
    reentrant_aliases: FxHashMap<Obj<TypeAliasItem>, ReentrantAliasState>,
}

struct SigImporterOpts {
    cause: ObligeCause,
    universe: HrtbUniverse,
    env: ClauseImportEnv,
    create_wf_obligations: bool,
}

#[derive(Debug, Copy, Clone)]
enum ReentrantAliasState {
    WaitingForViolation,
    Violated(Span),
}

/// Types
impl<'a, 'tcx> SigImporter<'a, 'tcx> {
    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn session(&self) -> &'tcx Session {
        self.ccx.session()
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
                let args = self.import_ty_or_re_list(args);

                if self.opts.create_wf_obligations {
                    todo!()
                }

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

                let parent_cause = self.opts.cause.clone();
                let parent_universe = self.opts.universe.clone();
                let old_opts = mem::replace(
                    &mut self.opts,
                    SigImporterOpts {
                        cause: parent_cause,
                        universe: parent_universe,
                        env,
                        // Parameters already constrained by parent WF checks.
                        create_wf_obligations: false,
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
                let re = self.import_re(re);
                let pointee = self.import_ty(pointee);

                if self.opts.create_wf_obligations {
                    todo!()
                }

                tcx.intern(TyKind::Reference(re, muta, pointee))
            }
            SigTyKind::Adt(SigAdtInstance { def, params }) => {
                let params = self.import_ty_or_re_list(params);

                if self.opts.create_wf_obligations {
                    todo!();
                }

                tcx.intern(TyKind::Adt(AdtInstance { def, params }))
            }
            SigTyKind::Trait(re, muta, clauses) => {
                let re = self.import_re(re);
                let clauses = self.import_clause_list(clauses);
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
                InferTyVarSourceInfo::Imported { span: ty.r(s).span },
            ),

            SigTyKind::Simple(kind) => tcx.intern(TyKind::Simple(kind)),

            SigTyKind::HrtbVar(idx) => tcx.intern(TyKind::HrtbVar(idx)),

            SigTyKind::Project(SigProjectType {
                target,
                spec,
                assoc_span: _,
                assoc_idx,
            }) => {
                let target = self.import_ty(target);

                let spec_imported = self.import_trait_spec(spec);

                let instance = self.ccx.instantiate_infer().instantiate_trait_spec(
                    &self.opts.cause,
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
            SigReKind::HrtbVar(idx) => Re::HrtbVar(idx),
            SigReKind::Infer => self.ccx.fresh_re_infer(),
            SigReKind::Generic(generic) => self.opts.env.lookup_re(s, generic),
            SigReKind::Error(err) => Re::Error(err),
        }
    }
}

/// Traits
impl<'a, 'tcx> SigImporter<'a, 'tcx> {
    pub fn import_clause_list(&mut self, clauses: SigTraitClauseList) -> TraitClauseList {
        todo!()
    }

    pub fn import_trait_clause(&mut self, clause: SigTraitClause) -> TraitClause {
        todo!()
    }

    pub fn import_trait_spec(&mut self, clause: SigTraitSpec) -> TraitSpec {
        todo!()
    }

    pub fn import_trait_instance(&mut self, instance: SigTraitInstance) -> TraitInstance {
        todo!()
    }

    fn import_trait_clause_inner(
        &mut self,
        wf_self_ty: Option<UniversalTyVar>,
        clause: SigTraitClause,
    ) -> TraitClause {
        todo!()
    }

    fn import_trait_spec_inner(
        &mut self,
        wf_self_ty: Option<UniversalTyVar>,
        clause: SigTraitSpec,
    ) -> TraitSpec {
        todo!()
    }

    fn import_trait_instance_inner(
        &mut self,
        wf_self_ty: Option<UniversalTyVar>,
        instance: SigTraitInstance,
    ) -> TraitInstance {
        todo!()
    }
}

// === HrtbInstantiator === //

// TODO
