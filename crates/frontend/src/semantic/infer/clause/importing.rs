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
            RegionGeneric, SigAdtInstance, SigHrtbBinder, SigProjectType, SigRe, SigReKind,
            SigTraitClause, SigTraitClauseKind, SigTraitClauseList, SigTraitInstance, SigTraitSpec,
            SigTy, SigTyKind, SigTyList, SigTyOrRe, SigTyOrReList, TraitClause, TraitClauseList,
            TraitInstance, TraitSpec, Ty, TyCtxt, TyKind, TyList, TyOrRe, TyOrReList,
            TypeAliasItem, TypeGeneric,
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
            cause,
            opts: SigImporterOpts {
                universe,
                env,
                wf_mode,
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
    cause: ObligeCause,
    opts: SigImporterOpts,
    reentrant_aliases: FxHashMap<Obj<TypeAliasItem>, ReentrantAliasState>,
}

struct SigImporterOpts {
    universe: HrtbUniverse,
    env: ClauseImportEnv,
    wf_mode: SigImporterWfMode,
}

#[derive(Debug, Copy, Clone)]
enum ReentrantAliasState {
    WaitingForViolation,
    Violated(Span),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum SigImporterWfMode {
    Skip,
    DelayBug,
    ReportHere,
}

impl SigImporterWfMode {
    pub fn should_perform(self) -> bool {
        matches!(self, Self::DelayBug | Self::ReportHere)
    }
}

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

                if self.opts.wf_mode.should_perform() {
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

                let old_universe = self.opts.universe.clone();
                let old_opts = mem::replace(
                    &mut self.opts,
                    SigImporterOpts {
                        universe: old_universe,
                        env,
                        // Parameters already constrained by parent WF checks.
                        wf_mode: SigImporterWfMode::Skip,
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

                if self.opts.wf_mode.should_perform() {
                    todo!()
                }

                tcx.intern(TyKind::Reference(re, muta, pointee))
            }
            SigTyKind::Adt(SigAdtInstance { def, params }) => {
                let params = self.import_ty_or_re_list(params);

                if self.opts.wf_mode.should_perform() {
                    todo!();
                }

                tcx.intern(TyKind::Adt(AdtInstance { def, params }))
            }
            SigTyKind::Trait(re, muta, clauses) => {
                let re = self.import_re(re);
                let clauses = self.import_clause_list_no_spec_wf(clauses);

                if self.opts.wf_mode.should_perform() {
                    todo!()
                }

                tcx.intern(TyKind::Trait(re, muta, clauses))
            }
            SigTyKind::Tuple(tys) => {
                let tys = self.import_ty_list(tys);

                if self.opts.wf_mode.should_perform() {
                    todo!()
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
                assoc_span,
                assoc_idx,
            }) => todo!(),

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

    pub fn import_clause_list(
        &mut self,
        clause_applies_to_for_wf: Ty,
        clauses: SigTraitClauseList,
    ) -> TraitClauseList {
        todo!()
    }

    pub fn import_clause_list_no_spec_wf(
        &mut self,
        clauses: SigTraitClauseList,
    ) -> TraitClauseList {
        todo!()
    }

    pub fn import_clause(
        &mut self,
        clause_applies_to_for_wf: Ty,
        clause: SigTraitClause,
    ) -> TraitClause {
        todo!()
    }

    pub fn import_clause_no_spec_wf(&mut self, clause: SigTraitClause) -> TraitClause {
        match clause.kind {
            SigTraitClauseKind::Outlives(dir, ty_or_re) => {
                todo!()
            }
            SigTraitClauseKind::Trait(binder) => {
                todo!()
            }
        }
    }

    pub fn import_binder(
        &mut self,
        clause_applies_to_for_wf: Ty,
        binder: SigHrtbBinder,
    ) -> HrtbBinder {
        todo!()
    }

    pub fn import_binder_no_spec_wf(&mut self, binder: SigHrtbBinder) -> HrtbBinder {
        todo!()
    }

    pub fn import_trait_spec(
        &mut self,
        clause_applies_to_for_wf: Ty,
        spec: SigTraitSpec,
    ) -> TraitSpec {
        todo!()
    }

    pub fn import_trait_spec_no_spec_wf(&mut self, spec: SigTraitSpec) -> TraitSpec {
        todo!()
    }

    pub fn import_trait_instance(
        &mut self,
        clause_self_ty_for_wf: Ty,
        spec: SigTraitInstance,
    ) -> TraitInstance {
        todo!()
    }

    pub fn import_trait_instance_no_spec_wf(&mut self, spec: SigTraitInstance) -> TraitInstance {
        todo!()
    }
}

// === HrtbInstantiator === //

// TODO
