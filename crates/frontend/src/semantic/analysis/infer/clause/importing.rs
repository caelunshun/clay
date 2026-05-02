//! Logic to import a user-written type in a signature or function body into a form the inference
//! context can understand.
//!
//! There are four visitors used in this process:
//!
//! 1. **Environment substitution:** Before doing anything with a signature type, we substitute in a
//!    given `ClauseImportEnv` to a signature type. This creates a type which is no longer sensitive
//!    to its environment. This means that we get rid of `SigThis`, `SigInfer`, and `SigGeneric`. We
//!    maintain `SigProject` and `SigAlias` for WF checking but perform environment substitution on
//!    their arguments.
//!
//!    This folder does not call into other folders—it simply performs a substitution.
//!
//! 2. **HRTB instantiation:** We also provide a collection of visitors to instantiate the
//!    top-most layer of a given HRTB binder body as either existential or universal. This
//!    maintains `SigProject` and `SigAlias` types to allow WF-checking of binders to check the
//!    pre-normalized types. Most users, however, will also perform normalizing instantiations of
//!    the binder contents after performing HRTB instantiation.
//!
//!    This folder does not call into other folders—it simply performs a substitution.
//!
//! 3. **Normalize instantiation:** This visitor instantiates `SigProject` and `SigAlias` types at
//!    the top unbound level of that type. We do not instantiate `SigProject` and `SigAlias` types
//!    within binders because `HrtbVar` is not allowed to be mentioned within a projection.
//!
//!    Obligations are only capable of working with normalized types.
//!
//!    Normalizing type aliases requires us to substitute in the type aliases' environment and
//!    then transitively normalize the contents of that alias.
//!
//!    In order to instantiate projection types, we spawn nested obligation queries which resolve
//!    the requested associated type as an inference type. These queries operate on a fully
//!    normalized body.
//!
//! 4. **WF-Checking:** WF-checking folds over HRTB-instantiated types and folds them to their
//!    normalized form. Then, in post-order, it takes the HRTB-instantiated type and its normalized
//!    form and performs WF-checking on that pair. Knowing the normalized form is necessary because
//!    WF-checking requires spawning obligations to e.g. ensure that generic parameters meet the
//!    correct traits and obligations must always run on normalized types.
//!
//!    If there are binders in the type, we instantiate the binder as universal using the
//!    HRTB instantiation folder and WF check that produced type alongside its normalized
//!    counterpart.
//!
//! None of these visitors should be used by the outside world. Instead, they should use drivers
//! which either...
//!
//! 1. Convert the top level of a signature type into a normalized type with WF-checking.
//! 2. Instantiate HRTBs as either existential or universal and normalize that top level.
//!

use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag, Session,
        analysis::{DebruijnAbsoluteRange, DebruijnTop, Spanned},
        arena::{HasInterner, HasListInterner, LateInit, Obj},
        syntax::Span,
    },
    semantic::{
        analysis::{
            ClauseCx, HrtbUniverse, HrtbUniverseInfo, ObligeCause, ObligeCauseBehavior,
            ObligeCauseFrame, UnifyCxMode,
        },
        syntax::{
            AdtInstance, AnyGeneric, FnInstance, FnInstanceInner, FnOwner, GenericBinder,
            GenericSubst, HrtbBinder, HrtbBinderKind, HrtbDebruijn, HrtbDebruijnDef,
            HrtbDebruijnDefList, InferTyVarSourceInfo, Re, RelationDirection, SpannedAdtInstance,
            SpannedFnInstance, SpannedFnOwner, SpannedFnOwnerView, SpannedHrtbBinder,
            SpannedHrtbBinderKindView, SpannedHrtbBinderView, SpannedRe, SpannedTraitInstance,
            SpannedTraitSpec, SpannedTy, SpannedTyView, TraitClause, TraitInstance, TraitParam,
            TraitSpec, Ty, TyCtxt, TyFoldable, TyFolder, TyFolderExt, TyFolderInfallibleExt,
            TyFolderPreservesSpans, TyKind, TyOrRe, TyOrReKind, TyOrReList, TyProjection,
            TyVisitable, TypeAliasItem, UniversalReVarSourceInfo, UniversalTyVarSourceInfo,
        },
    },
    utils::hash::FxHashMap,
};
use hashbrown::hash_map;
use std::{convert::Infallible, rc::Rc};

// === Driver === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn importer(&mut self) -> ClauseImporter<'_, 'tcx> {
        ClauseImporter {
            ccx: self,
            clause_applies_to: None,
        }
    }

    pub fn import_report_here<T>(
        &mut self,
        universe: &HrtbUniverse,
        env: ClauseImportEnvRef<'_>,
        value: Spanned<T>,
    ) -> T
    where
        T: TyFoldable + TyVisitable,
    {
        self.importer().import_report_here(universe, env, value)
    }

    pub fn import_report_elsewhere<T>(
        &mut self,
        universe: &HrtbUniverse,
        env: ClauseImportEnvRef<'_>,
        value: T,
    ) -> T
    where
        T: TyFoldable + TyVisitable,
    {
        self.importer()
            .import_report_elsewhere(universe, env, value)
    }

    pub fn instantiate_hrtb_universal(
        &mut self,
        universe: &HrtbUniverse,
        value: HrtbBinder,
    ) -> TraitSpec {
        let HrtbBinder {
            kind: HrtbBinderKind::Imported(defs),
            inner: value,
        } = value
        else {
            unreachable!()
        };

        let value = self
            .instantiate_hrtb_universal_without_normalization(universe, defs)
            .fold(value);

        self.normalizer(universe.clone()).fold(value)
    }

    pub fn instantiate_hrtb_infer(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        value: HrtbBinder,
    ) -> TraitSpec {
        let HrtbBinder {
            kind: HrtbBinderKind::Imported(defs),
            inner: value,
        } = value
        else {
            unreachable!()
        };

        let value = self
            .instantiate_hrtb_infer_without_normalization(cause, universe, defs)
            .fold(value);

        self.normalizer(universe.clone()).fold(value)
    }
}

pub struct ClauseImporter<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    clause_applies_to: Option<Ty>,
}

impl ClauseImporter<'_, '_> {
    pub fn with_clause_applies_to_opt(mut self, ty: Option<Ty>) -> Self {
        self.clause_applies_to = ty;
        self
    }

    pub fn with_clause_applies_to(self, ty: Ty) -> Self {
        self.with_clause_applies_to_opt(Some(ty))
    }

    pub fn import_report_here<T>(
        &mut self,
        universe: &HrtbUniverse,
        env: ClauseImportEnvRef<'_>,
        value: Spanned<T>,
    ) -> T
    where
        T: TyFoldable + TyVisitable,
    {
        let value = self
            .ccx
            .env_substitutor(universe.clone(), env)
            .fold_preserved(value);

        self.ccx
            .wf_and_normalize_folder(
                ObligeCause::new(ObligeCauseBehavior::Report),
                universe.clone(),
            )
            .with_clause_applies_to_opt(self.clause_applies_to)
            .fold_spanned(value)
    }

    pub fn import_report_elsewhere<T>(
        &mut self,
        universe: &HrtbUniverse,
        env: ClauseImportEnvRef<'_>,
        value: T,
    ) -> T
    where
        T: TyFoldable + TyVisitable,
    {
        let value = self.ccx.env_substitutor(universe.clone(), env).fold(value);

        self.ccx
            .wf_and_normalize_folder(
                ObligeCause::new(ObligeCauseBehavior::DelayBug),
                universe.clone(),
            )
            .with_clause_applies_to_opt(self.clause_applies_to)
            .fold(value)
    }
}

// === Environment substitution === //

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
    pub fn env_substitutor<'a>(
        &'a mut self,
        universe: HrtbUniverse,
        env: ClauseImportEnvRef<'a>,
    ) -> EnvSubstitutor<'a, 'tcx> {
        EnvSubstitutor {
            ccx: self,
            universe,
            env: env.to_owned(),
            hrtb_top: DebruijnTop::default(),
            hrtb_binder_ranges: FxHashMap::default(),
        }
    }
}

pub struct EnvSubstitutor<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    universe: HrtbUniverse,
    env: ClauseImportEnv,
    hrtb_top: DebruijnTop,
    hrtb_binder_ranges: FxHashMap<Obj<GenericBinder>, DebruijnAbsoluteRange>,
}

#[derive(Debug, Copy, Clone)]
enum ReentrantAliasState {
    WaitingForViolation,
    Violated(Span),
}

impl<'tcx> TyFolderPreservesSpans<'tcx> for EnvSubstitutor<'_, 'tcx> {}

impl<'tcx> EnvSubstitutor<'_, 'tcx> {
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

impl<'tcx> TyFolder<'tcx> for EnvSubstitutor<'_, 'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn fold_hrtb_binder(&mut self, binder: SpannedHrtbBinder) -> Result<HrtbBinder, Self::Error> {
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
                spawned_from: *def,
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
        let tcx = self.tcx();

        Ok(match ty.view(tcx) {
            SpannedTyView::SigThis => self.env.self_ty,
            SpannedTyView::SigInfer => self.ccx.fresh_ty_infer(
                self.universe.clone(),
                InferTyVarSourceInfo::Imported {
                    span: ty.own_span(),
                },
            ),
            SpannedTyView::SigGeneric(generic) => {
                self.lookup_generic(AnyGeneric::Ty(generic)).unwrap_ty()
            }
            SpannedTyView::Simple(_)
            | SpannedTyView::Reference(_, _, _)
            | SpannedTyView::Adt(_)
            | SpannedTyView::Trait(_, _, _)
            | SpannedTyView::Tuple(_)
            | SpannedTyView::FnDef(_)
            | SpannedTyView::SigProject(_)
            | SpannedTyView::SigAlias(_, _)
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

// === HRTB Instantiation === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn instantiate_hrtb_universal_without_normalization<'a>(
        &'a mut self,
        universe: &'a HrtbUniverse,
        defs: HrtbDebruijnDefList,
    ) -> HrtbSubstitutionFolder<'a, 'tcx> {
        let tcx = self.tcx();
        let s = self.session();

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
            match var {
                TyOrRe::Re(var) => {
                    let clauses = HrtbSubstitutionFolder::new(self, vars, s).fold(def.clauses);

                    for clause in clauses.r(s) {
                        let TraitClause::Outlives(permitted_outlive_dir, permitted_outlive) =
                            *clause
                        else {
                            unreachable!();
                        };

                        self.permit_universe_re_outlives_general(
                            var,
                            permitted_outlive,
                            permitted_outlive_dir,
                        );
                    }
                }
                TyOrRe::Ty(var) => {
                    let TyKind::UniversalVar(var) = *var.r(s) else {
                        unreachable!()
                    };

                    let clauses = HrtbSubstitutionFolder::new(self, vars, s).fold(def.clauses);

                    self.init_ty_universal_var_direct_clauses(var, clauses);
                }
            }
        }

        HrtbSubstitutionFolder::new(self, vars, s)
    }

    pub fn instantiate_hrtb_infer_without_normalization<'a>(
        &'a mut self,
        cause: &ObligeCause,
        universe: &'a HrtbUniverse,
        defs: HrtbDebruijnDefList,
    ) -> HrtbSubstitutionFolder<'a, 'tcx> {
        let tcx = self.tcx();
        let s = self.session();

        // Make up new inference variables for our binder.
        let vars = defs
            .r(s)
            .iter()
            .map(|def| match def.kind {
                TyOrReKind::Re => TyOrRe::Re(self.fresh_re_infer()),
                TyOrReKind::Ty => TyOrRe::Ty(self.fresh_ty_infer(
                    universe.clone(),
                    InferTyVarSourceInfo::HrtbLhsInstantiation {
                        span: def.spawned_from.span(s),
                        clauses: Rc::new(LateInit::uninit()),
                    },
                )),
            })
            .collect::<Vec<_>>();

        let vars = tcx.intern_list(&vars);

        // Constrain the new inference variables with their obligations.
        for (&def, &var) in defs.r(s).iter().zip(vars.r(s)) {
            match var {
                TyOrRe::Re(var) => {
                    let clauses = HrtbSubstitutionFolder::new(self, vars, s).fold(def.clauses);

                    self.oblige_re_meets_clauses(cause, var, clauses);
                }
                TyOrRe::Ty(var) => {
                    let clauses = HrtbSubstitutionFolder::new(self, vars, s).fold(def.clauses);

                    self.oblige_ty_meets_clauses(cause, universe, var, clauses);

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
        HrtbSubstitutionFolder::new(self, vars, s)
    }
}

pub struct HrtbSubstitutionFolder<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    replace_with: TyOrReList,
    top: DebruijnTop,
}

impl<'a, 'tcx> HrtbSubstitutionFolder<'a, 'tcx> {
    pub fn new(ccx: &'a mut ClauseCx<'tcx>, replace_with: TyOrReList, s: &Session) -> Self {
        Self {
            ccx,
            replace_with,
            top: DebruijnTop::new(replace_with.r(s).len()),
        }
    }

    pub fn replace_with(&self) -> TyOrReList {
        self.replace_with
    }
}

impl<'tcx> TyFolderPreservesSpans<'tcx> for HrtbSubstitutionFolder<'_, 'tcx> {}

impl<'tcx> TyFolder<'tcx> for HrtbSubstitutionFolder<'_, 'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn fold_hrtb_binder(&mut self, binder: SpannedHrtbBinder) -> Result<HrtbBinder, Self::Error> {
        let s = self.session();
        let binder = binder.value;

        let HrtbBinderKind::Imported(defs) = binder.kind else {
            unreachable!();
        };

        let bind_count = defs.r(s).len();

        self.top.move_inwards_by(bind_count);
        let inner = self.super_(binder.inner);
        self.top.move_outwards_by(bind_count);

        Ok(HrtbBinder {
            kind: binder.kind,
            inner,
        })
    }

    fn fold_ty(&mut self, ty: SpannedTy) -> Result<Ty, Self::Error> {
        let s = self.session();
        let ty = ty.value;

        if let TyKind::HrtbVar(var) = *ty.r(s) {
            let abs = self.top.lookup_relative(var.0).index();

            if abs < self.replace_with.r(s).len() {
                return Ok(self.replace_with.r(s)[abs].unwrap_ty());
            }
        }

        Ok(self.super_(ty))
    }

    fn fold_re(&mut self, re: SpannedRe) -> Result<Re, Self::Error> {
        let s = self.session();
        let re = re.value;

        if let Re::HrtbVar(var) = re {
            let abs = self.top.lookup_relative(var.0).index();

            if abs < self.replace_with.r(s).len() {
                return Ok(self.replace_with.r(s)[abs].unwrap_re());
            }
        }

        Ok(self.super_(re))
    }
}

// === Normalization === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn normalizer<'a>(&'a mut self, universe: HrtbUniverse) -> ClauseNormalizer<'a, 'tcx> {
        ClauseNormalizer {
            ccx: self,
            universe,
            reentrant_aliases: FxHashMap::default(),
        }
    }
}

pub struct ClauseNormalizer<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    universe: HrtbUniverse,
    reentrant_aliases: FxHashMap<Obj<TypeAliasItem>, ReentrantAliasState>,
}

impl<'tcx> TyFolder<'tcx> for ClauseNormalizer<'_, 'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn fold_hrtb_binder(&mut self, binder: SpannedHrtbBinder) -> Result<HrtbBinder, Self::Error> {
        let HrtbBinder { kind, inner } = binder.value;

        // We intentionally do not `fold` over the contents of binders.
        return Ok(HrtbBinder {
            kind: self.fold(kind),
            inner,
        });
    }

    fn fold_ty(&mut self, ty: SpannedTy) -> Result<Ty, Self::Error> {
        let s = self.session();

        let own_span = ty.own_span();
        let ty = self.super_spanned(ty);

        Ok(match *ty.r(s) {
            TyKind::SigProject(projection) => self.normalize_super_normalized_projection(
                ObligeCause::new_delay_bug(),
                own_span,
                projection,
            ),
            TyKind::SigAlias(def, args) => {
                self.normalize_super_normalized_alias(own_span, def, args)
            }

            TyKind::Simple(_)
            | TyKind::Reference(_, _, _)
            | TyKind::Adt(_)
            | TyKind::Trait(_, _, _)
            | TyKind::Tuple(_)
            | TyKind::FnDef(_)
            | TyKind::InferVar(_)
            | TyKind::UniversalVar(_)
            | TyKind::Error(_) => ty,

            TyKind::SigThis | TyKind::SigInfer | TyKind::SigGeneric(_) | TyKind::HrtbVar(_) => {
                unreachable!()
            }
        })
    }
}

impl ClauseNormalizer<'_, '_> {
    fn normalize_super_normalized_projection(
        &mut self,
        cause: ObligeCause,
        own_span: Span,
        projection: TyProjection,
    ) -> Ty {
        let s = self.session();
        let tcx = self.tcx();

        let TyProjection {
            target,
            spec,
            assoc,
        } = projection;

        let assoc_infer_ty = self.ccx.fresh_ty_infer(
            self.universe.clone(),
            InferTyVarSourceInfo::ProjectionResult { span: own_span },
        );
        let spec = {
            let mut args = spec.params.r(s).to_vec();
            args[assoc as usize] = TraitParam::Equals(TyOrRe::Ty(assoc_infer_ty));

            TraitSpec {
                def: spec.def,
                params: tcx.intern_list(&args),
            }
        };

        self.ccx
            .oblige_ty_meets_trait_instantiated(cause, self.universe.clone(), target, spec);

        assoc_infer_ty
    }

    fn normalize_super_normalized_alias(
        &mut self,
        own_span: Span,
        def: Obj<TypeAliasItem>,
        args: TyOrReList,
    ) -> Ty {
        let s = self.session();
        let tcx = self.tcx();

        // Substitute in the alias's environment.
        let env = ClauseImportEnv::new(
            tcx.intern(TyKind::SigThis),
            vec![GenericSubst {
                binder: def.r(s).generics,
                substs: args,
            }],
        );

        let body = self
            .ccx
            .env_substitutor(self.universe.clone(), env.as_ref())
            .fold_preserved(*def.r(s).body);

        // Normalize the target, reporting errors on guaranteed reentrancy (that is,
        // reentrancy for a given alias not involving projections).
        match self.reentrant_aliases.entry(def) {
            hash_map::Entry::Occupied(entry) => {
                let entry = entry.into_mut();

                if matches!(entry, ReentrantAliasState::WaitingForViolation) {
                    *entry = ReentrantAliasState::Violated(own_span);
                }

                return tcx.intern(TyKind::Error(ErrorGuaranteed::new_unchecked()));
            }
            hash_map::Entry::Vacant(entry) => {
                entry.insert(ReentrantAliasState::WaitingForViolation);
            }
        }

        let body = self.fold_spanned(body);

        match self.reentrant_aliases.remove(&def).unwrap() {
            ReentrantAliasState::WaitingForViolation => {
                // (no violation occurred)
            }
            ReentrantAliasState::Violated(span) => {
                let mut diag = Diag::span_err(own_span, "attempted to expand recursive type alias");

                if own_span != span {
                    diag.push_child(LeafDiag::span_note(span, "reentered here"));
                }

                diag.emit();
            }
        }

        body
    }
}

// === WF-Checking === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn wf_and_normalize_folder(
        &mut self,
        cause: ObligeCause,
        universe: HrtbUniverse,
    ) -> ClauseTyWfFolder<'_, 'tcx> {
        ClauseTyWfFolder {
            ccx: self,
            cause,
            universe,
            clause_applies_to: None,
        }
    }
}

pub struct ClauseTyWfFolder<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    cause: ObligeCause,
    universe: HrtbUniverse,
    clause_applies_to: Option<Ty>,
}

impl ClauseTyWfFolder<'_, '_> {
    pub fn with_clause_applies_to_opt(mut self, ty: Option<Ty>) -> Self {
        self.clause_applies_to = ty;
        self
    }
}

impl<'tcx> TyFolder<'tcx> for ClauseTyWfFolder<'_, 'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn fold_hrtb_binder(&mut self, binder: SpannedHrtbBinder) -> Result<HrtbBinder, Self::Error> {
        let tcx = self.tcx();
        let s = self.session();

        let SpannedHrtbBinderView {
            kind,
            inner:
                Spanned {
                    value: bound,
                    span_info: inner_span_info,
                },
        } = binder.view(tcx);

        let SpannedHrtbBinderKindView::Imported(defs) = kind.view(tcx) else {
            unreachable!()
        };

        // Check definitions and normalize them.
        let defs = self.fold_spanned(defs);

        // Universally instantiate the body and WF check it.
        let old_universe = self.universe.clone();
        let wf_cause = self.cause.clone().child(ObligeCauseFrame::WfHrtb {
            binder_span: kind.own_span(),
        });
        let new_universe = self.universe.clone().nest(HrtbUniverseInfo {
            cause: wf_cause.clone(),
        });

        self.universe = new_universe;
        {
            let mut hrtb_instantiation_visitor = self
                .ccx
                .instantiate_hrtb_universal_without_normalization(&self.universe, defs);

            let hrtb_universals = hrtb_instantiation_visitor.replace_with();
            let bound = hrtb_instantiation_visitor.fold(bound);
            let bound = Spanned::new_raw(bound, inner_span_info);

            let bound = self.fold_spanned(bound);

            self.ccx.oblige_covered(
                wf_cause,
                hrtb_universals
                    .r(s)
                    .iter()
                    .filter_map(|ty_or_re| ty_or_re.as_ty())
                    .map(|ty| {
                        let TyKind::UniversalVar(var) = *ty.r(s) else {
                            unreachable!()
                        };

                        var
                    }),
                None,
                Some(bound),
            );
        }
        self.universe = old_universe;

        Ok(HrtbBinder {
            kind: HrtbBinderKind::Imported(defs),
            // We don't normalize this inner type because normalization doesn't follow HRTB binders.
            inner: bound,
        })
    }

    fn fold_ty(&mut self, ty: SpannedTy) -> Result<Ty, Self::Error> {
        let s = self.session();
        let tcx = self.tcx();

        match ty.view(tcx) {
            SpannedTyView::Trait(_, _, _) => {
                let old_clause_applies_to = self.clause_applies_to.replace(ty.value);
                let normalized = self.super_spanned(ty);
                self.clause_applies_to = old_clause_applies_to;

                Ok(normalized)
            }
            SpannedTyView::Reference(re, muta, pointee) => {
                let pointee_span = pointee.own_span();
                let re = self.fold_spanned(re);
                let pointee = self.fold_spanned(pointee);

                self.ccx.oblige_ty_outlives_re(
                    self.cause.clone().child(ObligeCauseFrame::WfForReference {
                        pointee: pointee_span,
                    }),
                    pointee,
                    re,
                    RelationDirection::LhsOntoRhs,
                );

                Ok(tcx.intern(TyKind::Reference(re, muta, pointee)))
            }

            SpannedTyView::SigProject(TyProjection {
                target,
                spec,
                assoc,
            }) => {
                // TODO: Spans

                // WF-check and normalize target type.
                let target = self.fold(target);

                // WF-check and normalize spec. This has the effect of checking arguments.
                let old_clause_applies_to = self.clause_applies_to.replace(target);
                let spec = self.fold(spec);
                self.clause_applies_to = old_clause_applies_to;

                // Normalize projection type.
                let resolved = self
                    .ccx
                    .normalizer(self.universe.clone())
                    .normalize_super_normalized_projection(
                        self.cause.clone().child(ObligeCauseFrame::WfTyProjection {
                            span: ty.own_span(),
                        }),
                        ty.own_span(),
                        TyProjection {
                            target,
                            spec,
                            assoc,
                        },
                    );

                Ok(resolved)
            }
            SpannedTyView::SigAlias(def, args) => {
                // TODO: Spans

                // WF-check arguments
                let args = self.fold(args);

                // TODO: Move to env utilities
                self.check_generic_values(
                    // Cannot use `Self` in type alias.
                    tcx.intern(TyKind::SigThis),
                    def.r(s).generics,
                    [],
                    args,
                    &args.r(s).iter().map(|_| ty.own_span()).collect::<Vec<_>>(),
                    None,
                );

                // Normalize alias type.
                let resolved = self
                    .ccx
                    .normalizer(self.universe.clone())
                    .normalize_super_normalized_alias(ty.own_span(), def, args);

                Ok(resolved)
            }

            SpannedTyView::Simple(_)
            | SpannedTyView::Adt(_)
            | SpannedTyView::FnDef(_)
            | SpannedTyView::Tuple(_)
            | SpannedTyView::UniversalVar(_)
            | SpannedTyView::InferVar(_)
            | SpannedTyView::Error(_) => Ok(self.super_spanned(ty)),

            SpannedTyView::SigThis
            | SpannedTyView::SigInfer
            | SpannedTyView::SigGeneric(_)
            | SpannedTyView::HrtbVar(_) => {
                unreachable!()
            }
        }
    }

    fn fold_trait_spec(&mut self, spec: SpannedTraitSpec) -> Result<TraitSpec, Self::Error> {
        let s = self.session();
        let tcx = self.tcx();

        let param_spans = spec
            .view(tcx)
            .params
            .iter(tcx)
            .map(|v| v.own_span())
            .collect::<Vec<_>>();

        let spec = self.super_spanned(spec);

        let params = spec
            .params
            .r(s)
            .iter()
            .map(|&param| match param {
                TraitParam::Equals(v) => v,
                TraitParam::Unspecified(_) => TyOrRe::Ty(self.ccx.fresh_ty_infer(
                    self.universe.clone(),
                    InferTyVarSourceInfo::TraitAssocPlaceholderHelper,
                )),
            })
            .collect::<Vec<_>>();

        let params = tcx.intern_list(&params);

        // Just like in `rustc`, we never produce obligations on the associated types since, if an
        // `impl` is found, we just rely on the fact that `impl` WF checks already validated the
        // type for its clauses and ensure that our `impl` matches what the trait spec said it would
        // contain.
        self.check_generic_values(
            self.clause_applies_to.unwrap(),
            *spec.def.r(s).generics,
            [],
            params,
            &param_spans,
            Some(*spec.def.r(s).regular_generic_count),
        );

        Ok(spec)
    }

    fn fold_trait_instance(
        &mut self,
        instance: SpannedTraitInstance,
    ) -> Result<TraitInstance, Self::Error> {
        let s = self.session();
        let tcx = self.tcx();

        let param_spans = instance
            .view(tcx)
            .params
            .iter(tcx)
            .map(|v| v.own_span())
            .collect::<Vec<_>>();

        let instance = self.super_spanned(instance);

        self.check_generic_values(
            self.clause_applies_to.unwrap(),
            *instance.def.r(s).generics,
            [],
            instance.params,
            &param_spans,
            None,
        );

        Ok(instance)
    }

    fn fold_adt_instance(
        &mut self,
        instance: SpannedAdtInstance,
    ) -> Result<AdtInstance, Self::Error> {
        let s = self.session();
        let tcx = self.tcx();

        let param_spans = instance
            .view(tcx)
            .params
            .iter(tcx)
            .map(|v| v.own_span())
            .collect::<Vec<_>>();

        let instance = self.super_spanned(instance);

        // Check generics
        self.check_generic_values(
            tcx.intern(TyKind::Adt(instance)),
            instance.def.r(s).generics,
            [],
            instance.params,
            &param_spans,
            None,
        );

        Ok(instance)
    }

    fn fold_fn_instance(&mut self, instance: SpannedFnInstance) -> Result<FnInstance, Self::Error> {
        let s = self.session();
        let tcx = self.tcx();

        let own_span = instance.own_span();
        let early_arg_spans = instance
            .view(tcx)
            .early_args
            .map(|v| v.iter(tcx).map(|v| v.own_span()).collect::<Vec<_>>())
            .unwrap_or_default();

        // WF-check and normalize the interior types.
        let instance = self.super_(instance.value);
        let FnInstanceInner { owner, early_args } = *instance.r(s);

        // Construct an environment, validating the `owner` in the process.
        let env = self.ccx.create_infer_env_for_fn_owner(
            &self
                .cause
                .clone()
                .child(ObligeCauseFrame::WfFnDef { fn_ty: own_span }),
            &self.universe,
            owner,
        );

        // Validate the `early_args`.
        if let Some(early_args) = early_args {
            self.check_generic_values(
                env.self_ty,
                owner.def(s).r(s).generics,
                env.sig_generic_substs.iter().copied(),
                early_args,
                &early_arg_spans,
                None,
            );
        }

        Ok(instance)
    }

    fn fold_fn_owner(&mut self, owner: SpannedFnOwner) -> Result<FnOwner, Self::Error> {
        let tcx = self.tcx();

        match owner.view(tcx) {
            SpannedFnOwnerView::Item(def) => Ok(FnOwner::Item(def)),
            SpannedFnOwnerView::Trait {
                instance,
                self_ty,
                method_idx,
            } => {
                let self_ty = self.fold_spanned(self_ty);

                let old_clause_applies_to = self.clause_applies_to.replace(self_ty);
                let instance = self.fold_spanned(instance);
                self.clause_applies_to = old_clause_applies_to;

                Ok(FnOwner::Trait {
                    instance,
                    self_ty,
                    method_idx,
                })
            }
            SpannedFnOwnerView::Inherent {
                self_ty,
                block,
                method_idx,
            } => Ok(FnOwner::Inherent {
                self_ty: self.fold_spanned(self_ty),
                block,
                method_idx,
            }),
        }
    }
}

impl ClauseTyWfFolder<'_, '_> {
    fn check_generic_values(
        &mut self,
        clause_applies_to: Ty,
        binder: Obj<GenericBinder>,
        extra_def_substs: impl IntoIterator<Item = GenericSubst>,
        all_params: TyOrReList,
        param_spans: &[Span],
        validate_count: Option<u32>,
    ) {
        let s = self.session();

        let defs = &binder.r(s).defs[..];
        let defs = match validate_count {
            Some(limit) => &defs[..limit as usize],
            None => defs,
        };

        let validated_params = all_params.r(s);
        let validated_params = match validate_count {
            Some(limit) => &validated_params[..limit as usize],
            None => validated_params,
        };

        self.ccx.oblige_args_meet_binder_clauses(
            &self.universe,
            ClauseImportEnvRef::new(
                clause_applies_to,
                &[GenericSubst {
                    binder,
                    substs: all_params,
                }]
                .into_iter()
                .chain(extra_def_substs)
                .collect::<Vec<_>>(),
            ),
            defs,
            validated_params,
            |_, param_idx, clause_span| {
                self.cause
                    .clone()
                    .child(ObligeCauseFrame::WfForGenericParam {
                        use_span: param_spans[param_idx],
                        clause_span,
                    })
            },
        );
    }
}
