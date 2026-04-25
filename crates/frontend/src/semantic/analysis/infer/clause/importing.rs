//! Logic to import a user-written type in a signature or function body into a form the inference
//! context can understand.
//!
//! There are four visitors used in this process:
//!
//! 1. **Environment substitution:** Before doing anything with a signature type, we substitute in a
//!    given `ClauseImportEnv` to a signature type. This creates a type which is no longer sensitive
//!    to its environment. This means that we get rid of `SigThis`, `SigInfer`, and `SigGeneric`. We
//!    maintain `SigProject` and `SigAlias` for WF checking but include their arguments in this
//!    import process.
//!
//!    This folder does not call into other folders—it simply performs a substitution.
//!
//! 2. **HRTB instantiation:** We also provide a collection of visitors to instantiate the
//!    top-most layer of a given HRTB binder body as either existential or universal variables. This
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
//! 4. **WF-Checking:** WF-checking traverses both the HRTB-instantiated version of a type and its
//!    normalized form in parallel. This is necessary because, e.g., generic parameter verification
//!    requires us to create obligations on those parameters and obligations must operate on
//!    normalized types.
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
        arena::{HasInterner, HasListInterner, Obj},
        syntax::Span,
    },
    semantic::{
        analysis::{
            ClauseCx, ClauseOrigin, ClauseOriginKind, HrtbUniverse, HrtbUniverseInfo, UnifyCxMode,
        },
        syntax::{
            AnyGeneric, GenericBinder, GenericSubst, HrtbBinder, HrtbBinderKind, HrtbDebruijn,
            HrtbDebruijnDef, InferTyVarSourceInfo, Re, RelationDirection, SpannedAdtInstance,
            SpannedFnInstance, SpannedFnInstanceView, SpannedHrtbBinder, SpannedHrtbBinderKindView,
            SpannedHrtbBinderView, SpannedHrtbDebruijnDefView, SpannedRe, SpannedTraitInstance,
            SpannedTraitParamView, SpannedTraitSpec, SpannedTy, SpannedTyOrRe, SpannedTyOrReList,
            SpannedTyView, TraitClause, TraitParam, TraitSpec, Ty, TyCtxt, TyFoldable, TyFolder,
            TyFolderExt, TyFolderInfallibleExt, TyFolderPreservesSpans, TyKind, TyOrRe, TyOrReKind,
            TyOrReList, TyProjection, TyVisitable, TyVisitor, TyVisitorInfallibleExt,
            TypeAliasItem, UniversalReVarSourceInfo, UniversalTyVarSourceInfo,
        },
    },
    utils::hash::FxHashMap,
};
use hashbrown::hash_map;
use std::{convert::Infallible, mem, ops::ControlFlow};

// === Driver === //

// TODO

// === Environment Substitution === //

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
        origin: &'a ClauseOrigin,
        universe: HrtbUniverse,
        env: ClauseImportEnvRef<'a>,
    ) -> ClauseCxImporter<'a, 'tcx> {
        ClauseCxImporter {
            ccx: self,
            origin,
            universe,
            env: env.to_owned(),
            hrtb_top: DebruijnTop::default(),
            hrtb_binder_ranges: FxHashMap::default(),
            reentrant_aliases: FxHashMap::default(),
        }
    }
}

pub struct ClauseCxImporter<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    origin: &'a ClauseOrigin,
    universe: HrtbUniverse,
    env: ClauseImportEnv,
    hrtb_top: DebruijnTop,
    hrtb_binder_ranges: FxHashMap<Obj<GenericBinder>, DebruijnAbsoluteRange>,
    reentrant_aliases: FxHashMap<Obj<TypeAliasItem>, ReentrantAliasState>,
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
        let s = self.session();
        let tcx = self.tcx();

        Ok(match ty.view(tcx) {
            SpannedTyView::SigThis => self.env.self_ty,
            SpannedTyView::SigInfer => self.ccx.fresh_ty_infer(
                self.universe.clone(),
                InferTyVarSourceInfo::Imported {
                    origin: self.origin.clone(),
                    span: ty.own_span(),
                },
            ),
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

                let assoc_infer_ty = self.ccx.fresh_ty_infer(
                    self.universe.clone(),
                    InferTyVarSourceInfo::ProjectionResult {
                        origin: self.origin.clone(),
                        span: ty.own_span(),
                    },
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
                    .wf_visitor(self.universe.clone())
                    .with_clause_applies_to(target)
                    .visit_spanned(Spanned::new_saturated(spec, ty.own_span(), tcx));

                self.ccx.oblige_ty_meets_trait_instantiated(
                    self.origin
                        .clone()
                        .child(ClauseOriginKind::InstantiatedProjection {
                            span: ty.own_span(),
                        }),
                    self.universe.clone(),
                    target,
                    spec,
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
                        let mut diag = Diag::span_err(
                            ty.own_span(),
                            "attempted to expand recursive type alias",
                        );

                        if ty.own_span() != span {
                            diag.push_child(LeafDiag::span_note(span, "reentered here"));
                        }

                        diag.emit();
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

// === WF-Checking === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn wf_visitor(&mut self, universe: HrtbUniverse) -> ClauseTyWfVisitor<'_, 'tcx> {
        ClauseTyWfVisitor {
            ccx: self,
            universe,
            clause_applies_to: None,
        }
    }
}

pub struct ClauseTyWfVisitor<'a, 'tcx> {
    pub ccx: &'a mut ClauseCx<'tcx>,
    pub universe: HrtbUniverse,
    pub clause_applies_to: Option<Ty>,
}

impl ClauseTyWfVisitor<'_, '_> {
    pub fn with_clause_applies_to(mut self, ty: Ty) -> Self {
        self.clause_applies_to = Some(ty);
        self
    }
}

impl<'tcx> TyVisitor<'tcx> for ClauseTyWfVisitor<'_, 'tcx> {
    type Break = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn visit_hrtb_binder<T: Copy + TyVisitable + TyFoldable>(
        &mut self,
        binder: SpannedHrtbBinder<T>,
    ) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        let SpannedHrtbBinderView {
            kind,
            inner:
                Spanned {
                    value: _,
                    span_info: inner_span_info,
                },
        } = binder.view(tcx);

        let SpannedHrtbBinderKindView::Imported(defs) = kind.view(tcx) else {
            unreachable!()
        };

        let old_universe = self.universe.clone();
        let new_universe = if defs.is_empty(s) {
            self.universe.clone()
        } else {
            self.universe.clone().nest(HrtbUniverseInfo {
                origin: ClauseOrigin::root_report(ClauseOriginKind::WfHrtb {
                    binder_span: kind.own_span(),
                }),
            })
        };

        self.universe = new_universe;
        {
            let bound = Spanned::new_raw(
                self.ccx
                    .instantiate_hrtb_universal(&self.universe, binder.value),
                inner_span_info,
            );

            self.visit_spanned(bound);

            for def in defs.iter(tcx) {
                let SpannedHrtbDebruijnDefView {
                    spawned_from: _,
                    kind: _,
                    clauses,
                } = def.view(tcx);

                self.visit_spanned(clauses);
            }
        }
        self.universe = old_universe;

        ControlFlow::Continue(())
    }

    fn visit_ty(&mut self, ty: SpannedTy) -> ControlFlow<Self::Break> {
        match ty.view(self.tcx()) {
            SpannedTyView::Trait(_, _, _) => {
                let old_clause_applies_to = self.clause_applies_to.replace(ty.value);
                self.walk_spanned(ty);
                self.clause_applies_to = old_clause_applies_to;
            }
            SpannedTyView::Reference(re, _muta, pointee) => {
                self.ccx.oblige_ty_outlives_re(
                    ClauseOrigin::root_report(ClauseOriginKind::WfForReference {
                        pointee: pointee.own_span(),
                    }),
                    pointee.value,
                    re.value,
                    RelationDirection::LhsOntoRhs,
                );

                self.walk_spanned(ty);
            }

            SpannedTyView::Simple(_)
            | SpannedTyView::Adt(_)
            | SpannedTyView::FnDef(_)
            | SpannedTyView::Tuple(_)
            | SpannedTyView::UniversalVar(_)
            | SpannedTyView::HrtbVar(_)
            | SpannedTyView::Error(_) => {
                self.walk_spanned(ty);
            }
            SpannedTyView::InferVar(_) => {
                // It is assumed that inference variables are checked for well-formed'ness somewhere
                // else.
            }
            SpannedTyView::SigThis
            | SpannedTyView::SigInfer
            | SpannedTyView::SigGeneric(_)
            | SpannedTyView::SigProject(_)
            | SpannedTyView::SigAlias(_, _) => {
                unreachable!()
            }
        }

        ControlFlow::Continue(())
    }

    fn visit_trait_spec(&mut self, spec: SpannedTraitSpec) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        let params = spec
            .view(tcx)
            .params
            .iter(tcx)
            .map(|param| match param.view(tcx) {
                SpannedTraitParamView::Equals(v) => v,
                SpannedTraitParamView::Unspecified(_) => {
                    SpannedTyOrRe::new_unspanned(TyOrRe::Ty(self.ccx.fresh_ty_infer(
                        self.universe.clone(),
                        InferTyVarSourceInfo::TraitAssocPlaceholderHelper,
                    )))
                }
            })
            .collect::<Vec<_>>();

        let params = SpannedTyOrReList::alloc_list(spec.own_span(), &params, tcx);

        // Just like in `rustc`, we never produce obligations on the associated types since, if an
        // `impl` is found, we just rely on the fact that `impl` WF checks already validated the
        // type for its clauses and ensure that our `impl` matches what the trait spec said it would
        // contain.
        self.check_generic_values(
            self.clause_applies_to.unwrap(),
            *spec.value.def.r(s).generics,
            [],
            params,
            Some(*spec.value.def.r(s).regular_generic_count),
        );

        self.walk_spanned(spec);

        ControlFlow::Continue(())
    }

    fn visit_trait_instance(&mut self, instance: SpannedTraitInstance) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        self.check_generic_values(
            self.clause_applies_to.unwrap(),
            *instance.value.def.r(s).generics,
            [],
            instance.view(tcx).params,
            None,
        );
        self.walk_spanned(instance);

        ControlFlow::Continue(())
    }

    fn visit_adt_instance(&mut self, instance: SpannedAdtInstance) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        // Check generics
        self.check_generic_values(
            tcx.intern(TyKind::Adt(instance.value)),
            instance.value.def.r(s).generics,
            [],
            instance.view(tcx).params,
            None,
        );

        // Ensure parameter types are also well-formed.
        self.walk_spanned(instance);

        ControlFlow::Continue(())
    }

    fn visit_fn_instance(&mut self, instance: SpannedFnInstance) -> ControlFlow<Self::Break> {
        let s = self.session();
        let tcx = self.tcx();

        let SpannedFnInstanceView { owner, early_args } = instance.view(tcx);

        // Construct an environment, validating the `owner` in the process.
        let env = self.ccx.instantiate_fn_owner_env_as_infer(
            &ClauseOrigin::root_report(ClauseOriginKind::WfFnDef {
                fn_ty: instance.own_span(),
            }),
            &self.universe,
            owner.value,
        );

        // Validate the `early_args`.
        if let Some(early_args) = early_args {
            self.check_generic_values(
                env.self_ty,
                owner.value.def(s).r(s).generics,
                env.sig_generic_substs.iter().copied(),
                early_args,
                None,
            );
        }

        // Ensure parameter types are also well-formed.
        self.walk_spanned(instance);

        ControlFlow::Continue(())
    }
}

impl ClauseTyWfVisitor<'_, '_> {
    fn check_generic_values(
        &mut self,
        clause_applies_to: Ty,
        binder: Obj<GenericBinder>,
        extra_def_substs: impl IntoIterator<Item = GenericSubst>,
        all_params: SpannedTyOrReList,
        validate_count: Option<u32>,
    ) {
        let s = self.session();
        let tcx = self.tcx();

        let defs = &binder.r(s).defs[..];
        let defs = match validate_count {
            Some(limit) => &defs[..limit as usize],
            None => defs,
        };

        let validated_params = all_params.value.r(s);
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
                    substs: all_params.value,
                }]
                .into_iter()
                .chain(extra_def_substs)
                .collect::<Vec<_>>(),
            ),
            defs,
            validated_params,
            |_, param_idx, clause_span| {
                ClauseOrigin::root_report(ClauseOriginKind::WfForGenericParam {
                    use_span: all_params.nth(param_idx, tcx).own_span(),
                    clause_span,
                })
            },
        );
    }
}

// === HRTB Instantiation === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn instantiate_hrtb_universal<T: TyFoldable>(
        &mut self,
        universe: &HrtbUniverse,
        binder: HrtbBinder<T>,
    ) -> T {
        let tcx = self.tcx();
        let s = self.session();

        let HrtbBinderKind::Imported(defs) = binder.kind else {
            unreachable!();
        };

        // Fast path :)
        if defs.r(s).is_empty() {
            return binder.inner;
        }

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

        // Fold the inner type
        HrtbSubstitutionFolder::new(self, vars, s).fold(binder.inner)
    }

    pub fn instantiate_hrtb_infer(
        &mut self,
        origin: &ClauseOrigin,
        universe: &HrtbUniverse,
        binder: HrtbBinder<TraitSpec>,
    ) -> TraitSpec {
        let tcx = self.tcx();
        let s = self.session();

        let HrtbBinderKind::Imported(defs) = binder.kind else {
            unreachable!();
        };

        // Fast path :)
        if defs.r(s).is_empty() {
            return binder.inner;
        }

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

                    self.oblige_re_meets_clauses(
                        &origin.clone().child(ClauseOriginKind::HrtbSelection {
                            def: def.spawned_from.span(s),
                        }),
                        var,
                        clauses,
                    );
                }
                TyOrRe::Ty(var) => {
                    let clauses = HrtbSubstitutionFolder::new(self, vars, s).fold(def.clauses);

                    self.oblige_ty_meets_clauses(
                        &origin.clone().child(ClauseOriginKind::HrtbSelection {
                            def: def.spawned_from.span(s),
                        }),
                        universe,
                        var,
                        clauses,
                    );
                }
            }
        }

        // Fold the inner type
        HrtbSubstitutionFolder::new(self, vars, s).fold(binder.inner)
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
}

impl<'tcx> TyFolder<'tcx> for HrtbSubstitutionFolder<'_, 'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn fold_hrtb_binder<T: Copy + TyFoldable>(
        &mut self,
        binder: SpannedHrtbBinder<T>,
    ) -> Result<HrtbBinder<T>, Self::Error> {
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
