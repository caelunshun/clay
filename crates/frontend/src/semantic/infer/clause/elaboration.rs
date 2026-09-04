//! Logic to elaborate a trait clause list.
//!
//! Elaboration transforms a clause like `Inherited<A, B: Additional>` into a clause list which...
//!
//! a) includes all super-traits.
//! b) reifies all `Unspecified` trait parameters like `B: Additional` into fresh universals with
//!    direct clauses encompassing both `B`'s direct clauses (i.e. `Additional`) and all the clauses
//!    on that given associated type's definition.
//!
//! This process is made slightly more involved by the way in which `impl` obligation works. If you
//! have a universal type `T` such that its elaborated trait clause list is `T: Foo<Assoc = U1> +
//! Foo<Assoc = U2>`, only the `T: Foo<Assoc = U1>` clause will be used because that will be the
//! first clause which could be selected. This is sound because, if `U1` and `U2` are properly
//! disjoint, nothing could ever satisfy that constraint.
//!
//! This behavior, however, means that elaboration should make a best-effort to merge similar trait
//! clauses into a single clause before generating reified universal types since, otherwise, implied
//! constraints may be forgotten.
//!
//! To implement this, we spawn an inference variable for every single reified variable and
//! construct an obligation which, after fully resolving all inference variables in the clause
//! list's generic parameter list, unifies the appropriate universals with the inference variables.
//!
//! This is sensible to do because universals can only ever be created from a) importing types from
//! signatures, b) instantiating HRTBs, and c) elaborating existing universals. Besides HRTBs inside
//! function bodies, the universal clause list should not contain inference variables beyond those
//! produced by projection resolution. Projections, even if they depend on the universal being
//! elaborated, should usually end up treating universals and blank inference variables the same
//! except under really contrived and evil scenarios like this...
//!
//! ```ignore
//! pub trait Helper<T> {
//!     type Assoc;
//! }
//!
//! pub trait Foo {}
//!
//! fn mewo<T: Helper<<T as Helper<()>>::Assoc, Assoc: Foo>>() {}
//! ```
//!
//! ...which rustc doesn't even handle correctly.

use crate::{
    base::{
        arena::{HasInterner, HasListInterner},
        syntax::Span,
    },
    semantic::{
        infer::{
            ClauseCx, ClauseFuel, ClauseImportEnv, ClauseObligation, FloatingInferVar,
            GenericSubst, HrtbUniverse, ImportWfMode, ObligationNotReady, ObligationResult,
            ObligationTermination, clause::UniversalTyDescriptor,
        },
        syntax::{
            AnyGeneric, HrtbBinder, HrtbDebruijnDef, InferTyVar, InferTyVarSourceInfo, Mutability,
            Re, RelationMode, SimpleTySet, TraitClause, TraitClauseList, TraitParam, TraitSpec, Ty,
            TyCtxt, TyFolder, TyFolderInfallibleExt, TyKind, TyOrRe, TyVisitor, TyVisitorExt,
            UniversalReVarSourceInfo, UniversalTy, UniversalTyProjectionInner,
        },
    },
    symbol,
    utils::hash::{FxHashMap, FxHashSet},
};
use smallvec::SmallVec;
use std::{collections::VecDeque, convert::Infallible, ops::ControlFlow, rc::Rc};

// === Public Interface === //

#[derive(Debug, Clone)]
pub struct UniversalElaboration {
    pub clauses: TraitClauseList,
    pub lub_re: Re,
    pub wip_reification_state: Option<WipReificationState>,
}

impl UniversalElaboration {
    // FIXME: Can become stale accidentally
    pub fn collect_roots_if_floating(&self, ccx: &ClauseCx<'_>) -> Option<WipReificationRootSet> {
        self.wip_reification_state
            .as_ref()
            .map(|v| v.collect_roots(ccx))
    }
}

#[derive(Debug, Clone)]
pub struct WipReificationState(Rc<FxHashMap<InferTyVar, WipReifiedVar>>);

#[derive(Debug, Clone)]
pub struct WipReificationRootSet(FxHashSet<InferTyVar>);

#[derive(Debug, Clone)]
struct WipReifiedVar {
    reified_clauses: Option<TraitClauseList>,
    universal: HrtbUniverse,
    src_info_spec: TraitSpec,
    src_info_idx: u32,
}

impl WipReificationState {
    pub fn collect_roots(&self, ccx: &ClauseCx<'_>) -> WipReificationRootSet {
        WipReificationRootSet(
            self.0
                .keys()
                .map(|&var| ccx.lookup_ty_infer_var_without_poll(var).unwrap_err().root)
                .collect(),
        )
    }
}

impl<'tcx> ClauseCx<'tcx> {
    pub fn elaborate_ty_universal_clauses_possibly_floating(
        &mut self,
        universal: UniversalTy,
    ) -> UniversalElaboration {
        let s = self.session();
        let tcx = self.tcx();

        // See whether this universal variable has been elaborated yet.
        if let Some(elaborated) = self.universal_vars[&universal].elaboration.clone() {
            return elaborated;
        }

        let var_universe = self.lookup_universal_ty_hrtb_universe(universal).clone();

        // If not, elaborate the clause list without merging projections.
        let lub_re = self.fresh_re_universal(UniversalReVarSourceInfo::ElaboratedLub);

        let mut elaborated = Vec::new();
        let mut queue = VecDeque::from_iter(
            self.direct_ty_universal_clauses_possibly_floating(universal)
                .r(s)
                .iter()
                .copied(),
        );

        let mut reified_vars = FxHashMap::default();

        while let Some(target) = queue.pop_front() {
            match target {
                TraitClause::Outlives(outlive_dir, outlive) => {
                    self.permit_universe_re_outlives_general(lub_re, outlive, outlive_dir);
                    elaborated.push(TraitClause::Outlives(outlive_dir, outlive));
                }
                TraitClause::Trait(HrtbBinder { defs, inner: spec }) => {
                    // Replace unspecified parameters with fresh universals.
                    let new_param_equals = spec
                        .params
                        .r(s)
                        .iter()
                        .enumerate()
                        .map(|(idx, param)| match *param {
                            TraitParam::Equals(ty_or_re) => ty_or_re,
                            TraitParam::Unspecified(_) => {
                                let universal =
                                    self.lookup_universal_ty_hrtb_universe(universal).clone();
                                let var = self.fresh_ty_infer_var(
                                    // Associated types vary in the same way as their parent generic.
                                    universal.clone(),
                                    InferTyVarSourceInfo::ElaborationUnifyHelper,
                                );

                                reified_vars.insert(
                                    var,
                                    WipReifiedVar {
                                        reified_clauses: None,
                                        universal,
                                        src_info_spec: spec,
                                        src_info_idx: idx as u32,
                                    },
                                );

                                TyOrRe::Ty(tcx.intern(TyKind::InferVar(var)))
                            }
                        })
                        .collect::<Vec<_>>();

                    let new_param_equals = tcx.intern_list(&new_param_equals);

                    // Fill in each universal parameter's direct inheritance list.
                    for ((new_param, base), spec_param) in new_param_equals
                        .r(s)
                        .iter()
                        .zip(&spec.def.r(s).generics.r(s).defs)
                        .zip(spec.params.r(s).iter())
                    {
                        let TraitParam::Unspecified(explicit_clauses) = *spec_param else {
                            continue;
                        };

                        let (&TyOrRe::Ty(new_param_ty), AnyGeneric::Ty(base)) = (new_param, base)
                        else {
                            unreachable!()
                        };

                        let TyKind::InferVar(new_param) = *new_param_ty.r(s) else {
                            unreachable!()
                        };

                        let implicit_clauses = self
                            .importer(
                                ClauseFuel::new(),
                                // Associated types vary in the same way as their parent generic.
                                var_universe.clone(),
                                ClauseImportEnv::new(
                                    Some(tcx.intern(TyKind::Universal(universal))),
                                    [GenericSubst::new(*spec.def.r(s).generics, new_param_equals)],
                                ),
                                ImportWfMode::ReportElsewhere,
                            )
                            .import_trait_clause_list(*base.r(s).clauses)
                            // N.B. we're importing with maximum fuel so, if this fails, the primary
                            // `ReportHere` import should also fail.
                            .report_delay_bug();

                        let all_clauses = explicit_clauses
                            .r(s)
                            .iter()
                            .chain(implicit_clauses.r(s))
                            .copied()
                            .collect::<Vec<_>>();

                        let all_clauses = tcx.intern_list(&all_clauses);

                        reified_vars.get_mut(&new_param).unwrap().reified_clauses =
                            Some(all_clauses);
                    }

                    // Push on the elaborated trait `impl` constraint.
                    let new_params = new_param_equals
                        .r(s)
                        .iter()
                        .map(|&ty_or_re| TraitParam::Equals(ty_or_re))
                        .collect::<Vec<_>>();

                    let new_params = tcx.intern_list(&new_params);

                    elaborated.push(TraitClause::Trait(HrtbBinder {
                        defs,
                        inner: TraitSpec {
                            def: spec.def,
                            params: new_params,
                        },
                    }));

                    // Explore and push on the elaborated super-trait constraints.
                    let inherits = self
                        .importer(
                            ClauseFuel::new(),
                            // Associated types vary in the same way as their parent generic.
                            var_universe.clone(),
                            ClauseImportEnv::new(
                                Some(tcx.intern(TyKind::Universal(universal))),
                                [GenericSubst::new(*spec.def.r(s).generics, new_param_equals)],
                            ),
                            ImportWfMode::ReportElsewhere,
                        )
                        .import_trait_clause_list(*spec.def.r(s).inherits)
                        // See above.
                        .report_delay_bug();

                    elaborated.extend(inherits.r(s).iter().copied());
                }
            }
        }

        let elaborated = self.tcx().intern_list(&elaborated);

        let reified_vars = WipReificationState(Rc::new(reified_vars));

        // Create an obligation to properly resolve reified associated type inference variables to
        // proper universals (see module comment).
        self.push_obligation(ClauseObligation::UnifyReifiedElaboratedClauses {
            root: universal,
            clauses: elaborated,
            reified_vars: reified_vars.clone(),
        });

        // Record the elaboration and return it.
        let elaborated = UniversalElaboration {
            clauses: elaborated,
            lub_re,
            wip_reification_state: Some(reified_vars),
        };
        self.universal_vars.get_mut(&universal).unwrap().elaboration = Some(elaborated.clone());

        elaborated
    }

    pub fn is_elaborated_clause_ready_if_selected(
        &self,
        reified_var_roots: Option<&WipReificationRootSet>,
        clause: HrtbBinder,
    ) -> bool {
        let Some(reified_var_roots) = reified_var_roots else {
            return true;
        };

        FloatingInfVarVisitor {
            ccx: self,
            reified_var_roots,
        }
        .visit_fallible(clause)
        .is_continue()
    }
}

// === Obligation === //

impl ClauseCx<'_> {
    pub(super) fn oblige_unify_reified_elaborated_clauses(
        &mut self,
        root: UniversalTy,
        clauses: TraitClauseList,
        reified_vars: WipReificationState,
    ) -> ObligationResult {
        let s = self.session();
        let tcx = self.tcx();

        let reified_var_roots = reified_vars.collect_roots(self);

        // First, we must ensure that all remaining inference variables are either resolved or are
        // in the `reified_vars` set. If they aren't, the obligation isn't ready to run.
        for &clause in clauses.r(s) {
            let TraitClause::Trait(clause) = clause else {
                continue;
            };

            let clause = HrtbBinder {
                defs: clause.defs,
                inner: TraitSpec {
                    def: clause.inner.def,
                    // No need to replace the associated parameters because this is just used for
                    // visiting.
                    params: tcx.intern_list(
                        &clause.inner.params.r(s)
                            [..*clause.inner.def.r(s).regular_generic_count as usize],
                    ),
                },
            };

            if (FloatingInfVarVisitor {
                ccx: self,
                reified_var_roots: &reified_var_roots,
            }
            .visit_fallible(clause)
            .is_break())
            {
                return Err(ObligationNotReady::ElabStillResolving);
            }
        }

        // Next, let's attempt to determine which clauses should be merged together. Since there are
        // no inference variables in the types beyond our unique-constrained ones and unification
        // only allows region-based sub-typing, we can simply erase lifetimes and normalize types to
        // their roots to obtain a representative type indicating whether two types could possibly
        // unify. We still have to perform actual unification after this phase to ensure regions are
        // properly constrained.
        let mut merged_clauses = FxHashMap::<HrtbBinder, SmallVec<[HrtbBinder; 1]>>::default();

        for &clause in clauses.r(s) {
            let TraitClause::Trait(
                clause @ HrtbBinder {
                    defs,
                    inner: TraitSpec { def, params },
                },
            ) = clause
            else {
                continue;
            };

            let key = HrtbBinder {
                defs,
                inner: TraitSpec {
                    def,
                    // No need to replace the associated parameters because this is just a key.
                    params: tcx
                        .intern_list(&params.r(s)[..*def.r(s).regular_generic_count as usize]),
                },
            };

            let key = MergeRepresentativeFolder {
                ccx: self,
                reified_var_roots: &reified_var_roots,
            }
            .fold(key);

            merged_clauses.entry(key).or_default().push(clause);
        }

        // Finally, let's give our unification variables their actual identities.
        for clauses in merged_clauses.into_values() {
            let def = clauses.first().unwrap().inner.def;
            let regular_generic_count = *def.r(s).regular_generic_count as usize;

            // Determine what the associated type parameter should be.
            #[derive(Debug)]
            enum AssocParam<'a> {
                Uninit,
                Reified(&'a WipReifiedVar, SmallVec<[TraitClauseList; 1]>),
                Concrete(Ty),
            }

            let mut assoc_params = def
                .r(s)
                .generics
                .r(s)
                .defs
                .iter()
                .skip(regular_generic_count)
                .map(|_| AssocParam::Uninit)
                .collect::<Vec<_>>();

            for &HrtbBinder {
                defs: _,
                inner: spec,
            } in &clauses
            {
                // N.B. we use `spec` without any late lookup to allow us to detect which types were
                // originally elaboration universals.
                for (resolved, actual) in assoc_params
                    .iter_mut()
                    .zip(&spec.params.r(s)[regular_generic_count..])
                {
                    let TraitParam::Equals(TyOrRe::Ty(actual)) = *actual else {
                        unreachable!()
                    };

                    // See whether this parameter is a reified parameter.
                    if let TyKind::InferVar(var) = *actual.r(s)
                        && let Some(reified) = reified_vars.0.get(&var)
                    {
                        match resolved {
                            AssocParam::Uninit => {
                                *resolved = AssocParam::Reified(
                                    reified,
                                    smallvec::smallvec![reified.reified_clauses.unwrap()],
                                );
                            }
                            AssocParam::Reified(_, clauses) => {
                                clauses.push(reified.reified_clauses.unwrap());
                            }
                            AssocParam::Concrete(_) => {
                                // (ignored)
                            }
                        }

                        continue;
                    }

                    // Otherwise, turn the parameter into a concrete one.
                    match resolved {
                        AssocParam::Uninit | AssocParam::Reified(..) => {
                            *resolved = AssocParam::Concrete(actual);
                        }
                        AssocParam::Concrete(_) => {
                            // (keep the previous value)
                        }
                    }
                }
            }

            for assoc_param in &mut assoc_params {
                match assoc_param {
                    AssocParam::Uninit => unreachable!(),
                    AssocParam::Concrete(_) => {
                        // (keep as is)
                    }
                    AssocParam::Reified(first_wip, clauses) => {
                        let var = UniversalTy::Projection(tcx.intern(UniversalTyProjectionInner {
                            target: root,
                            spec: first_wip.src_info_spec,
                            assoc_idx: first_wip.src_info_idx,
                        }));

                        // TODO: normalize `var`

                        let clauses = clauses
                            .iter()
                            .flat_map(|v| v.r(s))
                            .copied()
                            .collect::<Vec<_>>();

                        let clauses = tcx.intern_list(&clauses);

                        // FIXME: This is cursed.
                        self.universal_vars.insert(
                            var,
                            UniversalTyDescriptor {
                                direct_clauses: Some(clauses),
                                elaboration: None,
                            },
                        );

                        *assoc_param = AssocParam::Concrete(tcx.intern(TyKind::Universal(var)));
                    }
                }
            }

            // Unify all the associated parameters with the target.
            for &HrtbBinder {
                defs: _,
                inner: spec,
            } in &clauses
            {
                for (resolved, actual) in assoc_params
                    .iter_mut()
                    .zip(&spec.params.r(s)[regular_generic_count..])
                {
                    let AssocParam::Concrete(resolved) = *resolved else {
                        unreachable!()
                    };

                    let TraitParam::Equals(TyOrRe::Ty(actual)) = *actual else {
                        unreachable!()
                    };

                    if let TyKind::InferVar(var) = *actual.r(s) {
                        self.force_update_permissions_of_ty_var(var, SimpleTySet::all());
                    }

                    self.oblige_ty_unifies_ty(resolved, actual, RelationMode::Equate)
                        // Permission sets ensure that this always succeeds.
                        .report_delay_bug();
                }
            }

            // Unify the non-associated generic parameters to ensure lifetimes are correct.
            let (&first, remaining) = clauses.split_first().unwrap();

            for &remaining in remaining {
                let fresh_re = self.fresh_re_infer();

                self.oblige_ty_unifies_ty(
                    tcx.intern(TyKind::Trait(
                        fresh_re,
                        Mutability::Mut,
                        tcx.intern_list(&[TraitClause::Trait(first)]),
                    )),
                    tcx.intern(TyKind::Trait(
                        fresh_re,
                        Mutability::Mut,
                        tcx.intern_list(&[TraitClause::Trait(remaining)]),
                    )),
                    RelationMode::Equate,
                )
                // TODO: Check this.
                .report_delay_bug();
            }
        }

        self.universal_vars
            .get_mut(&root)
            .unwrap()
            .elaboration
            .as_mut()
            .unwrap()
            .wip_reification_state = None;

        Ok(ObligationTermination::Regular)
    }
}

struct FloatingInfVarVisitor<'a, 'tcx> {
    ccx: &'a ClauseCx<'tcx>,
    reified_var_roots: &'a WipReificationRootSet,
}

impl<'tcx> TyVisitor<'tcx> for FloatingInfVarVisitor<'_, 'tcx> {
    type Break = ();

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn visit_ty(&mut self, ty: Ty) -> ControlFlow<Self::Break> {
        let s = self.session();

        match *ty.r(s) {
            TyKind::InferVar(var) => match self.ccx.lookup_ty_infer_var_without_poll(var) {
                Ok(ty) => self.walk_fallible(ty),
                Err(FloatingInferVar { root: var_root, .. }) => {
                    if self.reified_var_roots.0.contains(&var_root) {
                        return ControlFlow::Continue(());
                    }

                    ControlFlow::Break(())
                }
            },
            _ => self.walk_fallible(ty),
        }
    }
}

struct MergeRepresentativeFolder<'a, 'tcx> {
    ccx: &'a ClauseCx<'tcx>,
    reified_var_roots: &'a WipReificationRootSet,
}

impl<'tcx> TyFolder<'tcx> for MergeRepresentativeFolder<'_, 'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn fold_hrtb_debruijn_def(
        &mut self,
        defs: HrtbDebruijnDef,
    ) -> Result<HrtbDebruijnDef, Self::Error> {
        Ok(HrtbDebruijnDef {
            span: Span::DUMMY,
            name: symbol!(""),
            kind: defs.kind,
            clauses: self.fold(defs.clauses),
        })
    }

    fn fold_ty(&mut self, ty: Ty) -> Result<Ty, Self::Error> {
        let s = self.session();
        let tcx = self.tcx();

        Ok(match *ty.r(s) {
            TyKind::InferVar(var) => match self.ccx.lookup_ty_infer_var_without_poll(var) {
                Ok(ty) => self.fold(ty),
                Err(FloatingInferVar { root: root_var, .. }) => {
                    debug_assert!(self.reified_var_roots.0.contains(&root_var));
                    tcx.intern(TyKind::InferVar(root_var))
                }
            },
            _ => self.super_(ty),
        })
    }

    fn fold_re(&mut self, _re: Re) -> Result<Re, Self::Error> {
        Ok(Re::Erased)
    }
}
