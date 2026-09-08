use crate::{
    base::{
        analysis::{DebruijnRelative, DebruijnTop},
        arena::{HasInterner as _, HasListInterner},
    },
    semantic::{
        infer::{
            ClauseCx, ClauseFuel, ClauseImportEnv, ClauseObligation, GenericSubst, ImportWfMode,
            InstantiatedTraitSpec, ObligationNotReady, ObligationResult, ObligationTermination,
        },
        syntax::{
            HrtbBinder, HrtbDebruijn, HrtbDebruijnDef, HrtbProjection, InferTyVar,
            InferTyVarSourceInfo, Re, RelationMode, TraitClause, TraitParam, TraitSpec, Ty, TyCtxt,
            TyFolder, TyFolderInfallibleExt, TyKind, TyOrRe, TyVisitor, TyVisitorInfallibleExt,
            UniversalReVarSourceInfo, UniversalTy, UniversalTyOrReRoot, UniversalTyProjInner,
        },
    },
    utils::hash::{FxHashMap, FxHashSet},
};
use hashbrown::hash_map;
use std::{collections::VecDeque, convert::Infallible, num::NonZeroU32, ops::ControlFlow, rc::Rc};

// === Driver === //

#[derive(Debug, Clone)]
pub struct UniversalElaboration {
    pub lub_re: Re,
    pub hrtb_universals: FxHashMap<UniversalTyOrReRoot, HrtbDebruijnDef>,
    pub elaborated_clauses: Vec<ElaboratedClause>,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum ElaboratedClause {
    /// A clause which hasn't yet finished the elaboration process. If this clause is accepted, the
    /// selection fork must be rejected and the obligation must be deferred until the clause becomes
    /// `Ready`.
    NotReady {
        /// A partially elaborated clause which...
        ///
        /// - may contain `Unspecified` associated type parameters
        /// - may contain inference variables which haven't yet been solved
        /// - may contain temporary universals to fill in for HRTB variables; see `hrtb_universals`
        ///
        instantiated: TraitSpec,

        /// Associated types without equality constraints are instantiated to inference variables
        /// during elaboration so super-traits can have their parent inferences. These are unified
        /// with the fully-elaborated associated type upon transition to `Ready`. This field
        /// contains the temporary expansion we created for super-trait elaboration purposes.
        late_assoc_params: Rc<[Option<InferTyVar>]>,
    },

    /// A fully elaborated clause, which can be used without any caveats.
    Ready(HrtbBinder),
}

impl<'tcx> ClauseCx<'tcx> {
    pub fn elaborate_universal_or_request(
        &mut self,
        universal: UniversalTy,
    ) -> ObligationResult<UniversalElaboration> {
        if let Some(cached) = self.universal_ty_elaboration_state(universal).cloned() {
            Ok(cached)
        } else {
            Err(ObligationNotReady::RequestMissingElaboration(universal))
        }
    }

    pub fn elaborate_universal_immediately(
        &mut self,
        universal: UniversalTy,
    ) -> UniversalElaboration {
        let s = self.session();
        let tcx = self.tcx();

        // See whether this universal variable has been elaborated yet.
        if let Some(cached) = self.universal_ty_elaboration_state(universal).cloned() {
            return cached;
        }

        // If not, elaborate the clause list into its `NotReady` form.
        let var_universe = self.lookup_universal_ty_hrtb_universe(universal).clone();
        let lub_re = self.fresh_re_universal(UniversalReVarSourceInfo::ElaboratedLub);

        let mut elaborated_clauses = Vec::new();
        let mut hrtb_universals = FxHashMap::default();

        let mut queue = self
            .direct_ty_universal_clauses_possibly_floating(universal)
            .r(s)
            .iter()
            .copied()
            .collect::<VecDeque<_>>();

        while let Some(target) = queue.pop_front() {
            // Handle the simple outlives case.
            let binder = match target {
                TraitClause::Outlives(outlive_dir, outlive) => {
                    self.permit_universe_re_outlives_general(lub_re, outlive, outlive_dir);
                    continue;
                }
                TraitClause::Trait(binder) => binder,
            };

            // Otherwise, instantiate the clause and push its elaboration.
            let InstantiatedTraitSpec {
                spec: instantiated,
                params: hrtbs_as_universals,
            } = self
                .instantiate_hrtb_universal(ClauseFuel::new(), var_universe.clone(), binder)
                // TODO
                .report_delay_bug();

            let mut late_assoc_params = Vec::new();

            let instantiated_with_late = tcx.intern_list(
                &instantiated
                    .params
                    .r(s)
                    .iter()
                    .enumerate()
                    .map(|(idx, &param)| {
                        let is_assoc = idx >= *instantiated.def.r(s).regular_generic_count as usize;

                        match param {
                            TraitParam::Equals(eq) => {
                                if is_assoc {
                                    late_assoc_params.push(None);
                                }

                                eq
                            }
                            TraitParam::Unspecified(_spec) => {
                                let var = self.fresh_ty_infer_var(
                                    var_universe.clone(),
                                    InferTyVarSourceInfo::LateAssocElabPlaceholder,
                                );

                                debug_assert!(is_assoc);
                                late_assoc_params.push(Some(var));

                                TyOrRe::Ty(tcx.intern(TyKind::InferVar(var)))
                            }
                        }
                    })
                    .collect::<Vec<_>>(),
            );

            elaborated_clauses.push(ElaboratedClause::NotReady {
                instantiated,
                late_assoc_params: Rc::from_iter(late_assoc_params),
            });

            // Record our HRTB universals so we can recover them.
            hrtb_universals.extend(
                hrtbs_as_universals
                    .r(s)
                    .iter()
                    .map(|&param| match param {
                        TyOrRe::Re(root) => UniversalTyOrReRoot::Re(root),
                        TyOrRe::Ty(ty)
                            if let TyKind::Universal(UniversalTy::Root(root)) = *ty.r(s) =>
                        {
                            UniversalTyOrReRoot::Ty(root)
                        }
                        _ => unreachable!(),
                    })
                    .zip(binder.defs.r(s).iter().copied()),
            );

            // Explore and push on the elaborated super-trait constraints.
            let inherits = self
                .importer(
                    ClauseFuel::new(),
                    // Associated types vary in the same way as their parent generic.
                    var_universe.clone(),
                    ClauseImportEnv::new(
                        Some(tcx.intern(TyKind::Universal(universal))),
                        [GenericSubst::new(
                            *instantiated.def.r(s).generics,
                            instantiated_with_late,
                        )],
                    ),
                    ImportWfMode::ReportElsewhere,
                )
                .import_trait_clause_list(*instantiated.def.r(s).inherits)
                // TODO
                .report_delay_bug();

            queue.extend(inherits.r(s).iter().copied());
        }

        // Push an obligation to repeatedly poll for completion of `NotReady` clauses.
        let elaboration = UniversalElaboration {
            lub_re,
            hrtb_universals,
            elaborated_clauses,
        };

        *self.universal_ty_elaboration_state_mut(universal) = Some(elaboration.clone());

        self.push_obligation(ClauseObligation::PollElaboration { universal });

        elaboration
    }

    pub(super) fn run_poll_elaboration(&mut self, universal: UniversalTy) -> ObligationResult {
        fn elaborated_clauses<'a>(
            ccx: &'a mut ClauseCx<'_>,
            universal: UniversalTy,
        ) -> &'a mut Vec<ElaboratedClause> {
            let Some(UniversalElaboration {
                lub_re: _,
                hrtb_universals: _,
                elaborated_clauses,
            }) = ccx.universal_ty_elaboration_state_mut(universal)
            else {
                unreachable!()
            };

            elaborated_clauses
        }

        let s = self.session();
        let tcx = self.tcx();

        let mut shadowed_clauses = FxHashSet::<usize>::default();
        let mut next_clause_idx = 0usize;

        while next_clause_idx < elaborated_clauses(self, universal).len() {
            let curr_clause_idx = next_clause_idx;
            next_clause_idx += 1;

            if shadowed_clauses.contains(&curr_clause_idx) {
                continue;
            }

            let ElaboratedClause::NotReady {
                mut instantiated,
                late_assoc_params: ref instantiated_with_late,
            } = elaborated_clauses(self, universal)[curr_clause_idx]
            else {
                continue;
            };

            let instantiated_with_late = instantiated_with_late.clone();

            // First, ensure that `instantiated` has all its inference variables solved.
            // TODO

            // Next, let's build up a full context for all our clauses by considering subsequent
            // clauses.
            // TODO

            // Next, unify `instantiated_with_late` with universals based off of HRTB temporary
            // universals.
            {
                let regular_generic_count = *instantiated.def.r(s).regular_generic_count as usize;

                for ((idx, &param), &late_init) in instantiated
                    .params
                    .r(s)
                    .iter()
                    .enumerate()
                    .skip(regular_generic_count)
                    .zip(instantiated_with_late.iter())
                {
                    let Some(late_init_var) = late_init else {
                        continue;
                    };

                    let late_init_to = match param {
                        TraitParam::Equals(eq) => eq.unwrap_ty(),
                        TraitParam::Unspecified(clauses) => {
                            let projection =
                                self.fresh_ty_universal_proj(universal, instantiated, idx as u32);

                            self.init_ty_universal_direct_clauses(projection, clauses);

                            tcx.intern(TyKind::Universal(projection))
                        }
                    };

                    self.unify_ty_and_ty(
                        tcx.intern(TyKind::InferVar(late_init_var)),
                        late_init_to,
                        RelationMode::Equate,
                    )
                    .unwrap()
                    .report_never();
                }
            }

            // We have enough information to finish this clause. Convert it into its HRTB form and
            // mark it as done.
            let finished_binder = self.hrtb_binder_from_elab_universals(universal, instantiated);

            if !self.is_hrtb_binder_from_elab_universals_covered(finished_binder) {
                // Discard the clause since it contains projections which cannot be effectively
                // covered by an HRTB binder.
                elaborated_clauses(self, universal).remove(curr_clause_idx);
                next_clause_idx -= 1;

                continue;
            }

            elaborated_clauses(self, universal)[curr_clause_idx] =
                ElaboratedClause::Ready(finished_binder);
        }

        match elaborated_clauses(self, universal)
            .iter()
            .all(|v| matches!(v, ElaboratedClause::Ready(_)))
        {
            true => Ok(ObligationTermination::Finished),
            false => Ok(ObligationTermination::CommitAndKeep),
        }
    }
}

// === HRTB universals to binder === //

impl<'tcx> ClauseCx<'tcx> {
    pub fn hrtb_binder_from_elab_universals(
        &mut self,
        universal: UniversalTy,
        instantiated: TraitSpec,
    ) -> HrtbBinder {
        let tcx = self.tcx();

        let mut folder = HrtbReverseTranscriptase {
            ccx: self,
            universal,
            universal_root_to_debruijn: FxHashMap::default(),
            debruijn_defs_backward: Vec::new(),
        };

        let inner = folder.fold(instantiated);

        folder.debruijn_defs_backward.reverse();

        HrtbBinder {
            defs: tcx.intern_list(&folder.debruijn_defs_backward),
            inner,
        }
    }

    pub fn is_hrtb_binder_from_elab_universals_covered(&self, binder: HrtbBinder) -> bool {
        let s = self.session();

        let mut cover_visitor = HrtbCoverChecker {
            ccx: self,
            was_covered: (0..binder.defs.r(s).len()).map(|_| false).collect(),
            top: DebruijnTop::new(binder.defs.r(s).len()),
        };

        cover_visitor.visit(binder.inner);

        cover_visitor.was_covered.iter().all(|&v| v)
    }
}

struct HrtbReverseTranscriptase<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    universal: UniversalTy,
    universal_root_to_debruijn: FxHashMap<UniversalTyOrReRoot, u32>,
    debruijn_defs_backward: Vec<HrtbDebruijnDef>,
}

impl HrtbReverseTranscriptase<'_, '_> {
    fn universal_to_hrtb_if_was_instantiated(
        &mut self,
        var: UniversalTyOrReRoot,
    ) -> Option<HrtbDebruijn> {
        let entry = match self.universal_root_to_debruijn.entry(var) {
            hash_map::Entry::Occupied(entry) => {
                let idx = *entry.into_mut();

                return Some(HrtbDebruijn(DebruijnRelative::new(
                    NonZeroU32::new(idx + 1).unwrap(),
                )));
            }
            hash_map::Entry::Vacant(entry) => entry,
        };

        let def = self
            .ccx
            .universal_ty_elaboration_state(self.universal)
            .as_ref()
            .unwrap()
            .hrtb_universals
            .get(&var)
            .copied()?;

        let idx = self.debruijn_defs_backward.len() as u32;

        entry.insert(idx);

        self.debruijn_defs_backward.push(def);

        Some(HrtbDebruijn(DebruijnRelative::new(
            NonZeroU32::new(idx + 1).unwrap(),
        )))
    }
}

impl<'tcx> TyFolder<'tcx> for HrtbReverseTranscriptase<'_, 'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn fold_re(&mut self, re: Re) -> Result<Re, Self::Error> {
        let Re::UniversalVar(universal) = re else {
            return Ok(re);
        };

        let Some(debruijn) = self.universal_to_hrtb_if_was_instantiated(UniversalTyOrReRoot::Re(
            Re::UniversalVar(universal),
        )) else {
            // Not an HRTB.
            return Ok(re);
        };

        Ok(Re::HrtbVar(debruijn))
    }

    fn fold_ty(&mut self, ty: Ty) -> Result<Ty, Self::Error> {
        let tcx = self.tcx();
        let s = self.session();

        let ty = self.ccx.peel_ty_infer_var_without_poll(ty);

        let TyKind::Universal(universal) = *ty.r(s) else {
            return Ok(self.super_(ty));
        };

        match universal {
            UniversalTy::Root(root) => {
                let Some(debruijn) =
                    self.universal_to_hrtb_if_was_instantiated(UniversalTyOrReRoot::Ty(root))
                else {
                    // Not an HRTB.
                    return Ok(tcx.intern(TyKind::Universal(universal)));
                };

                Ok(tcx.intern(TyKind::HrtbVar(debruijn)))
            }
            UniversalTy::Projection(proj) => {
                let UniversalTyProjInner {
                    target,
                    as_spec,
                    assoc_idx,
                    cache_idx: _,
                } = *proj.r(s);

                let target = self.fold(tcx.intern(TyKind::Universal(target)));
                let as_spec = self.fold(as_spec);

                // TODO: only spawn if this is a new HRTB derivation (not needed for correctness but
                // possibly useful for performance)
                Ok(tcx.intern(TyKind::HrtbProjection(HrtbProjection {
                    target: target,
                    spec: as_spec,
                    assoc_idx,
                })))
            }
        }
    }

    fn fold_universal(&mut self, _ty: UniversalTy) -> Result<UniversalTy, Self::Error> {
        unreachable!()
    }
}

struct HrtbCoverChecker<'a, 'tcx> {
    ccx: &'a ClauseCx<'tcx>,
    was_covered: Vec<bool>,
    top: DebruijnTop,
}

impl HrtbCoverChecker<'_, '_> {
    fn visit_debruijn(&mut self, var: HrtbDebruijn) {
        if let Some(status) = self
            .was_covered
            .get_mut(self.top.lookup_relative(var.0).index())
        {
            *status = true;
        }
    }
}

impl<'tcx> TyVisitor<'tcx> for HrtbCoverChecker<'_, 'tcx> {
    type Break = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn visit_hrtb_binder(&mut self, binder: HrtbBinder) -> ControlFlow<Self::Break> {
        let s = self.session();

        let range = self.top.move_inwards_by(binder.defs.r(s).len());
        self.visit(binder.inner);
        self.top.move_outwards_by(range.len());

        ControlFlow::Continue(())
    }

    fn visit_re(&mut self, re: Re) -> ControlFlow<Self::Break> {
        if let Re::HrtbVar(var) = re {
            self.visit_debruijn(var);
        }

        ControlFlow::Continue(())
    }

    fn visit_ty(&mut self, ty: Ty) -> ControlFlow<Self::Break> {
        let s = self.session();
        let ty = self.ccx.peel_ty_infer_var_without_poll(ty);

        if let TyKind::HrtbVar(var) = *ty.r(s) {
            self.visit_debruijn(var);
        }

        ControlFlow::Continue(())
    }

    fn visit_hrtb_projection(&mut self, _projection: HrtbProjection) -> ControlFlow<Self::Break> {
        // (ignore `projection` since it doesn't contribute to cover)

        ControlFlow::Continue(())
    }
}
