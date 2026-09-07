use crate::{
    base::arena::{HasInterner as _, HasListInterner},
    semantic::{
        infer::{
            ClauseCx, ClauseFuel, ClauseImportEnv, ClauseObligation, GenericSubst, ImportWfMode,
            InstantiatedTraitSpec, ObligationResult, ObligationTermination,
        },
        syntax::{
            HrtbBinder, HrtbDebruijnDef, InferTyVarSourceInfo, Re, TraitClause, TraitParam,
            TraitSpec, TyKind, TyOrRe, TyOrReList, UniversalReVarSourceInfo, UniversalTy,
        },
    },
    utils::hash::FxHashSet,
};
use rustc_hash::FxHashMap;
use std::collections::VecDeque;

// === Driver === //

#[derive(Debug, Clone)]
pub struct UniversalElaboration {
    pub lub_re: Re,
    pub hrtb_universals: FxHashMap<TyOrRe, HrtbDebruijnDef>,
    pub elaborated_clauses: Vec<ElaboratedClause>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
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
        instantiated_with_late: TyOrReList,
    },

    /// A fully elaborated clause, which can be used without any caveats.
    Ready(HrtbBinder),
}

impl<'tcx> ClauseCx<'tcx> {
    pub fn elaborate_universal(&mut self, universal: UniversalTy) -> UniversalElaboration {
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

            let instantiated_with_late = tcx.intern_list(
                &instantiated
                    .params
                    .r(s)
                    .iter()
                    .map(|&param| match param {
                        TraitParam::Equals(eq) => eq,
                        TraitParam::Unspecified(_spec) => TyOrRe::Ty(self.fresh_ty_infer(
                            var_universe.clone(),
                            InferTyVarSourceInfo::LateAssocElabPlaceholder,
                        )),
                    })
                    .collect::<Vec<_>>(),
            );

            elaborated_clauses.push(ElaboratedClause::NotReady {
                instantiated,
                instantiated_with_late,
            });

            // Record our HRTB universals so we can recover them.
            hrtb_universals.extend(
                hrtbs_as_universals
                    .r(s)
                    .iter()
                    .copied()
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
        let elaborated_clauses = move |ccx: &mut ClauseCx<'_>| -> &mut Vec<ElaboratedClause> {
            let Some(UniversalElaboration {
                lub_re: _,
                hrtb_universals: _,
                elaborated_clauses,
            }) = self.universal_ty_elaboration_state_mut(universal)
            else {
                unreachable!()
            };

            elaborated_clauses
        };

        let mut shadowed_clauses = FxHashSet::default();
        let mut next_clause_idx = 0usize;

        'outer: while next_clause_idx < elaborated_clauses(self).len() {
            let curr_clause_idx = next_clause_idx;
            next_clause_idx += 1;

            if shadowed_clauses.contains(&curr_clause_idx) {
                continue;
            }

            let ElaboratedClause::NotReady {
                instantiated,
                instantiated_with_late,
            } = elaborated_clauses(self)[curr_clause_idx]
            else {
                continue;
            };

            // First, ensure that `instantiated` has all its inference variables solved.
            // TODO

            // Next, let's build up a full context for all our clauses by considering subsequent
            // clauses.
            // TODO

            // We have enough information to finish this clause. Convert it into its HRTB form and
            // mark it as done.
            // TODO
        }

        match is_done {
            true => Ok(ObligationTermination::Finished),
            false => Ok(ObligationTermination::CommitAndKeep),
        }
    }

    pub fn hrtb_binder_from_elab_universals(
        &mut self,
        universal: UniversalTy,
        instantiated: TraitSpec,
    ) -> Option<HrtbBinder> {
        todo!()
    }
}
