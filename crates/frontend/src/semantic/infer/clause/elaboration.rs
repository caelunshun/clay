use crate::{
    base::arena::{HasInterner as _, HasListInterner},
    semantic::{
        infer::{
            ClauseCx, ClauseFuel, ClauseImportEnv, ClauseObligation, GenericSubst, ImportWfMode,
            InstantiatedTraitSpec, ObligationResult, ObligationTermination,
        },
        syntax::{
            HrtbBinder, HrtbDebruijnDefList, InferTyVarSourceInfo, Re, TraitClause, TraitParam,
            TraitSpec, TyKind, TyOrRe, TyOrReList, UniversalReVarSourceInfo, UniversalTy,
        },
    },
};
use std::collections::VecDeque;

#[derive(Debug, Clone)]
pub struct UniversalElaboration {
    pub lub_re: Re,
    pub elaborated_clauses: Vec<ElaboratedClause>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ElaboratedClause {
    /// A clause which hasn't yet finished the elaboration process. If this clause is accepted, the
    /// selection fork must be rejected and the obligation must be deferred until the clause becomes
    /// `Ready`.
    NotReady {
        /// The set of binder variables from the root clause from which this clause was elaborated.
        /// Might not cover `instantiated` and may need to be reduced before creating its equivalent
        /// `Ready` form.
        binder_defs: HrtbDebruijnDefList,

        /// The universals spawned for each binder definition.
        universal_roots: TyOrReList,

        /// A partially elaborated clause which...
        ///
        /// - may contain `Unspecified` associated type parameters
        /// - may contain temporary universals to fill in for HRTB variables
        /// - may contain inference variables which haven't yet been solved
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
            let binder_defs = binder.defs;
            let InstantiatedTraitSpec {
                spec: instantiated,
                params: universal_roots,
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
                            InferTyVarSourceInfo::ElaborationUnifyHelper,
                        )),
                    })
                    .collect::<Vec<_>>(),
            );

            elaborated_clauses.push(ElaboratedClause::NotReady {
                binder_defs,
                universal_roots,
                instantiated,
                instantiated_with_late,
            });

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
            elaborated_clauses,
        };

        *self.universal_ty_elaboration_state_mut(universal) = Some(elaboration.clone());

        self.push_obligation(ClauseObligation::PollElaboration { universal });

        elaboration
    }

    pub(super) fn run_poll_elaboration(&mut self, universal: UniversalTy) -> ObligationResult {
        let mut is_done = true;

        // Attempt to finish whichever obligations we can.

        match is_done {
            true => Ok(ObligationTermination::Finished),
            false => Ok(ObligationTermination::CommitAndKeep),
        }
    }
}
