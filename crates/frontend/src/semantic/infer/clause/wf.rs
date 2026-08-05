use crate::{
    base::{arena::Obj, syntax::Span},
    semantic::{
        infer::{
            ClauseCx, ClauseImportEnv, GenericSubst, HrtbUniverse, ObligeCause, ObligeCauseStep,
            SigImporterWfMode,
        },
        syntax::{AnyGeneric, GenericBinder, SigTraitClauseKind, TraitClause, TyOrRe, TyOrReList},
    },
};

impl<'tcx> ClauseCx<'tcx> {
    pub fn init_constraints_for_binder(
        &mut self,
        cause: &ObligeCause,
        universe: &HrtbUniverse,
        binder_parent_env: &ClauseImportEnv,
        target_binder: Obj<GenericBinder>,
        target_vars: TyOrReList,
    ) {
        let s = self.session();

        let binder_own_env = binder_parent_env
            .clone()
            .with_subst(GenericSubst::new(target_binder, target_vars));

        self.init_constraints_for_binder_raw(
            universe,
            &binder_own_env,
            &target_binder.r(s).defs,
            target_vars.r(s),
            |_ccx, _idx, clause| {
                cause
                    .clone()
                    .child(ObligeCauseStep::ImportEnvMeetsRequirements { clause }.into())
            },
        )
    }

    pub fn init_constraints_for_binder_raw(
        &mut self,
        universe: &HrtbUniverse,
        binder_own_env: &ClauseImportEnv,
        target_binder: &[AnyGeneric],
        target_vars: &[TyOrRe],
        mut gen_cause: impl FnMut(&mut ClauseCx<'tcx>, usize, Span) -> ObligeCause,
    ) {
        let s = self.session();

        for (i, (&generic, &var)) in target_binder.iter().zip(target_vars).enumerate() {
            match (generic, var) {
                (AnyGeneric::Re(generic), TyOrRe::Re(var)) => {
                    for &clause in generic.r(s).clauses.elems.r(s) {
                        let clause_span = clause.span;

                        let SigTraitClauseKind::Outlives(must_outlive_dir, must_outlive) =
                            clause.kind
                        else {
                            unreachable!()
                        };

                        let cause = gen_cause(self, i, clause_span);

                        let must_outlive = self
                            .importer(
                                cause.clone(),
                                universe.clone(),
                                binder_own_env.clone(),
                                // TODO: Can we really skip WF here?
                                SigImporterWfMode::Skip,
                            )
                            .import_ty_or_re(must_outlive);

                        self.oblige_general_outlives(
                            cause,
                            TyOrRe::Re(var),
                            must_outlive,
                            must_outlive_dir,
                        );
                    }
                }
                (AnyGeneric::Ty(generic), TyOrRe::Ty(var)) => {
                    for &clause in generic.r(s).clauses.elems.r(s) {
                        let cause = gen_cause(self, i, clause.span);

                        let clause = self
                            .importer(
                                cause.clone(),
                                universe.clone(),
                                binder_own_env.clone(),
                                // TODO: Can we really skip WF here?
                                SigImporterWfMode::Skip,
                            )
                            .import_clause_no_spec_wf(clause);

                        match clause {
                            TraitClause::Outlives(must_outlive_dir, must_outlive) => {
                                self.oblige_general_outlives(
                                    cause,
                                    TyOrRe::Ty(var),
                                    must_outlive,
                                    must_outlive_dir,
                                );
                            }
                            TraitClause::Trait(rhs) => {
                                self.oblige_ty_meets_trait(cause, universe.clone(), var, rhs);
                            }
                        }
                    }
                }
                _ => unreachable!(),
            }
        }
    }
}
