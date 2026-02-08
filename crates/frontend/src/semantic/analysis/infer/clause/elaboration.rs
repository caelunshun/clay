//! Logic to elaborate a trait clause list.

use crate::{
    base::arena::{HasInterner, HasListInterner},
    semantic::{
        analysis::{ClauseCx, ClauseImportEnvRef, TyFolderInfallibleExt, UniversalElaboration},
        syntax::{
            AnyGeneric, GenericSubst, HrtbBinder, Re, TraitClause, TraitClauseList, TraitParam,
            TraitSpec, TyKind, TyOrRe, UniversalReVarSourceInfo, UniversalTyVar,
            UniversalTyVarSourceInfo,
        },
    },
};

impl<'tcx> ClauseCx<'tcx> {
    pub fn elaborate_ty_universal_clauses(&mut self, var: UniversalTyVar) -> UniversalElaboration {
        // See whether this universal variable has been elaborated yet.
        if let Some(elaborated) = self.universal_vars[var].elaboration {
            return elaborated;
        }

        // If not, accumulate a collection of clauses.
        let mut elaborated = Vec::new();

        let lub_re = self.fresh_re_universal(UniversalReVarSourceInfo::ElaboratedLub);

        self.elaborate_clause_and_implied(
            var,
            lub_re,
            &mut elaborated,
            self.direct_ty_universal_clauses(var),
        );

        let elaborated = UniversalElaboration {
            clauses: self.tcx().intern_list(&elaborated),
            lub_re,
        };
        self.universal_vars[var].elaboration = Some(elaborated);
        elaborated
    }

    fn elaborate_clause_and_implied(
        &mut self,
        root: UniversalTyVar,
        lub_re: Re,
        accum: &mut Vec<TraitClause>,
        target: TraitClauseList,
    ) {
        let s = self.session();
        let tcx = self.tcx();

        for &target in target.r(s) {
            match target {
                TraitClause::Outlives(outlive_dir, outlive) => {
                    self.permit_universe_re_outlives_general(lub_re, outlive, outlive_dir);
                    accum.push(TraitClause::Outlives(outlive_dir, outlive));
                }
                TraitClause::Trait(HrtbBinder { kind, inner: spec }) => {
                    // Elaborate with filled in parameters.
                    let new_params = spec
                        .params
                        .r(s)
                        .iter()
                        .enumerate()
                        .map(|(idx, param)| match *param {
                            TraitParam::Equals(ty_or_re) => ty_or_re,
                            TraitParam::Unspecified(_) => TyOrRe::Ty(self.fresh_ty_universal(
                                UniversalTyVarSourceInfo::Projection(root, spec, idx as u32),
                                // Associated types vary in the same way as their parent generic.
                                self.lookup_universal_ty_hrtb_universe(root).clone(),
                            )),
                        })
                        .collect::<Vec<_>>();

                    let new_params = tcx.intern_list(&new_params);

                    for ((new_param, base), spec_param) in new_params
                        .r(s)
                        .iter()
                        .zip(&spec.def.r(s).generics.r(s).defs)
                        .zip(spec.params.r(s).iter())
                    {
                        let TraitParam::Unspecified(explicit_clauses) = *spec_param else {
                            continue;
                        };

                        let (TyOrRe::Ty(new_param), AnyGeneric::Ty(base)) = (new_param, base)
                        else {
                            unreachable!()
                        };

                        let TyKind::UniversalVar(new_param) = *new_param.r(s) else {
                            unreachable!()
                        };

                        let implicit_clauses = self
                            .importer(
                                ClauseImportEnvRef {
                                    self_ty: tcx.intern(TyKind::UniversalVar(root)),
                                    sig_generic_substs: &[GenericSubst {
                                        binder: *spec.def.r(s).generics,
                                        substs: new_params,
                                    }],
                                },
                                // Associated types vary in the same way as their parent generic.
                                self.lookup_universal_ty_hrtb_universe(root).clone(),
                            )
                            .fold(base.r(s).clauses.value);

                        let all_clauses = explicit_clauses
                            .r(s)
                            .iter()
                            .chain(implicit_clauses.r(s))
                            .copied()
                            .collect::<Vec<_>>();

                        let all_clauses = tcx.intern_list(&all_clauses);

                        self.init_ty_universal_var_direct_clauses(new_param, all_clauses);
                    }

                    let new_params = new_params
                        .r(s)
                        .iter()
                        .map(|&ty_or_re| TraitParam::Equals(ty_or_re))
                        .collect::<Vec<_>>();

                    let new_params = tcx.intern_list(&new_params);

                    accum.push(TraitClause::Trait(HrtbBinder {
                        kind,
                        inner: TraitSpec {
                            def: spec.def,
                            params: new_params,
                        },
                    }));

                    // Elaborate super-traits.
                    // TODO
                }
            }
        }
    }
}
