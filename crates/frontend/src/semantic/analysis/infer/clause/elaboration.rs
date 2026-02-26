//! Logic to elaborate a trait clause list.

use crate::{
    base::arena::{HasInterner, HasListInterner},
    semantic::{
        analysis::{
            ClauseCx, ClauseImportEnvRef, ClauseOrigin, TyFolderInfallibleExt, UniversalElaboration,
        },
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

        self.elaborate_clause_list(
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

    fn elaborate_clause_list(
        &mut self,
        root: UniversalTyVar,
        lub_re: Re,
        accum: &mut Vec<TraitClause>,
        target: TraitClauseList,
    ) {
        let s = self.session();

        for &target in target.r(s) {
            self.elaborate_any_clause(root, lub_re, accum, target);
        }
    }

    fn elaborate_any_clause(
        &mut self,
        root: UniversalTyVar,
        lub_re: Re,
        accum: &mut Vec<TraitClause>,
        target: TraitClause,
    ) {
        match target {
            TraitClause::Outlives(outlive_dir, outlive) => {
                self.permit_universe_re_outlives_general(lub_re, outlive, outlive_dir);
                accum.push(TraitClause::Outlives(outlive_dir, outlive));
            }
            TraitClause::Trait(spec) => self.elaborate_impl_clause(root, lub_re, accum, spec),
        }
    }

    fn elaborate_impl_clause(
        &mut self,
        root: UniversalTyVar,
        lub_re: Re,
        accum: &mut Vec<TraitClause>,
        target: HrtbBinder<TraitSpec>,
    ) {
        let s = self.session();
        let tcx = self.tcx();

        let HrtbBinder { kind, inner: spec } = target;

        // Replace unspecified parameters with fresh universals.
        let new_param_equals = spec
            .params
            .r(s)
            .iter()
            .enumerate()
            .map(|(idx, param)| match *param {
                TraitParam::Equals(ty_or_re) => ty_or_re,
                TraitParam::Unspecified(_) => TyOrRe::Ty(self.fresh_ty_universal(
                    // Associated types vary in the same way as their parent generic.
                    self.lookup_universal_ty_hrtb_universe(root).clone(),
                    UniversalTyVarSourceInfo::Projection(root, spec, idx as u32),
                )),
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

            let (TyOrRe::Ty(new_param), AnyGeneric::Ty(base)) = (new_param, base) else {
                unreachable!()
            };

            let TyKind::UniversalVar(new_param) = *new_param.r(s) else {
                unreachable!()
            };

            let implicit_clauses = self
                .importer(
                    &ClauseOrigin::empty_report(),
                    // Associated types vary in the same way as their parent generic.
                    self.lookup_universal_ty_hrtb_universe(root).clone(),
                    ClauseImportEnvRef {
                        self_ty: tcx.intern(TyKind::UniversalVar(root)),
                        sig_generic_substs: &[GenericSubst {
                            binder: *spec.def.r(s).generics,
                            substs: new_param_equals,
                        }],
                    },
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

        // Push on the elaborated trait `impl` constraint.
        let new_params = new_param_equals
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

        // Explore and push on the elaborated super-trait constraints.
        let inherits = self
            .importer(
                &ClauseOrigin::empty_report(),
                // Associated types vary in the same way as their parent generic.
                self.lookup_universal_ty_hrtb_universe(root).clone(),
                ClauseImportEnvRef {
                    self_ty: tcx.intern(TyKind::UniversalVar(root)),
                    sig_generic_substs: &[GenericSubst {
                        binder: *spec.def.r(s).generics,
                        substs: new_param_equals,
                    }],
                },
            )
            .fold_spanned(*spec.def.r(s).inherits);

        self.elaborate_clause_list(root, lub_re, accum, inherits);
    }
}
