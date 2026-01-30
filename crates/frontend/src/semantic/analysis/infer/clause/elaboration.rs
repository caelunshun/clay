//! Logic to elaborate a trait clause list.

use crate::{
    base::arena::HasListInterner,
    semantic::{
        analysis::{ClauseCx, UniversalElaboration},
        syntax::{Re, TraitClause, TraitClauseList, UniversalReVarSourceInfo, UniversalTyVar},
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

        for &target in target.r(s) {
            match target {
                TraitClause::Outlives(outlive_dir, outlive) => {
                    self.permit_universe_re_outlives_general(lub_re, outlive, outlive_dir);
                    accum.push(TraitClause::Outlives(outlive_dir, outlive));
                }
                TraitClause::Trait(spec) => {
                    // // Elaborate with filled in parameters.
                    // let new_params = spec
                    //     .params
                    //     .r(s)
                    //     .iter()
                    //     .zip(&spec.def.r(s).generics.r(s).defs)
                    //     .enumerate()
                    //     .map(|(idx, (param, base))| match *param {
                    //         TraitParam::Equals(ty) => TraitParam::Equals(ty),
                    //         TraitParam::Unspecified(extra_clauses) => {
                    //             let universal = self.fresh_ty_universal_var(
                    //                 UniversalTyVarSourceInfo::Projection(root, spec, idx as u32),
                    //             );
                    //             let base = *base.as_ty().unwrap().r(s).clauses;
                    //
                    //             self.importer(self_ty, sig_generic_substs);
                    //
                    //             todo!()
                    //         }
                    //     });
                    //
                    // // Elaborate super-traits.
                    // // TODO

                    accum.push(TraitClause::Trait(spec));
                }
            }
        }
    }
}
