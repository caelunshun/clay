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
    base::arena::{HasInterner, HasListInterner},
    semantic::{
        analysis::{
            ClauseCx, ClauseImportEnvRef, ClauseOrigin, ObligationResult, TyFolderInfallibleExt,
            UniversalElaboration,
        },
        syntax::{
            AnyGeneric, GenericSubst, HrtbBinder, InferTyVar, Re, TraitClause, TraitClauseList,
            TraitParam, TraitSpec, TyKind, TyOrRe, UniversalReVarSourceInfo, UniversalTyVar,
            UniversalTyVarSourceInfo,
        },
    },
    utils::hash::FxHashMap,
};
use std::rc::Rc;

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

    pub(super) fn oblige_unify_reified_elaborated_clauses(
        &mut self,
        clauses: TraitClauseList,
        reified_vars: Rc<FxHashMap<InferTyVar, TraitClauseList>>,
    ) -> ObligationResult {
        todo!()
    }
}
