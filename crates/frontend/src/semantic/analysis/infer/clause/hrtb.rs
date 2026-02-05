//! Logic to instantiate an imported type with an HRTB binder around it.

use crate::{
    base::{Session, analysis::DebruijnTop, arena::HasListInterner},
    semantic::{
        analysis::{
            ClauseOrigin, ClauseOriginKind, ClauseCx, TyCtxt, TyFoldable, TyFolder,
            TyFolderInfallibleExt,
        },
        syntax::{
            HrtbBinder, HrtbBinderKind, Re, SpannedHrtbBinder, SpannedRe, SpannedTy, TraitClause,
            TraitSpec, Ty, TyKind, TyOrRe, TyOrReKind, TyOrReList, UniversalReVarSourceInfo,
            UniversalTyVarSourceInfo,
        },
    },
};
use std::convert::Infallible;

impl<'tcx> ClauseCx<'tcx> {
    pub fn instantiate_hrtb_universal(&mut self, binder: HrtbBinder<TraitSpec>) -> TraitSpec {
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
                TyOrReKind::Ty => {
                    TyOrRe::Ty(self.fresh_ty_universal(UniversalTyVarSourceInfo::HrtbVar))
                }
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
                TyOrReKind::Ty => TyOrRe::Ty(self.fresh_ty_infer()),
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
                            def: def.spawned_from,
                        }),
                        var,
                        clauses,
                    );
                }
                TyOrRe::Ty(var) => {
                    let clauses = HrtbSubstitutionFolder::new(self, vars, s).fold(def.clauses);

                    self.oblige_ty_meets_clauses(
                        &origin.clone().child(ClauseOriginKind::HrtbSelection {
                            def: def.spawned_from,
                        }),
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
