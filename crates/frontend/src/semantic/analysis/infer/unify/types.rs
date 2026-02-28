use crate::{
    semantic::{
        analysis::{FloatingInferVar, HrtbUniverse, TyCtxt},
        syntax::{InferTyVar, SimpleTySet, Ty, UniversalTyVar, UniversalTyVarSourceInfo},
    },
    utils::hash::FxHashSet,
};
use disjoint::DisjointSetVec;
use index_vec::IndexVec;
use std::cell::RefCell;

#[derive(Debug, Clone)]
pub struct TyUnifyTracker {
    disjoint: DisjointSetVec<DisjointTyInferNode>,
    universals: IndexVec<UniversalTyVar, UniversalTyVarDescriptor>,
}

#[derive(Debug, Clone)]
struct DisjointTyInferNode {
    root: Option<DisjointTyInferRoot>,
}

#[derive(Debug, Clone)]
enum DisjointTyInferRoot {
    Known(Ty),
    Floating {
        max_universe: HrtbUniverse,
        perm_set: SimpleTySet,
    },
}

#[derive(Debug, Clone)]
struct UniversalTyVarDescriptor {
    in_universe: HrtbUniverse,
    src_info: UniversalTyVarSourceInfo,
}

#[derive(Debug)]
struct TyInferTracingState {
    set: RefCell<FxHashSet<InferTyVar>>,
    var_count: InferTyVar,
}

impl Default for TyUnifyTracker {
    fn default() -> Self {
        Self {
            disjoint: DisjointSetVec::new(),
            universals: IndexVec::new(),
        }
    }
}

impl TyUnifyTracker {
    pub fn fresh_infer_restricted(
        &mut self,
        max_universe: HrtbUniverse,
        perm_set: SimpleTySet,
    ) -> InferTyVar {
        let var = InferTyVar::from_usize(self.disjoint.len());
        self.disjoint.push(DisjointTyInferNode {
            root: Some(DisjointTyInferRoot::Floating {
                max_universe: max_universe.clone(),
                perm_set,
            }),
        });
        var
    }

    pub fn fresh_universal(
        &mut self,
        in_universe: HrtbUniverse,
        src_info: UniversalTyVarSourceInfo,
    ) -> UniversalTyVar {
        self.universals.push(UniversalTyVarDescriptor {
            in_universe,
            src_info,
        })
    }

    pub fn lookup_universal_src_info(&self, var: UniversalTyVar) -> UniversalTyVarSourceInfo {
        self.universals[var].src_info
    }

    pub fn lookup_universal_hrtb_universe(&self, var: UniversalTyVar) -> &HrtbUniverse {
        &self.universals[var].in_universe
    }

    pub fn lookup_infer(&self, var: InferTyVar) -> Result<Ty, FloatingInferVar<'_>> {
        let root_var = self.disjoint.root_of(var.index());

        match self.disjoint[root_var].root.as_ref().unwrap() {
            &DisjointTyInferRoot::Known(ty) => Ok(ty),
            DisjointTyInferRoot::Floating {
                perm_set,
                max_universe,
            } => Err(FloatingInferVar {
                root: InferTyVar::from_usize(root_var),
                max_universe,
                perm_set: *perm_set,
            }),
        }
    }

    pub fn force_update_permissions_of_ty_var(&mut self, var: InferTyVar, perms: SimpleTySet) {
        let root_var = self.disjoint.root_of(var.index());

        let DisjointTyInferRoot::Floating {
            perm_set,
            max_universe: _,
        } = self.disjoint[root_var].root.as_mut().unwrap()
        else {
            unreachable!()
        };

        *perm_set = perms;
    }

    pub fn restrict_floating_infer_max_universe(&mut self, var: InferTyVar, other: &HrtbUniverse) {
        let root_var = self.disjoint.root_of(var.index());

        let DisjointTyInferRoot::Floating {
            perm_set: _,
            max_universe,
        } = self.disjoint[root_var].root.as_mut().unwrap()
        else {
            unreachable!()
        };

        *max_universe = max_universe.min(other).clone();
    }

    pub fn assign_floating_infer_to_non_var(&mut self, var: InferTyVar, ty: Ty) {
        let root_idx = self.disjoint.root_of(var.index());
        let root = self.disjoint[root_idx].root.as_mut().unwrap();

        let DisjointTyInferRoot::Floating {
            max_universe: _,
            perm_set: _,
        } = root
        else {
            unreachable!();
        };

        *root = DisjointTyInferRoot::Known(ty);
    }

    pub fn union_unrelated_infer_floating(
        &mut self,
        tcx: &TyCtxt,
        lhs: InferTyVar,
        rhs: InferTyVar,
    ) {
        let lhs_root = self.disjoint.root_of(lhs.index());
        let rhs_root = self.disjoint.root_of(rhs.index());

        if lhs_root == rhs_root {
            return;
        }

        let lhs_root = self.disjoint[lhs_root].root.take().unwrap();
        let rhs_root = self.disjoint[rhs_root].root.take().unwrap();

        let (
            DisjointTyInferRoot::Floating {
                max_universe: lhs_max_universe,
                perm_set: lhs_perm_set,
            },
            DisjointTyInferRoot::Floating {
                max_universe: rhs_max_universe,
                perm_set: rhs_perm_set,
            },
        ) = (lhs_root, rhs_root)
        else {
            unreachable!()
        };

        self.disjoint.join(lhs.index(), rhs.index());

        let new_root = self.disjoint.root_of(lhs.index());
        let new_root = &mut self.disjoint[new_root].root;

        debug_assert!(new_root.is_none());

        let perm_set = lhs_perm_set.intersection(rhs_perm_set);
        debug_assert!(!perm_set.is_empty());

        if let Some(unique_ty) = perm_set.to_unique_type(tcx) {
            *new_root = Some(DisjointTyInferRoot::Known(unique_ty));
        } else {
            *new_root = Some(DisjointTyInferRoot::Floating {
                max_universe: lhs_max_universe.min(&rhs_max_universe).clone(),
                perm_set,
            });
        }
    }

    pub fn restrict_perm_set_of_floating(
        &mut self,
        tcx: &TyCtxt,
        lhs: InferTyVar,
        rhs: SimpleTySet,
    ) {
        let lhs_root = self.disjoint.root_of(lhs.index());

        let Some(DisjointTyInferRoot::Floating { perm_set, .. }) =
            &mut self.disjoint[lhs_root].root
        else {
            unreachable!()
        };

        let new_perm_set = perm_set.intersection(rhs);
        debug_assert!(!new_perm_set.is_empty());

        if let Some(unique_ty) = new_perm_set.to_unique_type(tcx) {
            self.disjoint[lhs_root].root = Some(DisjointTyInferRoot::Known(unique_ty));
        } else {
            *perm_set = new_perm_set;
        }
    }
}
