use crate::{
    semantic::{
        analysis::{FloatingInferVar, ObservedTyInferVar},
        syntax::{HrtbUniverse, InferTyVar, Ty},
    },
    utils::hash::FxHashSet,
};
use disjoint::DisjointSetVec;
use std::{cell::RefCell, rc::Rc};

#[derive(Debug, Clone)]
pub struct TyUnifyTracker {
    disjoint: DisjointSetVec<DisjointTyInferNode>,
    observed_reveal_order: Vec<ObservedTyInferVar>,
    next_observe_idx: ObservedTyInferVar,
    tracing_state: Option<Rc<TyInferTracingState>>,
}

#[derive(Debug, Clone)]
struct DisjointTyInferNode {
    root: Option<DisjointTyInferRoot>,
    observed_idx: Option<ObservedTyInferVar>,
}

#[derive(Debug, Clone)]
enum DisjointTyInferRoot {
    Known(Ty),
    Floating {
        observed: Vec<ObservedTyInferVar>,
        max_universe: HrtbUniverse,
    },
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
            observed_reveal_order: Vec::new(),
            next_observe_idx: ObservedTyInferVar::from_usize(0),
            tracing_state: None,
        }
    }
}

impl TyUnifyTracker {
    pub fn start_tracing(&mut self) {
        debug_assert!(self.tracing_state.is_none());

        self.tracing_state = Some(Rc::new(TyInferTracingState {
            set: RefCell::default(),
            var_count: InferTyVar::from_usize(self.disjoint.len()),
        }))
    }

    pub fn finish_tracing(&mut self) -> FxHashSet<InferTyVar> {
        let set = self.tracing_state.take().expect("not tracing");
        let set = Rc::into_inner(set)
            .expect("derived inference contexts remain using the same tracing state");

        set.set.into_inner()
    }

    pub fn mention_var_for_tracing(&self, var: InferTyVar) {
        let Some(state) = &self.tracing_state else {
            return;
        };

        if var >= state.var_count {
            return;
        }

        state.set.borrow_mut().insert(var);
    }

    pub fn fresh(&mut self, max_universe: HrtbUniverse) -> InferTyVar {
        let var = InferTyVar::from_usize(self.disjoint.len());
        self.disjoint.push(DisjointTyInferNode {
            root: Some(DisjointTyInferRoot::Floating {
                observed: Vec::new(),
                max_universe: max_universe.clone(),
            }),
            observed_idx: None,
        });
        var
    }

    pub fn observe(&mut self, var: InferTyVar) -> ObservedTyInferVar {
        let observed_idx = &mut self.disjoint[var.index()].observed_idx;

        if let Some(observed_idx) = *observed_idx {
            return observed_idx;
        }

        let observed_idx = *observed_idx.insert(self.next_observe_idx);
        self.next_observe_idx += 1;

        let root_var = self.disjoint.root_of(var.index());

        match self.disjoint[root_var].root.as_mut().unwrap() {
            DisjointTyInferRoot::Known(_) => {
                self.observed_reveal_order.push(observed_idx);
            }
            DisjointTyInferRoot::Floating {
                observed,
                max_universe: _,
            } => {
                observed.push(observed_idx);
            }
        }

        observed_idx
    }

    pub fn observed_reveal_order(&self) -> &[ObservedTyInferVar] {
        &self.observed_reveal_order
    }

    pub fn constrain_max_universe(&mut self, var: InferTyVar, other: &HrtbUniverse) {
        let root_var = self.disjoint.root_of(var.index());

        if let DisjointTyInferRoot::Floating {
            observed: _,
            max_universe,
        } = self.disjoint[root_var].root.as_mut().unwrap()
        {
            *max_universe = max_universe.min(other).clone();
        }
    }

    pub fn lookup(&self, var: InferTyVar) -> Result<Ty, FloatingInferVar<'_>> {
        let root_var = self.disjoint.root_of(var.index());

        match self.disjoint[root_var].root.as_ref().unwrap() {
            &DisjointTyInferRoot::Known(ty) => Ok(ty),
            DisjointTyInferRoot::Floating {
                observed: observed_equivalent,
                max_universe,
            } => {
                self.mention_var_for_tracing(var);

                Err(FloatingInferVar {
                    root: InferTyVar::from_usize(root_var),
                    observed_equivalent,
                    max_universe,
                })
            }
        }
    }

    pub fn assign_floating_to_non_var(&mut self, var: InferTyVar, ty: Ty) {
        let root_idx = self.disjoint.root_of(var.index());
        let root = self.disjoint[root_idx].root.as_mut().unwrap();

        let DisjointTyInferRoot::Floating {
            observed,
            max_universe: _,
        } = root
        else {
            unreachable!();
        };

        self.observed_reveal_order.extend_from_slice(observed);
        *root = DisjointTyInferRoot::Known(ty);
    }

    pub fn union_unrelated_floating(&mut self, lhs: InferTyVar, rhs: InferTyVar) {
        let lhs_root = self.disjoint.root_of(lhs.index());
        let rhs_root = self.disjoint.root_of(rhs.index());

        if lhs_root == rhs_root {
            return;
        }

        let lhs_root = self.disjoint[lhs_root].root.take().unwrap();
        let rhs_root = self.disjoint[rhs_root].root.take().unwrap();

        let (
            DisjointTyInferRoot::Floating {
                observed: mut lhs_observed,
                max_universe: lhs_max_universe,
            },
            DisjointTyInferRoot::Floating {
                observed: mut rhs_observed,
                max_universe: rhs_max_universe,
            },
        ) = (lhs_root, rhs_root)
        else {
            unreachable!()
        };

        self.disjoint.join(lhs.index(), rhs.index());

        let new_root = self.disjoint.root_of(lhs.index());
        let new_root = &mut self.disjoint[new_root].root;

        debug_assert!(new_root.is_none());

        lhs_observed.append(&mut rhs_observed);

        *new_root = Some(DisjointTyInferRoot::Floating {
            observed: lhs_observed,
            max_universe: lhs_max_universe.min(&rhs_max_universe).clone(),
        });
    }
}
