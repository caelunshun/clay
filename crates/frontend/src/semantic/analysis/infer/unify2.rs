use crate::{
    base::ErrorGuaranteed,
    semantic::syntax::{InferReVar, Re, RelationDirection, UniversalReVar},
    utils::hash::FxHashSet,
};
use index_vec::IndexVec;
use smallvec::SmallVec;
use std::ops::ControlFlow;

// === ReUnifyTracker === //

#[derive(Debug, Clone)]
pub struct ReUnifyTracker {
    next_infer: InferReVar,
    universals: IndexVec<UniversalReVar, ReUniversalState>,
    constraints: Vec<ReConstraint>,
}

#[derive(Debug, Clone, Default)]
struct ReUniversalState {
    allowed_outlive: Vec<InferRe>,
    allowed_outlived_by: Vec<InferRe>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
struct ReConstraint {
    lhs: InferRe,
    rhs: InferRe,
    origin: (),
}

impl Default for ReUnifyTracker {
    fn default() -> Self {
        Self {
            next_infer: InferReVar::from_raw(0),
            universals: IndexVec::new(),
            constraints: Vec::new(),
        }
    }
}

impl ReUnifyTracker {
    pub fn fresh_universal(&mut self) -> UniversalReVar {
        self.universals.push(ReUniversalState::default())
    }

    pub fn fresh_infer(&mut self) -> InferReVar {
        let var = self.next_infer;
        self.next_infer += 1;
        var
    }

    pub fn relate(&mut self, lhs: Re, rhs: Re) {
        let (Ok(lhs), Ok(rhs)) = (InferRe::from_re(lhs), InferRe::from_re(rhs)) else {
            return;
        };

        self.constraints.push(ReConstraint {
            lhs,
            rhs,
            origin: (),
        });
    }

    pub fn permit(&mut self, universal: UniversalReVar, other: Re, dir: RelationDirection) {
        let Ok(other) = InferRe::from_re(other) else {
            return;
        };

        match dir {
            RelationDirection::LhsOntoRhs => {
                self.universals[universal].allowed_outlive.push(other);
            }
            RelationDirection::RhsOntoLhs => {
                self.universals[universal].allowed_outlived_by.push(other);
            }
        }
    }

    pub fn verify(&self) {
        let permissions = ReElaboratedPermissions::compute(self);

        todo!()
    }
}

// === ReElaboratedPermissions === //

#[derive(Debug, Clone)]
struct ReElaboratedPermissions {
    /// Universal variables for which `'lhs: 'rhs`.
    permitted_uni_outlives: FxHashSet<(UniversalReVar, UniversalReVar)>,

    /// Universal variables for which `'lhs: 'gc`.
    permitted_gc_outlives: FxHashSet<UniversalReVar>,
}

impl ReElaboratedPermissions {
    fn compute(tracker: &ReUnifyTracker) -> Self {
        // Convert constraints and permissions into a graph.
        let mut graph = InferReGraph::default();

        for cst in &tracker.constraints {
            graph.add(cst.lhs, cst.rhs);
        }

        for (var, state) in tracker.universals.iter_enumerated() {
            for &outlives in &state.allowed_outlive {
                graph.add(InferRe::Universal(var), outlives);
            }

            for &outlived_by in &state.allowed_outlived_by {
                graph.add(outlived_by, InferRe::Universal(var));
            }
        }

        // DFS each universal's permission set to figure out which universals they are allowed to
        // outlive.
        let mut permitted_uni_outlives = FxHashSet::default();
        let mut permitted_gc_outlives = FxHashSet::default();

        let mut dfs = InferReDfs::default();

        for (var, state) in tracker.universals.iter_enumerated() {
            // Find regions for which `'var: 'other` is permitted.

            // Allow `dfs` to get saturated within the `allowed_outlive` loop since we only ever
            // need to see a given DFS target once.
            dfs.clear();

            for &root in &state.allowed_outlive {
                dfs.visit(root);

                cbit::cbit!(for (dfs, other) in dfs.flush() {
                    match other {
                        InferRe::Gc => {
                            permitted_gc_outlives.insert(var);
                        }
                        InferRe::Universal(other) => {
                            permitted_uni_outlives.insert((var, other));
                        }
                        InferRe::Infer(_) => {
                            // (nothing to register)
                        }
                    }

                    dfs.visit_slice(graph.outlives().successors(other));
                });
            }

            // Find regions for which `'other: 'var` is permitted.
            dfs.clear();

            for &root in &state.allowed_outlived_by {
                dfs.visit(root);

                cbit::cbit!(for (dfs, other) in dfs.flush() {
                    match other {
                        InferRe::Gc => {
                            // (implicit, no need to register)
                        }
                        InferRe::Universal(other) => {
                            permitted_uni_outlives.insert((other, var));
                        }
                        InferRe::Infer(_) => {
                            // (nothing to register)
                        }
                    }

                    dfs.visit_slice(graph.outlived_by().successors(other));
                });
            }
        }

        Self {
            permitted_uni_outlives,
            permitted_gc_outlives,
        }
    }

    fn can_outlive(&self, lhs: InferRe, rhs: InferRe) -> bool {
        match (lhs, rhs) {
            (InferRe::Gc, _) => true,
            (InferRe::Universal(lhs), InferRe::Gc) => self.permitted_gc_outlives.contains(&lhs),
            (InferRe::Universal(lhs), InferRe::Universal(rhs)) => {
                lhs == rhs
                    || self.permitted_uni_outlives.contains(&(lhs, rhs))
                    || self.permitted_gc_outlives.contains(&lhs)
            }
            (InferRe::Infer(_), _) | (_, InferRe::Infer(_)) => unreachable!(),
        }
    }
}

// === InferRe === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
enum InferRe {
    Gc,
    Universal(UniversalReVar),
    Infer(InferReVar),
}

impl InferRe {
    pub fn from_re(re: Re) -> Result<InferRe, ErrorGuaranteed> {
        match re {
            Re::Gc => Ok(InferRe::Gc),
            Re::UniversalVar(var) => Ok(InferRe::Universal(var)),
            Re::InferVar(var) => Ok(InferRe::Infer(var)),
            Re::Error(err) => Err(err),
            Re::SigInfer | Re::SigGeneric(_) | Re::HrtbVar(_) | Re::Erased => unreachable!(),
        }
    }

    pub fn to_re(self) -> Re {
        match self {
            InferRe::Gc => Re::Gc,
            InferRe::Universal(var) => Re::UniversalVar(var),
            InferRe::Infer(var) => Re::InferVar(var),
        }
    }
}

// === InferReMap === //

#[derive(Debug, Clone, Default)]
struct InferReMap<T> {
    gc_maps_to: T,
    universal_maps_to: IndexVec<UniversalReVar, T>,
    infer_maps_to: IndexVec<InferReVar, T>,
}

impl<T: Default> InferReMap<T> {
    pub fn get(&self, re: InferRe) -> Option<&T> {
        match re {
            InferRe::Gc => Some(&self.gc_maps_to),
            InferRe::Universal(var) => self.universal_maps_to.get(var),
            InferRe::Infer(var) => self.infer_maps_to.get(var),
        }
    }

    pub fn get_mut(&mut self, re: InferRe) -> &mut T {
        fn get_entry<I: index_vec::Idx, T: Default>(target: &mut IndexVec<I, T>, idx: I) -> &mut T {
            let min_len = idx.index() + 1;

            if target.len() < min_len {
                target.resize_with(min_len, T::default);
            }

            &mut target[idx]
        }

        match re {
            InferRe::Gc => &mut self.gc_maps_to,
            InferRe::Universal(var) => get_entry(&mut self.universal_maps_to, var),
            InferRe::Infer(var) => get_entry(&mut self.infer_maps_to, var),
        }
    }
}

// === InferReGraph === //

#[derive(Debug, Clone, Default)]
struct InferReGraph {
    outlives: DirectedInferReGraph,
    outlived_by: DirectedInferReGraph,
    entries: FxHashSet<(InferRe, InferRe)>,
}

impl InferReGraph {
    pub fn add(&mut self, lhs: InferRe, rhs: InferRe) {
        if !self.entries.insert((lhs, rhs)) {
            return;
        }

        self.outlives.add(lhs, rhs);
        self.outlived_by.add(rhs, lhs);
    }

    pub fn outlives(&self) -> &DirectedInferReGraph {
        &self.outlives
    }

    pub fn outlived_by(&self) -> &DirectedInferReGraph {
        &self.outlived_by
    }
}

#[derive(Debug, Clone, Default)]
struct DirectedInferReGraph(InferReMap<SmallVec<[InferRe; 1]>>);

impl DirectedInferReGraph {
    pub fn add(&mut self, lhs: InferRe, rhs: InferRe) {
        self.0.get_mut(lhs).push(rhs);
    }

    pub fn successors(&self, re: InferRe) -> &[InferRe] {
        self.0.get(re).map_or(&[][..], |v| v.as_slice())
    }
}

#[derive(Debug, Clone, Default)]
struct InferReDfs {
    visited: FxHashSet<InferRe>,
    stack: Vec<InferRe>,
}

impl InferReDfs {
    pub fn clear(&mut self) {
        self.visited.clear();
        self.stack.clear();
    }

    pub fn visit(&mut self, re: InferRe) {
        if self.visited.insert(re) {
            self.stack.push(re);
        }
    }

    pub fn visit_slice(&mut self, re: &[InferRe]) {
        for &re in re {
            self.visit(re);
        }
    }

    pub fn flush<B>(
        &mut self,
        mut f: impl FnMut((&mut Self, InferRe)) -> ControlFlow<B>,
    ) -> ControlFlow<B> {
        debug_assert!(self.stack.is_empty());

        while let Some(top) = self.stack.pop() {
            f((self, top))?;
        }

        ControlFlow::Continue(())
    }
}
