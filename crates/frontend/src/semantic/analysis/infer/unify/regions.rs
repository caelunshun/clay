use crate::{
    base::ErrorGuaranteed,
    semantic::{
        analysis::{CheckOrigin, ClauseCx, ReAndReUnifyError},
        syntax::{InferReVar, Re, RelationDirection, UniversalReVar, UniversalReVarSourceInfo},
    },
    utils::hash::FxHashSet,
};
use index_vec::IndexVec;
use smallvec::SmallVec;
use std::ops::ControlFlow;

// === ReUnifyTracker === //

#[derive(Debug, Clone)]
pub struct ReUnifyTracker {
    /// The next fresh inference variable to yield to the user.
    next_infer: InferReVar,

    /// A map from universal variable to the set of regions it's explicitly permitted to outlive or
    /// be outlived by.
    universals: IndexVec<UniversalReVar, ReUniversalState>,

    /// The set of user-generated constraints between regions. May contain duplicate constraints and
    /// redundant constraints like `'gc: 'other` or `'other: 'other`.
    constraints: Vec<ReConstraint>,
}

#[derive(Debug, Clone)]
struct ReUniversalState {
    src_info: UniversalReVarSourceInfo,

    /// Regions for which `'self: 'other`. May contain duplicates and redundant constraints like
    /// `'self: 'self`.
    allowed_outlive: Vec<InferRe>,

    /// Regions for which `'other: 'self`. May contain duplicates and redundant constraints like
    /// `'gc` and `'self`.
    allowed_outlived_by: Vec<InferRe>,
}

#[derive(Debug, Clone)]
struct ReConstraint {
    lhs: InferRe,
    rhs: InferRe,
    origin: CheckOrigin,
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
    pub fn fresh_universal(&mut self, src_info: UniversalReVarSourceInfo) -> UniversalReVar {
        self.universals.push(ReUniversalState {
            src_info,
            allowed_outlive: Vec::new(),
            allowed_outlived_by: Vec::new(),
        })
    }

    pub fn lookup_universal_src_info(&self, var: UniversalReVar) -> UniversalReVarSourceInfo {
        self.universals[var].src_info
    }

    pub fn fresh_infer(&mut self) -> InferReVar {
        let var = self.next_infer;
        self.next_infer += 1;
        var
    }

    pub fn constrain(&mut self, origin: CheckOrigin, lhs: Re, rhs: Re) {
        let (Ok(lhs), Ok(rhs)) = (InferRe::from_re(lhs), InferRe::from_re(rhs)) else {
            return;
        };

        self.constraints.push(ReConstraint { lhs, rhs, origin });
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

    pub fn verify(&self, ccx: &ClauseCx<'_>) {
        let permissions = ReElaboratedPermissions::new(self);
        let mut outlives = ReIncrementalOutlives::new(self);

        for cst in &self.constraints {
            outlives.add_constraint(cst.lhs, cst.rhs, |var, must_outlive| {
                if permissions.can_outlive(var, must_outlive) {
                    return Ok(());
                }

                Err(ReAndReUnifyError {
                    origin: cst.origin.clone(),
                    lhs: cst.lhs.to_re(),
                    rhs: cst.rhs.to_re(),
                    requires_var: var,
                    to_outlive: must_outlive.to_re(),
                }
                .emit(ccx))
            })
        }
    }
}

// === ReElaboratedPermissions === //

#[derive(Debug, Clone)]
struct ReElaboratedPermissions {
    /// Universal variables for which `'lhs: 'rhs`.
    ///
    /// Some caveats:
    ///
    /// - May or may not contain relations connected implicitly by a `'gc` (e.g. `'lhs: 'gc`, which
    ///   implies `'lhs: 'rhs` for all other `'rhs`).
    ///
    /// - May or may not contain redundant constraints like `'self: 'self`.
    ///
    permitted_uni_outlives: FxHashSet<(UniversalReVar, UniversalReVar)>,

    /// Universal variables for which `'lhs: 'gc`.
    permitted_gc_outlives: FxHashSet<UniversalReVar>,
}

impl ReElaboratedPermissions {
    fn new(tracker: &ReUnifyTracker) -> Self {
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

    fn can_outlive(&self, lhs: UniversalReVar, rhs: InferRe) -> bool {
        match rhs {
            InferRe::Gc => self.permitted_gc_outlives.contains(&lhs),
            InferRe::Universal(rhs) => {
                lhs == rhs
                    || self.permitted_uni_outlives.contains(&(lhs, rhs))
                    || self.permitted_gc_outlives.contains(&lhs)
            }
            InferRe::Infer(_) => unreachable!(),
        }
    }
}

// === ReIncrementalOutlives === //

#[derive(Debug, Clone)]
struct ReIncrementalOutlives {
    direct_outlive_graph: DirectedInferReGraph,
    transitive_universal_outlives: IndexVec<UniversalReVar, FxHashSet<InferRe>>,
    dfs_queue: Vec<InferRe>,
}

impl ReIncrementalOutlives {
    fn new(tracker: &ReUnifyTracker) -> Self {
        Self {
            direct_outlive_graph: DirectedInferReGraph::default(),
            transitive_universal_outlives: IndexVec::from_iter(
                tracker.universals.iter().map(|_| FxHashSet::default()),
            ),
            dfs_queue: Vec::new(),
        }
    }

    fn add_constraint(
        &mut self,
        lhs: InferRe,
        rhs: InferRe,
        mut check_outlive: impl FnMut(UniversalReVar, InferRe) -> Result<(), ErrorGuaranteed>,
    ) {
        self.direct_outlive_graph.add(lhs, rhs);

        for (var, var_outlives) in self.transitive_universal_outlives.iter_mut_enumerated() {
            if !(lhs == InferRe::Universal(var) || var_outlives.contains(&lhs)) {
                continue;
            }

            if !var_outlives.insert(rhs) {
                continue;
            }

            debug_assert!(self.dfs_queue.is_empty());

            self.dfs_queue.push(rhs);

            for stack_idx in 0.. {
                let Some(&top) = self.dfs_queue.get(stack_idx) else {
                    break;
                };

                match top {
                    InferRe::Gc | InferRe::Universal(_) => {
                        if check_outlive(var, top).is_err() {
                            for marked in &self.dfs_queue {
                                var_outlives.remove(marked);
                            }

                            break;
                        }
                    }
                    InferRe::Infer(_) => {
                        // (do not report)
                    }
                }

                for &succ in self.direct_outlive_graph.successors(top) {
                    if !var_outlives.insert(succ) {
                        continue;
                    }

                    self.dfs_queue.push(succ);
                }
            }

            self.dfs_queue.clear();
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
    fn from_re(re: Re) -> Result<InferRe, ErrorGuaranteed> {
        match re {
            Re::Gc => Ok(InferRe::Gc),
            Re::UniversalVar(var) => Ok(InferRe::Universal(var)),
            Re::InferVar(var) => Ok(InferRe::Infer(var)),
            Re::Error(err) => Err(err),
            Re::SigInfer | Re::SigGeneric(_) | Re::HrtbVar(_) | Re::Erased => unreachable!(),
        }
    }

    fn to_re(self) -> Re {
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
    fn get(&self, re: InferRe) -> Option<&T> {
        match re {
            InferRe::Gc => Some(&self.gc_maps_to),
            InferRe::Universal(var) => self.universal_maps_to.get(var),
            InferRe::Infer(var) => self.infer_maps_to.get(var),
        }
    }

    fn get_mut(&mut self, re: InferRe) -> &mut T {
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
    fn add(&mut self, lhs: InferRe, rhs: InferRe) {
        if !self.entries.insert((lhs, rhs)) {
            return;
        }

        self.outlives.add(lhs, rhs);
        self.outlived_by.add(rhs, lhs);
    }

    fn outlives(&self) -> &DirectedInferReGraph {
        &self.outlives
    }

    fn outlived_by(&self) -> &DirectedInferReGraph {
        &self.outlived_by
    }
}

#[derive(Debug, Clone, Default)]
struct DirectedInferReGraph(InferReMap<SmallVec<[InferRe; 1]>>);

impl DirectedInferReGraph {
    fn add(&mut self, lhs: InferRe, rhs: InferRe) {
        self.0.get_mut(lhs).push(rhs);
    }

    fn successors(&self, re: InferRe) -> &[InferRe] {
        self.0.get(re).map_or(&[][..], |v| v.as_slice())
    }
}

#[derive(Debug, Clone, Default)]
struct InferReDfs {
    visited: FxHashSet<InferRe>,
    stack: Vec<InferRe>,
}

impl InferReDfs {
    fn clear(&mut self) {
        self.visited.clear();
        self.stack.clear();
    }

    fn visit(&mut self, re: InferRe) {
        if self.visited.insert(re) {
            self.stack.push(re);
        }
    }

    fn visit_slice(&mut self, re: &[InferRe]) {
        for &re in re {
            self.visit(re);
        }
    }

    fn flush<B>(
        &mut self,
        mut f: impl FnMut((&mut Self, InferRe)) -> ControlFlow<B>,
    ) -> ControlFlow<B> {
        while let Some(top) = self.stack.pop() {
            f((self, top))?;
        }

        ControlFlow::Continue(())
    }
}
