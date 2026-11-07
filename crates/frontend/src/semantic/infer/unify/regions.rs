use crate::{
    base::ErrorGuaranteed,
    flags,
    semantic::{
        infer::{
            ClauseCx, ClausePrettyFmtOpts, Promise, PromiseHandle, ReAndReUnifyErrorCause,
            ReConstraintOrder, UnifyCxMode,
        },
        syntax::{InferReVar, Re, RelationDirection, UniversalReVar, UniversalReVarSourceInfo},
    },
};
use clay_core::FastHashSet;
use index_vec::IndexVec;
use petgraph::{dot::Dot, graph::NodeIndex};
use smallvec::SmallVec;
use std::{fmt, ops::ControlFlow};

// === ReUnifyTracker === //

#[derive(Debug, Clone)]
pub struct ReUnifyTracker<'sess> {
    non_blind_state: Option<NonBlindState<'sess>>,

    /// A map from universal variable to the set of regions it's explicitly permitted to outlive or
    /// be outlived by.
    universals: IndexVec<UniversalReVar, ReUniversalState>,
}

#[derive(Debug, Clone)]
struct NonBlindState<'sess> {
    /// The next fresh inference variable to yield to the user.
    next_infer: InferReVar,

    /// The set of user-generated constraints between regions. May contain duplicate constraints and
    /// redundant constraints like `'gc: 'other` or `'other: 'other`.
    constraints: Vec<ReConstraint<'sess>>,
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
struct ReConstraint<'sess> {
    handle: PromiseHandle<'sess, ReAndReUnifyErrorCause>,
    lhs: InferRe,
    rhs: InferRe,
    order: ReConstraintOrder,
}

impl<'sess> ReUnifyTracker<'sess> {
    pub fn new(mode: UnifyCxMode) -> Self {
        Self {
            non_blind_state: match mode {
                UnifyCxMode::RegionAware => Some(NonBlindState {
                    next_infer: InferReVar::from_raw(0),
                    constraints: Vec::new(),
                }),
                UnifyCxMode::RegionBlind => None,
            },
            universals: IndexVec::new(),
        }
    }

    pub fn mode(&self) -> UnifyCxMode {
        match self.non_blind_state.is_some() {
            true => UnifyCxMode::RegionAware,
            false => UnifyCxMode::RegionBlind,
        }
    }

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
        let Some(non_blind_state) = &mut self.non_blind_state else {
            return InferReVar::ERASED;
        };

        let var = non_blind_state.next_infer;
        non_blind_state.next_infer += 1;
        var
    }

    pub fn constrain(
        &mut self,
        order: ReConstraintOrder,
        lhs: Re,
        rhs: Re,
    ) -> Promise<'sess, ReAndReUnifyErrorCause> {
        let Some(non_blind_state) = &mut self.non_blind_state else {
            return Promise::trivial();
        };

        let (Ok(lhs), Ok(rhs)) = (InferRe::from_re(lhs), InferRe::from_re(rhs)) else {
            return Promise::trivial();
        };

        let (promise, handle) = Promise::new();

        non_blind_state.constraints.push(ReConstraint {
            handle,
            lhs,
            rhs,
            order,
        });

        promise
    }

    pub fn permit(&mut self, universal: UniversalReVar, other: Re, dir: RelationDirection) {
        if self.non_blind_state.is_none() {
            return;
        }

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

    pub fn verify(ccx: &mut ClauseCx<'sess>) {
        fn get_this<'a, 'sess>(ccx: &'a mut ClauseCx<'sess>) -> &'a mut ReUnifyTracker<'sess> {
            &mut ccx.ucx_mut().regions
        }

        let this = get_this(ccx);

        if this.non_blind_state.is_none() {
            return;
        }

        this.non_blind_state
            .as_mut()
            .unwrap()
            .constraints
            .sort_by_key(|v| v.order);

        let permissions = ReElaboratedPermissions::new(this);
        let mut outlives = ReIncrementalConstraints::new(this);

        let mut to_resolve = Vec::new();

        for cst in &this.non_blind_state.as_ref().unwrap().constraints {
            outlives.add_constraint(cst.lhs, cst.rhs, |var, must_outlive| {
                if permissions.can_outlive(var, must_outlive) {
                    return Ok(());
                }

                to_resolve.push((
                    cst.handle.clone(),
                    ReAndReUnifyErrorCause {
                        requires_var: var,
                        to_outlive: must_outlive.to_re(),
                    },
                ));

                Err(ErrorGuaranteed::new_unchecked())
            });
        }

        for (promise, err) in to_resolve {
            promise.reject(ccx, err);
        }

        for cst_idx in 0..get_this(ccx)
            .non_blind_state
            .as_ref()
            .unwrap()
            .constraints
            .len()
        {
            get_this(ccx).non_blind_state.as_ref().unwrap().constraints[cst_idx]
                .handle
                .clone()
                .accept_if_not_rejected(ccx);
        }

        if flags::should_print_ccx_region_graph() {
            #[derive(Clone)]
            enum NodeKind {
                Universal(String),
                Infer(String),
            }

            impl fmt::Display for NodeKind {
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    let (NodeKind::Universal(v) | NodeKind::Infer(v)) = self;
                    f.write_str(v)
                }
            }

            #[derive(Copy, Clone)]
            enum EdgeKind {
                Permit,
                Constrain,
            }

            impl fmt::Display for EdgeKind {
                fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    Ok(())
                }
            }

            let this = get_this(ccx).clone();
            let nbs = this.non_blind_state.as_ref().unwrap();

            let fcx = ccx.pretty(ClausePrettyFmtOpts { verbose: true });

            let mut graph = petgraph::Graph::new();

            let universal_nodes = this
                .universals
                .indices()
                .map(|universal| {
                    graph.add_node(NodeKind::Universal(fcx.wrap(universal).to_string()))
                })
                .collect::<IndexVec<UniversalReVar, _>>();

            let infer_nodes = (0..nbs.next_infer.index())
                .map(InferReVar::from_usize)
                .map(|infer| {
                    graph.add_node(NodeKind::Infer(fcx.wrap(Re::InferVar(infer)).to_string()))
                })
                .collect::<IndexVec<InferReVar, _>>();

            let gc_node = graph.add_node(NodeKind::Universal("'gc".to_string()));

            let re_to_node = |re: InferRe| -> NodeIndex {
                match re {
                    InferRe::Gc => gc_node,
                    InferRe::Universal(var) => universal_nodes[var],
                    InferRe::Infer(var) => infer_nodes[var],
                }
            };

            for cst in &nbs.constraints {
                graph.add_edge(
                    re_to_node(cst.lhs),
                    re_to_node(cst.rhs),
                    EdgeKind::Constrain,
                );
            }

            for (universal, state) in this.universals.iter_enumerated() {
                for &other in &state.allowed_outlive {
                    graph.add_edge(
                        universal_nodes[universal],
                        re_to_node(other),
                        EdgeKind::Permit,
                    );
                }

                for &other in &state.allowed_outlived_by {
                    graph.add_edge(
                        re_to_node(other),
                        universal_nodes[universal],
                        EdgeKind::Permit,
                    );
                }
            }

            let viz = Dot::with_attr_getters(
                &graph,
                &[],
                &|_graph, edge| match edge.weight() {
                    EdgeKind::Permit => "style=solid".to_string(),
                    EdgeKind::Constrain => "style=dashed".to_string(),
                },
                &|_graph, (_idx, node)| match node {
                    NodeKind::Universal(_) => "shape=box".to_string(),
                    NodeKind::Infer(_) => "shape=circle".to_string(),
                },
            );

            println!("{viz}");
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
    permitted_uni_outlives: FastHashSet<(UniversalReVar, UniversalReVar)>,

    /// Universal variables for which `'lhs: 'gc`.
    permitted_gc_outlives: FastHashSet<UniversalReVar>,
}

impl ReElaboratedPermissions {
    fn new(tracker: &ReUnifyTracker) -> Self {
        // Convert permissions into a graph.
        let mut perm_graph = InferReGraph::default();

        for (var, state) in tracker.universals.iter_enumerated() {
            // Permissions introduce edges on this graph to ensure that...
            //
            // ```
            // permit 'a: 'b
            // permit 'b: 'c
            // ==>
            // permit 'a: 'c
            // ```
            //
            // ...works properly.
            for &outlives in &state.allowed_outlive {
                perm_graph.add(InferRe::Universal(var), outlives);
            }

            for &outlived_by in &state.allowed_outlived_by {
                perm_graph.add(outlived_by, InferRe::Universal(var));
            }
        }

        // Also convert direct constraints, excluding permissions, into a graph.
        let mut cst_graph = InferReGraph::default();

        for cst in &tracker.non_blind_state.as_ref().unwrap().constraints {
            cst_graph.add(cst.lhs, cst.rhs);
        }

        // DFS each universal's permission set to figure out which universals they are allowed to
        // outlive.
        let mut permitted_uni_outlives = FastHashSet::default();
        let mut permitted_gc_outlives = FastHashSet::default();

        let mut perm_dfs = InferReDfs::default();
        let mut cst_dfs = InferReDfs::default();

        for (var, state) in tracker.universals.iter_enumerated() {
            // Find regions for which `'var: 'other` is permitted.

            // Allow `dfs` to get saturated within the `allowed_outlive` loop since we only ever
            // need to see a given DFS target once.
            perm_dfs.clear();

            for &root in &state.allowed_outlive {
                match root {
                    InferRe::Gc | InferRe::Universal(_) => {
                        perm_dfs.visit(root);
                    }
                    InferRe::Infer(_) => {
                        // We only want to traverse constraints until we reach a universal when
                        // permitting universals to outlive an inference variable.
                        cst_dfs.visit(root);
                        cbit::cbit!(for (dfs, other) in cst_dfs.flush() {
                            match other {
                                InferRe::Gc | InferRe::Universal(_) => {
                                    perm_dfs.visit(other);
                                }
                                InferRe::Infer(_) => {
                                    dfs.visit_slice(cst_graph.outlives().successors(other));
                                }
                            }
                        });

                        cst_dfs.clear();
                    }
                }

                cbit::cbit!(for (dfs, other) in perm_dfs.flush() {
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

                    dfs.visit_slice(perm_graph.outlives().successors(other));
                });
            }

            // Find regions for which `'other: 'var` is permitted.
            perm_dfs.clear();

            for &root in &state.allowed_outlived_by {
                match root {
                    InferRe::Gc | InferRe::Universal(_) => {
                        perm_dfs.visit(root);
                    }
                    InferRe::Infer(_) => {
                        cst_dfs.visit(root);
                        cbit::cbit!(for (dfs, other) in cst_dfs.flush() {
                            match other {
                                InferRe::Gc | InferRe::Universal(_) => {
                                    perm_dfs.visit(other);
                                }
                                InferRe::Infer(_) => {
                                    dfs.visit_slice(cst_graph.outlived_by().successors(other));
                                }
                            }
                        });

                        cst_dfs.clear();
                    }
                }

                cbit::cbit!(for (dfs, other) in perm_dfs.flush() {
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

                    dfs.visit_slice(perm_graph.outlived_by().successors(other));
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

// === ReIncrementalConstraints === //

#[derive(Debug, Clone)]
struct ReIncrementalConstraints {
    /// A graph from region to regions they are constrained to outlive. Does not include permissions
    /// since the presence of a permission edge along a path implies that either...
    ///
    /// a) One universal is already allowed to outlive the permission edge universal, and is
    ///    therefore allowed to outlive all universals the other universal is allowed to outlive.
    /// b) One universal is not allowed to outlive the permission edge universal, in which case an
    ///    error is already guaranteed.
    ///
    direct_outlive_graph: DirectedInferReGraph,

    /// The set of lifetimes each universal is constrained to outlive.
    transitive_universal_outlives: IndexVec<UniversalReVar, FastHashSet<InferRe>>,

    /// A reusable queue for DFS'ing. Always empty in between invocations of `add_constraint`.
    dfs_queue: Vec<InferRe>,
}

impl ReIncrementalConstraints {
    fn new(tracker: &ReUnifyTracker) -> Self {
        Self {
            direct_outlive_graph: DirectedInferReGraph::default(),
            transitive_universal_outlives: IndexVec::from_iter(
                tracker.universals.iter().map(|_| FastHashSet::default()),
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

        let mut okay = true;

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

                            okay = false;

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

        if !okay {
            self.direct_outlive_graph.remove(lhs, rhs);
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
            Re::InferVar(var) => {
                assert_ne!(var, InferReVar::ERASED);

                Ok(InferRe::Infer(var))
            }
            Re::Error(err) => Err(err),
            Re::HrtbVar(_) => unreachable!(),
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
    entries: FastHashSet<(InferRe, InferRe)>,
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
struct DirectedInferReGraph(InferReMap<SmallVec<[InferRe; 2]>>);

impl DirectedInferReGraph {
    fn add(&mut self, lhs: InferRe, rhs: InferRe) {
        self.0.get_mut(lhs).push(rhs);
    }

    fn remove(&mut self, lhs: InferRe, rhs: InferRe) {
        let target = self.0.get_mut(lhs);
        target.remove(target.iter().position(|&v| v == rhs).unwrap());
    }

    fn successors(&self, re: InferRe) -> &[InferRe] {
        self.0.get(re).map_or(&[][..], |v| v.as_slice())
    }
}

#[derive(Debug, Clone, Default)]
struct InferReDfs {
    visited: FastHashSet<InferRe>,
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
