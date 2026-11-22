use crate::{
    semantic::{
        infer::{
            ClauseCx, ClausePrettyFmtOpts, Promise, PromiseHandle, PromiseResolutionQueue,
            ReAndReUnifyError, ReConstraintOrder, RePermissionFlags,
            unify::regions::solver::{RegionFormulaSolver, RegionFormulaTerm},
        },
        syntax::{InferReVar, Re, RelationMode, UniversalReVar},
    },
    utils::lang::RangeExt as _,
};
use clay_core::{FastHashSet, FastIndexSet};
use index_vec::{IndexVec, define_index_type};
use petgraph::{Direction, Graph, dot::Dot, graph::NodeIndex, visit::EdgeRef};
use std::{
    fmt::{self, Display},
    range::Range,
};

// === RegionRelationGraph === //

define_index_type! {
    struct BufferIdx = u32;
}

define_index_type! {
    struct RelationIdx = u32;
    MAX_INDEX = (u32::MAX - 2) as usize;
}

#[derive(Clone)]
pub struct RegionRelationGraph<'sess> {
    buffer: IndexVec<BufferIdx, RegionFormulaTerm>,
    relations: IndexVec<RelationIdx, Relation<'sess>>,
    permission_count: RelationIdx,
}

#[derive(Clone)]
struct Relation<'sess> {
    /// A handle if this is a constraint or `None` if this is the assertion portion of a permission.
    handle: Option<PromiseHandle<'sess, ReAndReUnifyError>>,

    /// The flags used to create this permission, if applicable.
    flags: RePermissionFlags,

    /// The order in which this relation should be added to the solver.
    order: RelationOrder,

    mode: RelationMode,
    lhs: Range<BufferIdx>,
    rhs: Range<BufferIdx>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
enum RelationOrder {
    Permission,
    Constraint(ReConstraintOrder),
}

impl RelationOrder {
    fn to_num(self) -> u32 {
        match self {
            RelationOrder::Permission => 0,
            RelationOrder::Constraint(order) => order.0.get(),
        }
    }
}

impl Default for RegionRelationGraph<'_> {
    fn default() -> Self {
        Self {
            buffer: IndexVec::new(),
            relations: IndexVec::new(),
            permission_count: RelationIdx::from_usize(0),
        }
    }
}

impl<'sess> RegionRelationGraph<'sess> {
    pub fn permit(
        &mut self,
        mode: RelationMode,
        flags: RePermissionFlags,
        lhs: impl IntoIterator<Item = Re>,
        rhs: impl IntoIterator<Item = Re>,
    ) {
        let Some((lhs, rhs)) = self.push_to_buffer(lhs, rhs) else {
            // (Vacuous)
            return;
        };

        self.relations.push(Relation {
            handle: None,
            order: RelationOrder::Permission,
            flags,
            mode,
            lhs,
            rhs,
        });

        self.permission_count += 1;
    }

    pub fn constrain(
        &mut self,
        order: ReConstraintOrder,
        mode: RelationMode,
        lhs: impl IntoIterator<Item = Re>,
        rhs: impl IntoIterator<Item = Re>,
    ) -> Promise<'sess, ReAndReUnifyError> {
        let Some((lhs, rhs)) = self.push_to_buffer(lhs, rhs) else {
            // (Vacuous)
            return Promise::trivial();
        };

        let (promise, handle) = Promise::new();

        self.relations.push(Relation {
            handle: Some(handle),
            order: RelationOrder::Constraint(order),
            flags: RePermissionFlags::empty(),
            mode,
            lhs,
            rhs,
        });

        promise
    }

    fn push_to_buffer(
        &mut self,
        lhs: impl IntoIterator<Item = Re>,
        rhs: impl IntoIterator<Item = Re>,
    ) -> Option<(Range<BufferIdx>, Range<BufferIdx>)> {
        let lhs_start = self.buffer.len_idx();
        self.buffer.extend(
            lhs.into_iter()
                .filter_map(|re| RegionFormulaTerm::from_re(re).ok()),
        );

        let rhs_start = self.buffer.len_idx();
        self.buffer.extend(
            rhs.into_iter()
                .filter_map(|re| RegionFormulaTerm::from_re(re).ok()),
        );

        if lhs_start == rhs_start || rhs_start == self.buffer.len_idx() {
            self.buffer.truncate(lhs_start.index());
            return None;
        }

        Some((
            (lhs_start..rhs_start).into(),
            (rhs_start..self.buffer.len_idx()).into(),
        ))
    }

    pub fn verify(
        &mut self,
        queue: &mut PromiseResolutionQueue<'sess>,
        universal_count: usize,
        infer_count: usize,
    ) {
        // Elaborate permissions according to their `RePermissionFlags`.
        PermissionElaborator::new(self, universal_count, infer_count).elaborate(self);

        self.relations
            .sort_by_key(|relation| relation.order.to_num());

        let (permissions, constraints) = self.relations.split_at(self.permission_count);

        // Now, we can run our formula solver on the stream of axioms and checks.
        let mut solver = RegionFormulaSolver::new(universal_count, infer_count);

        for permission in permissions {
            debug_assert!(permission.handle.is_none());
            debug_assert_eq!(permission.order, RelationOrder::Permission);

            for (lhs, rhs) in permission.mode.enumerate(
                // Recall: the solver uses implications but we use `'a: &longer 'b` constraints,
                // hence the backwards `rhs` and `lhs`.
                &self.buffer[permission.rhs.to_ops_range()],
                &self.buffer[permission.lhs.to_ops_range()],
            ) {
                solver.push_axiom(lhs.iter().copied(), rhs.iter().copied());
            }
        }

        for constraint in constraints {
            let handle = constraint.handle.as_ref().unwrap();
            let mut causes = Vec::new();

            for (lhs, rhs) in constraint.mode.enumerate(
                // Same as above.
                &self.buffer[constraint.rhs.to_ops_range()],
                &self.buffer[constraint.lhs.to_ops_range()],
            ) {
                if let Err(err) = solver.push_checked(lhs.iter().copied(), rhs.iter().copied()) {
                    causes.push(err);
                }
            }

            if causes.is_empty() {
                handle.queue_accept(queue);
            } else {
                handle.queue_reject(
                    queue,
                    ReAndReUnifyError {
                        lhs: self.buffer[constraint.lhs.to_ops_range()]
                            .iter()
                            .map(|v| v.to_re())
                            .collect(),
                        rhs: self.buffer[constraint.rhs.to_ops_range()]
                            .iter()
                            .map(|v| v.to_re())
                            .collect(),
                        mode: constraint.mode,
                        causes,
                    },
                );
            }
        }
    }

    pub fn graphviz(
        &self,
        ccx: &ClauseCx<'_>,
        universal_count: usize,
        infer_count: usize,
    ) -> String {
        #[derive(Copy, Clone)]
        enum VizNode {
            Gc,
            Universal(UniversalReVar),
            Infer(InferReVar),
            Conjunction,
        }

        #[derive(Copy, Clone)]
        enum VizEdge {
            Thin,
            Constraint,
            Permission,
        }

        let mut graph = Graph::<VizNode, VizEdge>::new();

        let universals = (0..universal_count)
            .map(UniversalReVar::from_usize)
            .map(|var| graph.add_node(VizNode::Universal(var)))
            .collect::<IndexVec<UniversalReVar, NodeIndex>>();

        let infers = (0..infer_count)
            .map(InferReVar::from_usize)
            .map(|var| graph.add_node(VizNode::Infer(var)))
            .collect::<IndexVec<InferReVar, NodeIndex>>();

        let gc = graph.add_node(VizNode::Gc);

        let translate_node = |term: RegionFormulaTerm| -> NodeIndex {
            match term {
                RegionFormulaTerm::True => gc,
                RegionFormulaTerm::Universal(var) => universals[var],
                RegionFormulaTerm::Existential(var) => infers[var],
            }
        };

        for Relation {
            handle,
            mode,
            lhs,
            rhs,
            ..
        } in &self.relations
        {
            let lhs = &self.buffer[lhs.to_ops_range()];
            let rhs = &self.buffer[rhs.to_ops_range()];

            let edge = match handle {
                Some(_) => VizEdge::Constraint,
                None => VizEdge::Permission,
            };

            for (lhs, rhs) in mode.enumerate(lhs, rhs) {
                let rhs = match rhs.as_raw_slice() {
                    [] => continue,
                    &[unique] => translate_node(unique),
                    conjoined => {
                        let conjunction = graph.add_node(VizNode::Conjunction);

                        for &part in conjoined {
                            graph.add_edge(conjunction, translate_node(part), VizEdge::Thin);
                        }

                        conjunction
                    }
                };

                for &lhs in lhs {
                    let lhs = translate_node(lhs);

                    graph.add_edge(lhs, rhs, edge);
                }
            }
        }

        let pretty = ccx.pretty(ClausePrettyFmtOpts { verbose: true });

        fmt::from_fn(|f| {
            Dot::with_attr_getters(
                &graph,
                &[],
                &|_, edge| match edge.weight() {
                    VizEdge::Thin => "color=red".to_string(),
                    VizEdge::Constraint => "color=black".to_string(),
                    VizEdge::Permission => "color=gray".to_string(),
                },
                &|_, (_, node)| match node {
                    VizNode::Gc => "shape=rectangle, color=gold".to_string(),
                    VizNode::Universal(_) => "shape=rectangle, color=green".to_string(),
                    VizNode::Infer(_) => "shape=circle, color=blue".to_string(),
                    VizNode::Conjunction => "shape=circle, color=red".to_string(),
                },
            )
            .graph_fmt(
                f,
                |node, f| match *node {
                    VizNode::Gc => f.write_str("'gc"),
                    VizNode::Universal(var) => pretty.wrap(var).fmt(f),
                    VizNode::Infer(var) => pretty.wrap(Re::InferVar(var)).fmt(f),
                    VizNode::Conjunction => f.write_str("^"),
                },
                |_edge, _f| Ok(()),
            )
        })
        .to_string()
    }
}

// === PermissionElaborator === //

struct PermissionElaborator {
    graph: Graph<ElaboratorNode, ()>,
    universals: IndexVec<UniversalReVar, NodeIndex>,
    existentials: IndexVec<InferReVar, NodeIndex>,
    truthy: NodeIndex,
    to_idealize: Vec<InferReVar>,
    to_propagate: Vec<ToPropagate>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
enum ElaboratorNode {
    True,
    And,
    Universal(UniversalReVar),
    Existential(InferReVar),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
struct ToPropagate {
    target: NodeIndex,
    direction: Direction,
}

impl PermissionElaborator {
    fn new(tracker: &RegionRelationGraph<'_>, universal_count: usize, infer_count: usize) -> Self {
        let mut graph = Graph::new();

        let existentials = (0..infer_count)
            .map(InferReVar::from_usize)
            .map(|var| graph.add_node(ElaboratorNode::Existential(var)))
            .collect::<IndexVec<InferReVar, _>>();

        let universals = (0..universal_count)
            .map(UniversalReVar::from_usize)
            .map(|var| graph.add_node(ElaboratorNode::Universal(var)))
            .collect::<IndexVec<UniversalReVar, _>>();

        let truthy = graph.add_node(ElaboratorNode::True);

        let mut this = Self {
            graph,
            universals,
            existentials,
            truthy,
            to_idealize: Vec::new(),
            to_propagate: Vec::new(),
        };

        for &Relation {
            ref handle,
            mode,
            flags: permissions,
            lhs,
            rhs,
            ..
        } in &tracker.relations
        {
            // To make everything confusing forever, we use the implication order of regions. Yes,
            // having two conventions for LHS and RHS is super annoying.
            for (lhs, rhs) in mode.enumerate(rhs, lhs) {
                this.build_implication_edge(
                    tracker,
                    handle.is_none().then_some(permissions),
                    lhs,
                    rhs,
                );
            }
        }

        this
    }

    fn build_implication_edge(
        &mut self,
        tracker: &RegionRelationGraph<'_>,
        permissions: Option<RePermissionFlags>,
        lhs: Range<BufferIdx>,
        rhs: Range<BufferIdx>,
    ) {
        let lhs = tracker.buffer[lhs.to_ops_range()].as_raw_slice();
        let rhs = tracker.buffer[rhs.to_ops_range()].as_raw_slice();

        if let Some(permissions) = permissions {
            for &lhs in lhs {
                match lhs {
                    RegionFormulaTerm::Existential(var) => {
                        // Yes, this is another instance of a backwards implication. Deal with it.
                        if permissions.contains(RePermissionFlags::IDEALIZE_RHS) {
                            self.to_idealize.push(var);
                        }
                    }
                    RegionFormulaTerm::True | RegionFormulaTerm::Universal(_) => {
                        // (no need to complete)
                    }
                }
            }
        }

        match lhs {
            [] => {
                // (vacuous)
            }
            &[lhs] => {
                let lhs = self.term_to_node(lhs);

                for &rhs in rhs {
                    let rhs = self.term_to_node(rhs);

                    self.graph.add_edge(lhs, rhs, ());
                }
            }
            lhs => {
                let and = self.graph.add_node(ElaboratorNode::And);

                for &lhs in lhs {
                    let lhs = self.term_to_node(lhs);

                    self.graph.add_edge(lhs, and, ());
                }

                for &rhs in rhs {
                    let rhs = self.term_to_node(rhs);

                    self.graph.add_edge(and, rhs, ());
                }
            }
        }
    }

    fn term_to_node(&self, term: RegionFormulaTerm) -> NodeIndex {
        match term {
            RegionFormulaTerm::True => self.truthy,
            RegionFormulaTerm::Universal(var) => self.universals[var],
            RegionFormulaTerm::Existential(var) => self.existentials[var],
        }
    }

    fn elaborate(&self, tracker: &mut RegionRelationGraph<'_>) {
        self.elaborate_propagations(tracker);
        self.elaborate_idealizations(tracker);
    }

    fn elaborate_propagations(&self, tracker: &mut RegionRelationGraph<'_>) {
        todo!()
    }

    fn elaborate_idealizations(&self, tracker: &mut RegionRelationGraph<'_>) {
        let mut queue = Vec::new();
        let mut visit_set = FastHashSet::default();
        let mut universal_set = FastIndexSet::default();

        for &to_idealize in &self.to_idealize {
            // Figure out everything we could imply.
            queue.push(self.existentials[to_idealize]);
            visit_set.insert(self.existentials[to_idealize]);

            while let Some(curr) = queue.pop() {
                for edge in self.graph.edges_directed(curr, Direction::Outgoing) {
                    let next = edge.target();

                    match self.graph[next] {
                        ElaboratorNode::True => {
                            // (ignored)
                        }
                        ElaboratorNode::Universal(var) => {
                            universal_set.insert(var);
                        }
                        ElaboratorNode::Existential(_) | ElaboratorNode::And => {
                            if visit_set.insert(next) {
                                queue.push(next);
                            }
                        }
                    }
                }
            }

            // Create the necessary conjunction node.
            // Recall: the order is backwards :)
            if !universal_set.is_empty() {
                tracker.permit(
                    RelationMode::LhsOntoRhs,
                    RePermissionFlags::empty(),
                    [Re::InferVar(to_idealize)],
                    universal_set.iter().map(|&var| Re::UniversalVar(var)),
                );
            } else {
                tracker.permit(
                    RelationMode::LhsOntoRhs,
                    RePermissionFlags::empty(),
                    [Re::InferVar(to_idealize)],
                    [Re::Gc],
                );
            }

            // Reset
            queue.clear();
            visit_set.clear();
            universal_set.clear();
        }
    }
}
