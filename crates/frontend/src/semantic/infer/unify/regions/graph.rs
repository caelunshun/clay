use crate::{
    bool_enum,
    semantic::{
        infer::{
            ClauseCx, ClausePrettyFmtOpts, Promise, PromiseHandle, PromiseResolutionQueue,
            ReAndReUnifyError, ReConstraintOrder,
            unify::regions::solver::{RegionFormulaSolver, RegionFormulaTerm},
        },
        syntax::{InferReVar, Re, RelationMode, UniversalReVar},
    },
    utils::lang::RangeExt as _,
};
use clay_core::FastHashSet;
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
        // For permissions involving inference variables, we promote all relations that transitively
        // connect that inference variable to further terms into axioms, stopping until we reach a
        // universal variable or a `'gc`. If a relation has mixed axiomatic-ness—that is, parts of
        // it are axioms and parts aren't, as could happen with a conjunction term—we promote the
        // whole term.
        PermissionElaborator::new(self, universal_count, infer_count).propagate(self, queue);

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
                // TODO
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
    graph: Graph<NodeShouldPropagate, RelationIdx>,
    universals: IndexVec<UniversalReVar, NodeIndex>,
    existentials: IndexVec<InferReVar, NodeIndex>,
    truthy: NodeIndex,
}

bool_enum! {
    enum NodeShouldPropagate {
        true => Yes;
        false => No;
    }
}

const DUMMY_EDGE: RelationIdx = RelationIdx::from_raw_unchecked(u32::MAX - 1);
const PERMISSION_EDGE: RelationIdx = RelationIdx::from_raw_unchecked(u32::MAX);

impl PermissionElaborator {
    fn new(tracker: &RegionRelationGraph<'_>, universal_count: usize, infer_count: usize) -> Self {
        let mut graph = Graph::new();

        let existentials = (0..infer_count)
            .map(InferReVar::from_usize)
            .map(|_| graph.add_node(NodeShouldPropagate::Yes))
            .collect::<IndexVec<InferReVar, _>>();

        let universals = (0..universal_count)
            .map(UniversalReVar::from_usize)
            .map(|_| graph.add_node(NodeShouldPropagate::No))
            .collect::<IndexVec<UniversalReVar, _>>();

        let truthy = graph.add_node(NodeShouldPropagate::No);

        let mut this = Self {
            graph,
            universals,
            existentials,
            truthy,
        };

        for (
            relation_idx,
            &Relation {
                ref handle,
                mode,
                lhs,
                rhs,
                ..
            },
        ) in tracker.relations.iter_enumerated()
        {
            let weight = if handle.is_some() {
                relation_idx
            } else {
                PERMISSION_EDGE
            };

            for (lhs, rhs) in mode.enumerate(lhs, rhs) {
                this.build_relation(tracker, weight, lhs, rhs);
            }
        }

        this
    }

    fn build_relation(
        &mut self,
        tracker: &RegionRelationGraph<'_>,
        weight: RelationIdx,
        lhs: Range<BufferIdx>,
        rhs: Range<BufferIdx>,
    ) {
        let lhs = tracker.buffer[lhs.to_ops_range()].as_raw_slice();
        let rhs = tracker.buffer[rhs.to_ops_range()].as_raw_slice();

        match (lhs, rhs) {
            ([], _) | (_, []) => return,
            (&[lhs], rhs) => {
                for &rhs in rhs {
                    self.graph
                        .add_edge(self.term_to_node(lhs), self.term_to_node(rhs), weight);
                }
            }
            (lhs, &[rhs]) => {
                for &lhs in lhs {
                    self.graph
                        .add_edge(self.term_to_node(lhs), self.term_to_node(rhs), weight);
                }
            }
            // `joiner` avoids `O(n^2)` edge count.
            (lhs, rhs) => {
                let joiner = self.graph.add_node(NodeShouldPropagate::Yes);

                for &lhs in lhs {
                    self.graph
                        .add_edge(self.term_to_node(lhs), joiner, DUMMY_EDGE);
                }

                for &rhs in rhs {
                    self.graph.add_edge(joiner, self.term_to_node(rhs), weight);
                }
            }
        };
    }

    fn term_to_node(&self, term: RegionFormulaTerm) -> NodeIndex {
        match term {
            RegionFormulaTerm::True => self.truthy,
            RegionFormulaTerm::Universal(var) => self.universals[var],
            RegionFormulaTerm::Existential(var) => self.existentials[var],
        }
    }

    fn propagate<'sess>(
        &self,
        tracker: &mut RegionRelationGraph<'sess>,
        queue: &mut PromiseResolutionQueue<'sess>,
    ) {
        let mut forward = DirectionalPermissionElaborator::new(self, Direction::Outgoing);
        let mut backward = DirectionalPermissionElaborator::new(self, Direction::Incoming);

        for edge in self.graph.edge_references() {
            if *edge.weight() != PERMISSION_EDGE {
                continue;
            }

            if self.graph[edge.target()].is_truthy() {
                forward.queue(edge.target());
                forward.flush(tracker, queue);
            }

            if self.graph[edge.source()].is_truthy() {
                backward.queue(edge.source());
                backward.flush(tracker, queue);
            }
        }
    }
}

struct DirectionalPermissionElaborator<'a> {
    graph: &'a PermissionElaborator,
    direction: Direction,
    visit_stack: Vec<NodeIndex>,
    visit_set: FastHashSet<NodeIndex>,
}

impl<'a> DirectionalPermissionElaborator<'a> {
    fn new(graph: &'a PermissionElaborator, direction: Direction) -> Self {
        Self {
            graph,
            direction,
            visit_stack: Vec::new(),
            visit_set: FastHashSet::default(),
        }
    }

    fn queue(&mut self, node: NodeIndex) {
        if self.visit_set.insert(node) {
            self.visit_stack.push(node);
        }
    }

    fn flush<'sess>(
        &mut self,
        tracker: &mut RegionRelationGraph<'sess>,
        queue: &mut PromiseResolutionQueue<'sess>,
    ) {
        while let Some(node) = self.visit_stack.pop() {
            for edge in self.graph.graph.edges_directed(node, self.direction) {
                let relation = *edge.weight();

                if relation.index() < RelationIdx::MAX_INDEX
                    && let relation = &mut tracker.relations[relation]
                    && let Some(handle) = relation.handle.take()
                {
                    relation.order = RelationOrder::Permission;
                    tracker.permission_count += 1;
                    handle.queue_accept(queue);
                }

                let other = match self.direction {
                    Direction::Outgoing => edge.target(),
                    Direction::Incoming => edge.source(),
                };

                if self.graph.graph[other].is_truthy() {
                    self.queue(other);
                }
            }
        }
    }
}
