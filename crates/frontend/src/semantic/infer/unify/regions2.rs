//! Clay's region solver.
//!
//! ## Underlying Theory
//!
//! Region constraints take the form...
//!
//! ```text
//! 'lhs_1 + ... + 'lhs_n: 'rhs_1 + ... + 'rhs_n
//! ```
//!
//! ...where the `+` denotes a set of regions. It indicates that, if `'rhs_1` through `'rhs_n` are
//! all alive, `'lhs_1` through `'lhs_n` will also be alive.
//!
//! For example, the source code region constraint `(&'a (), &'b ()): &longer (&'c (), &'d ())`
//! would be represented in the solver as the formula `'a + 'b: 'c + 'd`. As another example, the
//! source code region constraint `'a: &longer 'gc` would indicate that, so long as `'gc` is alive,
//! so too will `'a`; thus, since `'gc` is always alive, `'a` will also always be alive.
//!
//! Given a set of precondition formulae, a new formula can be determined sound *iff* it meets the
//! following logical equation...
//!
//! ```text
//! forall<'universal_1, ..., 'universal_n>
//!     (exists<'infer_1, ..., 'infer_n>
//!         (
//!             'precond_1_rhs_1 & ... & 'precond_1_rhs_n
//!             =>
//!             'precond_1_lhs_1 & ... & 'precond_1_lhs_n
//!         )
//!         &
//!         ...
//!         &
//!         (
//!             'precond_m_rhs_1 & ... & 'precond_m_rhs_n
//!             =>
//!             'precond_m_lhs_1 & ... & 'precond_m_lhs_n
//!         )
//!     )
//!     =>
//!     (exists<'infer_1, ..., 'infer_n>
//!         (
//!             'precond_1_rhs_1 & ... & 'precond_1_rhs_n
//!             =>
//!             'precond_1_lhs_1 & ... & 'precond_1_lhs_n
//!         )
//!         &
//!         ...
//!         &
//!         (
//!             'precond_m_rhs_1 & ... & 'precond_m_rhs_n
//!             =>
//!             'precond_m_lhs_1 & ... & 'precond_m_lhs_n
//!         )
//!         &
//!         (
//!             'consequent_rhs_1 & ... & 'consequent_rhs_n
//!             =>
//!             'consequent_lhs_1 & ... & 'consequent_lhs_n
//!         )
//!     )
//! ```
//!
//! A few notes...
//!
//! 1. Each universal region becomes a universally quantified boolean and each inference region
//!    becomes an existentially quantified boolean.
//!
//! 2. The term `'lhs_1 + ... + 'lhs_n: 'rhs_1 + ... + 'rhs_n` becomes
//!    `'rhs_1 & .. & 'rhs_n => 'lhs_1 & ... & 'lhs_n` where each variable denotes the liveness
//!    of a given region.
//!
//! 3. The special region `'gc` is treated as a logical truth.
//!
//! 4. We use two existential binders to handle inference variables rather than writing
//!    `forall<...> exists<...> precond => consequent` because, otherwise, the inference variables
//!    could be chosen to potentially make the preconditions falsy regardless of the consequent.
//!
//! ## Solving and NP-Completeness
//!
//! We would like to construct an algorithm that takes preconditions and a consequent and returns
//! whether that consequent is satisfiable according to the definition above.
//!
//! As is tradition, we'll be doing this by attempting to disprove the satisfiability of the
//! routine. The means coming up with a set of universals which force the consequent RHS to be true
//! but the consequent LHS to be false.
//!
//! Unfortunately, there are a possibly exponential number of ways to force the RHS to be true and
//! a possibly exponential number of ways to force the LHS to be false.
//!
//! Consider the following input, which has a number of ways to set the LHS to `true` exponential
//! in the number of universals defined...
//!
//! ```text
//! u't_1 => i'1
//! u'f_1 => i'1
//!
//! ...
//!
//! u't_n => i'n
//! u'f_n => i'n
//!
//! i'1 & ... & i'n => rhs
//! ```
//!
//! ...where `i'x` denotes an inference region and `u'x` denotes a universal region.
//!
//! Likewise, consider the following input—this time, exponential in the number of ways in which
//! it could be made falsy...
//!
//! ```text
//! u't_1 & u'f_1 => i'a
//! ...
//! u't_n & u'f_n => i'a
//!
//! lhs => i'a
//! ```
//!
//! Unfortunately, one can reduce a 3-SAT problem into our solver like so...
//!
//! ```text
//! // Consider the following 3-SAT problem...
//! // (A || !B || C) & (!A || !B || C)
//!
//! // First, we create the following universals...
//! //
//! // u'a_t, u'b_t, u'c_t
//! // u'a_f, u'b_f, u'c_f
//! //
//! // `u'a_t` denotes `A` is `true` and `u'a_f` denotes `A` is `false`.
//!
//! // Disjunction
//! u'a_t & u'a_f => u'dead_if_not_both
//! u'b_t & u'b_f => u'dead_if_not_both
//! u'c_t & u'c_f => u'dead_if_not_both
//!
//! u'a_t => i'live_if_at_least_one_a
//! u'a_f => i'live_if_at_least_one_a
//! u'b_t => i'live_if_at_least_one_b
//! u'b_f => i'live_if_at_least_one_b
//! u'c_t => i'live_if_at_least_one_c
//! u'c_f => i'live_if_at_least_one_c
//!
//! // 3-SAT triples
//! u'a_t => i'live_if_term_1_truthy
//! u'b_f => i'live_if_term_1_truthy
//! u'c_t => i'live_if_term_1_truthy
//!
//! u'a_f => i'live_if_term_2_truthy
//! u'b_f => i'live_if_term_2_truthy
//! u'c_t => i'live_if_term_2_truthy
//!
//! // Final consequent (all terms above were preconditions)
//! i'?live_if_at_least_one_a & ?live_if_at_least_one_b & ?live_if_at_least_one_c &
//!     i'live_if_term_1_truthy & i'live_if_term_2_truthy => u'dead_if_not_both
//! ```
//!
//! The 3-SAT formula is satisfiable *iff* we can come up with a set of universals that cause a
//! contradiction in our formula:
//!
//! - If we try to select `A_t` and `A_f`, we'll be forced to enable the `dead_if_not_both`
//!   universal and cause the consequent to pass.
//! - If we select neither `A_t` nor `A_f`, `?true_if_non_empty` will be allowed to be `false`.
//! - If we don't match all terms, `?terms_truthy` will be allowed to be `false`.
//!
//! Let's see how we would express this in Clay...
//!
//! ```text
//! struct Binder<'a>;
//!
//! impl Binder<'a> {
//!     fn new() => Self {
//!         Self
//!     }
//!
//!     fn longer<'s: &shorter Self, 'b: &longer 'a>() {}
//! }
//!
//! fn assert_all_imply<
//!     'lhs: &longer (&'rhs_1 (), &'rhs_2 (), &'rhs_3 (), &'rhs_4 (), &'rhs_5 ()),
//!     'rhs_1, 'rhs_2, 'rhs_3, 'rhs_4, 'rhs_5
//! >(
//!     rhs_1: Binder<'rhs_1>,
//!     rhs_2: Binder<'rhs_2>,
//!     rhs_3: Binder<'rhs_3>,
//!     rhs_4: Binder<'rhs_4>,
//!     rhs_5: Binder<'rhs_5>
//! ) {
//! }
//!
//! fn meow<
//!     'a_t, 'a_f,
//!     'b_t, 'b_f,
//!     'c_t, 'c_f,
//!     'dead_if_not_both:
//!         &longer (&'a_t (), &'a_f ()) +  // a_t + a_f => dead_if_not_both
//!         &longer (&'b_t (), &'b_f ()) +  // b_t + b_f => dead_if_not_both
//!         &longer (&'c_t (), &'c_f ()),   // c_t + c_f => dead_if_not_both
//! >() {
//!     let live_if_at_least_one_a = Binder::new();
//!     live_if_at_least_one_a.longer::<'a_t>();  // 'a_t => ?live_if_at_least_one_a
//!     live_if_at_least_one_a.longer::<'a_f>();  // 'a_f => ?live_if_at_least_one_a
//!
//!     let live_if_at_least_one_b = Binder::new();
//!     live_if_at_least_one_b.longer::<'b_t>();  // 'b_t => ?live_if_at_least_one_b
//!     live_if_at_least_one_b.longer::<'b_f>();  // 'b_f => ?live_if_at_least_one_b
//!
//!     let live_if_at_least_one_c = Binder::new();
//!     live_if_at_least_one_c.longer::<'c_t>();  // 'c_t => ?live_if_at_least_one_c
//!     live_if_at_least_one_c.longer::<'c_f>();  // 'c_f => ?live_if_at_least_one_c
//!
//!     let live_if_term_1_truthy = Binder::new();
//!     live_if_term_1_truthy.longer::<'a_t>();  // 'a_t => ?live_if_term_1_truthy
//!     live_if_term_1_truthy.longer::<'b_f>();  // 'b_f => ?live_if_term_1_truthy
//!     live_if_term_1_truthy.longer::<'c_t>();  // 'c_t => ?live_if_term_1_truthy
//!
//!     let live_if_term_2_truthy = Binder::new();
//!     live_if_term_2_truthy.longer::<'a_f>();  // 'a_f => ?live_if_term_2_truthy
//!     live_if_term_2_truthy.longer::<'b_f>();  // 'b_f => ?live_if_term_2_truthy
//!     live_if_term_2_truthy.longer::<'c_t>();  // 'c_t => ?live_if_term_2_truthy
//!
//!     // ?live_if_at_least_one_a + ?live_if_at_least_one_b + ?live_if_at_least_one_c +
//!     //    ?live_if_term_1_truthy + ?live_if_term_2_truthy => 'dead_if_not_both
//!     assert_all_imply::<'_, '_, '_, '_, '_, 'dead_if_not_both>(
//!         live_if_at_least_one_a,
//!         live_if_at_least_one_b,
//!         live_if_at_least_one_c,
//!         live_if_term_1_truthy,
//!         live_if_term_2_truthy,
//!     );
//! }
//! ```
//!
//! Using just `&longer <type>` universal constraints (or `<type>: &shorter <lifetime>`), one can
//! reduce SAT-3 to Clay. This is all very unfortunate!
//!
//! How does Rust fare? Here is the closest I got to replicating this case...
//!
//! ```ignore
//! use std::marker::PhantomData;
//!
//! #[derive(Default, Copy, Clone)]
//! struct Binder<'a>(PhantomData<fn(&'a ()) => &'a ()>);
//!
//! impl<'a> Binder<'a> {
//!     fn longer<'b: 'a>(&self, _: Binder<'b>) {}
//! }
//!
//! fn dead_unless_at_least_one_live<'a, 'b, 'c, A: 'a, B: 'b, C: 'c>(
//!     _: A,
//!     _: B,
//!     _: C,
//! ) => impl Sized + 'a + 'b + 'c {
//! }
//!
//! fn meow<'a_t, 'a_f, 'b_t, 'b_f, 'c_t, 'c_f>(
//!     a_t: Binder<'a_t>,
//!     a_f: Binder<'a_f>,
//!     b_t: Binder<'b_t>,
//!     b_f: Binder<'b_f>,
//!     c_t: Binder<'c_t>,
//!     c_f: Binder<'c_f>,
//! ) {
//!     // live(u'a_t) & live (u'a_f) => live(u'dead_unless_true_and_false_simultaneously)
//!     // live(u'b_t) & live (u'b_f) => live(u'dead_unless_true_and_false_simultaneously)
//!     // live(u'c_t) & live (u'c_f) => live(u'dead_unless_true_and_false_simultaneously)
//!     let dead_unless_true_and_false_simultaneously =
//!         dead_unless_at_least_one_live((a_t, a_f), (b_t, b_f), (c_t, c_f));
//!
//!     let live_if_at_least_one_a = Binder::default();
//!     live_if_at_least_one_a.longer(a_t); // live(u'a_t) => live(i'live_if_at_least_one_a)
//!     live_if_at_least_one_a.longer(a_f); // live(u'a_f) => live(i'live_if_at_least_one_a)
//!
//!     let live_if_at_least_one_b = Binder::default();
//!     live_if_at_least_one_b.longer(b_t); // live(u'b_t) => live(i'live_if_at_least_one_b)
//!     live_if_at_least_one_b.longer(b_f); // live(u'b_f) => live(i'live_if_at_least_one_b)
//!
//!     let live_if_at_least_one_c = Binder::default();
//!     live_if_at_least_one_c.longer(c_t); // live(u'c_t) => live(i'live_if_at_least_one_c)
//!     live_if_at_least_one_c.longer(c_f); // live(u'c_f) => live(i'live_if_at_least_one_c)
//!
//!     let live_if_term_1_truthy = Binder::default();
//!     live_if_term_1_truthy.longer(a_t); // live(u'a_t) => live(i'live_if_term_1_truthy)
//!     live_if_term_1_truthy.longer(b_f); // live(u'b_f) => live(i'live_if_term_1_truthy)
//!     live_if_term_1_truthy.longer(c_t); // live(u'c_t) => live(i'live_if_term_1_truthy)
//!
//!     let live_if_term_2_truthy = Binder::default();
//!     live_if_term_2_truthy.longer(a_f); // live(u'a_f) => live(i'live_if_term_2_truthy)
//!     live_if_term_2_truthy.longer(b_f); // live(u'b_f) => live(i'live_if_term_2_truthy)
//!     live_if_term_2_truthy.longer(c_t); // live(u'c_t) => live(i'live_if_term_2_truthy)
//!
//!     let live_if_satisfied = (
//!         live_if_at_least_one_a,
//!         live_if_at_least_one_b,
//!         live_if_at_least_one_c,
//!         live_if_term_1_truthy,
//!         live_if_term_2_truthy,
//!     );
//!
//!     // ???
//! }
//! ```
//!
//! Since there is no mechanism to assert that `live_if_satisfied` being live implies that
//! `dead_unless_true_and_false_simultaneously` is also live, it seems like this case is impossible
//! to express in Rust.
//!
//! Perhaps we could revisit the surface syntax of Clay to bring its complexity closer to Rust's?
//!
//! For the time being, we will write an NP-complete solver and hope that users won't run into
//! it in practice. It's really difficult to say which exact restrictions we would have to put on
//! the logical language itself to prevent NP-completeness and, with the presence of
//! `&longer <type>` or `&longer (<region list>)` syntax in dynamic trait types to support a
//! mechanism similar to Rust's `impl Trait + use<'a> + use<'b>` in return position feature, we'll
//! likely end up having to accept some level of NP-completeness, even if we do ultimately curb the
//! most obvious ways to trigger it.
//!
//! ## Reduction to SAT
//!
//! TODO
//!
//! ## Organization
//!
//! - The [`RegionSatSolver`] provides an interactive structure for verifying formulae using the
//!   theory defined above. One can either push a formula as an axiom using `push_axiom` or
//!   push a formula while checking its validity against the preconditions using `push_checked`.
//!
//! - The [`ReUnifyTracker`] builds on the `RegionSatSolver` to add support for permission and
//!   constraint edges such that permissions properly propagate across reachable subgraphs of
//!   inference nodes.

use crate::semantic::syntax::{InferReVar, UniversalReVar};
use index_vec::IndexVec;
use petgraph::{Graph, graph::NodeIndex};

// === RegionSatSolver === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum RegionSatTerm {
    True,
    Universal(UniversalReVar),
    Existential(InferReVar),
}

pub struct RegionSatSolver {
    graph: Graph<SatNode, ()>,
    true_node: NodeIndex,
    universal_nodes: IndexVec<UniversalReVar, NodeIndex>,
    existential_nodes: IndexVec<InferReVar, NodeIndex>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
enum SatNode {
    And,
    True,
    Universal(UniversalReVar),
    Existential(InferReVar),
}

impl RegionSatSolver {
    pub fn new(universal_count: usize, existential_count: usize) -> Self {
        let mut graph = Graph::new();

        let true_node = graph.add_node(SatNode::True);

        let universal_nodes = (0..universal_count)
            .map(|idx| graph.add_node(SatNode::Universal(UniversalReVar::from_usize(idx))))
            .collect();

        let existential_nodes = (0..existential_count)
            .map(|idx| graph.add_node(SatNode::Existential(InferReVar::from_usize(idx))))
            .collect();

        Self {
            graph,
            true_node,
            universal_nodes,
            existential_nodes,
        }
    }

    fn transform_term(&self, term: RegionSatTerm) -> NodeIndex {
        match term {
            RegionSatTerm::True => self.true_node,
            RegionSatTerm::Universal(var) => self.universal_nodes[var],
            RegionSatTerm::Existential(var) => self.existential_nodes[var],
        }
    }

    pub fn push_axiom(&mut self, lhs: &[RegionSatTerm], rhs: RegionSatTerm) {
        todo!()
    }

    pub fn push_checked(
        &mut self,
        lhs: impl IntoIterator<Item = RegionSatTerm>,
        rhs: impl IntoIterator<Item = RegionSatTerm>,
    ) {
        let mut lhs = lhs.into_iter().fuse();
        let mut rhs = rhs.into_iter().peekable();

        if rhs.peek().is_none() {
            // Vacuous
            return;
        }

        let lhs = match (lhs.next(), lhs.next()) {
            (None, None) => {
                // Vacuous
                return;
            }
            (Some(node), None) => self.transform_term(node),
            (Some(first), Some(second)) => {
                let joiner = self.graph.add_node(SatNode::And);

                for lhs in [first, second].into_iter().chain(lhs) {
                    self.graph.add_edge(self.transform_term(lhs), joiner, ());
                }

                joiner
            }
            (None, Some(_)) => unreachable!(),
        };

        // TODO
    }

    fn push_checked_internal(&mut self, lhs: NodeIndex, rhs: NodeIndex) {
        // First, let us determine all the ways to force the `lhs` to be true.
    }
}

// === ReUnifyTracker === //

pub struct ReUnifyTracker {}
