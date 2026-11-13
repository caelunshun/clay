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
//! i'live_if_at_least_one_a & i'live_if_at_least_one_b & i'live_if_at_least_one_c &
//!     i'live_if_term_1_truthy & i'live_if_term_2_truthy => u'dead_if_not_both
//! ```
//!
//! The 3-SAT formula is satisfiable *iff* we can come up with a set of universals that cause a
//! contradiction in our formula:
//!
//! - If we try to select `A_t` and `A_f`, we'll be forced to enable the `dead_if_not_both`
//!   universal and cause the consequent to pass.
//! - If we select neither `A_t` nor `A_f`, `i'true_if_non_empty` will be allowed to be `false`.
//! - If we don't match all terms, `i'terms_truthy` will be allowed to be `false`.
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
//!         &longer (&'a_t (), &'a_f ()) +  // u'a_t + u'a_f => u'dead_if_not_both
//!         &longer (&'b_t (), &'b_f ()) +  // u'b_t + u'b_f => u'dead_if_not_both
//!         &longer (&'c_t (), &'c_f ()),   // u'c_t + u'c_f => u'dead_if_not_both
//! >() {
//!     let live_if_at_least_one_a = Binder::new();
//!     live_if_at_least_one_a.longer::<'a_t>();  // u'a_t => i'live_if_at_least_one_a
//!     live_if_at_least_one_a.longer::<'a_f>();  // u'a_f => i'live_if_at_least_one_a
//!
//!     let live_if_at_least_one_b = Binder::new();
//!     live_if_at_least_one_b.longer::<'b_t>();  // u'b_t => i'live_if_at_least_one_b
//!     live_if_at_least_one_b.longer::<'b_f>();  // u'b_f => i'live_if_at_least_one_b
//!
//!     let live_if_at_least_one_c = Binder::new();
//!     live_if_at_least_one_c.longer::<'c_t>();  // u'c_t => i'live_if_at_least_one_c
//!     live_if_at_least_one_c.longer::<'c_f>();  // u'c_f => i'live_if_at_least_one_c
//!
//!     let live_if_term_1_truthy = Binder::new();
//!     live_if_term_1_truthy.longer::<'a_t>();  // u'a_t => i'live_if_term_1_truthy
//!     live_if_term_1_truthy.longer::<'b_f>();  // u'b_f => i'live_if_term_1_truthy
//!     live_if_term_1_truthy.longer::<'c_t>();  // u'c_t => i'live_if_term_1_truthy
//!
//!     let live_if_term_2_truthy = Binder::new();
//!     live_if_term_2_truthy.longer::<'a_f>();  // u'a_f => i'live_if_term_2_truthy
//!     live_if_term_2_truthy.longer::<'b_f>();  // u'b_f => i'live_if_term_2_truthy
//!     live_if_term_2_truthy.longer::<'c_t>();  // u'c_t => i'live_if_term_2_truthy
//!
//!     // i'live_if_at_least_one_a + i'live_if_at_least_one_b + i'live_if_at_least_one_c +
//!     //    i'live_if_term_1_truthy + i'live_if_term_2_truthy => u'dead_if_not_both
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
//! We've shown how to reduce SAT to the region system (i.e. NP-completeness) but how might we
//! reduce the region system to a SAT problem (i.e. NP-hardness, specifically if we consider
//! checking for unsoundness)? Doing this would allow us to reuse the existing hard work that has
//! gone into implementing efficient SAT solvers.
//!
//! A formula is unsound *iff* we manage to find a set of *well-formed* universals which force the
//! LHS to be live while forcing the RHS to be dead. Both the condition of "the LHS being forced to
//! be live" and the condition of the "RHS being forced to be dead" can be expressed as nested
//! conjunctions, disjunctions, and negations of boolean variables, which are bread-and-butter SAT
//! constructs. Well-formedness, likewise, can be expressed using conjunctions of implications.
//!
//! In terms of lowering...
//!
//! - On the LHS, the terms `i/u'X_1 -> Y; ...; i/u'X_n -> i'Y` tell us that `i'Y` would be forced
//!   to be alive *iff* `forced_alive(i'X_1) | ... | forced_alive(i'X_n)` is `true`.
//!
//!   The term `i/u'X_1 + ... + i/u'X_n -> i'Y` tell us that `i'Y` would be forced to be
//!   alive *iff* `forced_alive(i'X_1) & ... & forced_alive(i'X_n)` is `true`.
//!
//!   If `Y` were a universal in either of the above equations, it would only be forced to be live
//!   through well-formedness constraints.
//!
//!   The term `forced_alive(i'X)` where `X` is an inference variable with nothing implying it is
//!   `false` and `forced_alive(u'x) = x` denotes `x` the SAT variable for `u'x`.
//!
//! - On the RHS, meanwhile, the terms `i/u'X_1 -> Y; ...; i/u'X_n -> i'Y` tell us that `i'Y` would
//!   be forced to be dead *iff* `forced_dead(i'X_1) & ... & forced_dead(i'X_n)` is `true`.
//!
//!   The term `i/u'X_1 + ... + i/u'X_n -> i'Y` tell us that `i'Y` would be forced to be dead *iff*
//!   `forced_dead(i'X_1) | ... | forced_dead(i'X_n)`.
//!
//!   In summary, the LHS and RHS flip conjunction and disjunction in their liveness determination.
//!
//!   The term `forced_dead(i'X)` is `false` and `forced_dead(u'x) = !x` where `x` denotes the SAT
//!   variable for `u'x`.
//!
//! - If there is a cycle in an implication where the inference variable on the right occurs
//!   somewhere in an inference variable on the left, that term can be safely discarded because the
//!   existential value to which that inference variable corresponds can be set or unset so long as
//!   it doesn't violate any universals.
//!
//! We can employ some shortcuts to avoid having to call into a SAT solver although we'll need to
//! investigate whether any of these shortcuts are warranted or if SAT solvers already have good
//! enough fast paths for these...
//!
//! - If the number of unique universals mentioned transitively in the **LHS** is lower than some
//!   small limit (e.g. 4), we could just enumerate all the unique combinations of those universals
//!   and see which combination forces the LHS to be `true` and, by setting all the remaining
//!   universals to `false`, the RHS to be `false`.
//!
//! - If the number of unique universals mentioned transitively in the **RHS** is lower than some
//!   small limit (e.g. 4), we could just enumerate all the unique combinations of those universals
//!   and see which combination forces the RHS to be `false` and, by setting all the remaining
//!   universals to `true`, the LHS to be `true`.
//!
//! - As a refinement of the above strategies, sometimes, sets of universals are all forced to be
//!   on at the same time because they're mentioned inside a region conjunction.
//!
//! All in all, this should give hope that triggering exponential solving behavior is somewhat
//! tricky in practice: users need to mention a large number of universals in both the LHS and the
//! RHS simultaneously and must do so with a specific structure of inference lifetimes to create the
//! particular structure required for exponential blowup.
//!
//! ## Organization
//!
//! - The [`RegionFormulaSolver`] provides an interactive structure for verifying formulae using the
//!   theory defined above. One can either push a formula as an axiom using `push_axiom` or
//!   push a formula while checking its validity against the preconditions using `push_checked`.
//!
//! - The [`ReUnifyTracker`] builds on the `RegionFormulaSolver` to add support for permission and
//!   constraint edges such that permissions properly propagate across reachable subgraphs of
//!   inference nodes.

use crate::semantic::{
    infer::unify::sat::{SatBuilder, SatNaiveBuilder, SatTerm, SatVar},
    syntax::{InferReVar, UniversalReVar},
};
use clay_core::{FastHashMap, FastHashSet, FastIndexMap};
use index_vec::IndexVec;
use petgraph::{Direction, Graph, graph::NodeIndex, visit::EdgeRef};
use smallvec::SmallVec;

// === ReUnifyTracker === //

pub struct ReUnifyTracker {}

// === RegionFormulaSolver === //

const BRUTE_FORCE_VAR_LIMIT: u32 = 10;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum RegionFormulaTerm {
    True,
    Universal(UniversalReVar),
    Existential(InferReVar),
}

pub struct RegionFormulaSolver {
    graph: Graph<FormulaNode, ()>,
    true_node: NodeIndex,
    universal_nodes: IndexVec<UniversalReVar, NodeIndex>,
    existential_nodes: IndexVec<InferReVar, NodeIndex>,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
enum FormulaNode {
    And,
    True,
    Universal(UniversalReVar),
    Existential(InferReVar),
}

impl RegionFormulaSolver {
    pub fn new(universal_count: usize, existential_count: usize) -> Self {
        let mut graph = Graph::new();

        let true_node = graph.add_node(FormulaNode::True);

        let universal_nodes = (0..universal_count)
            .map(|idx| graph.add_node(FormulaNode::Universal(UniversalReVar::from_usize(idx))))
            .collect();

        let existential_nodes = (0..existential_count)
            .map(|idx| graph.add_node(FormulaNode::Existential(InferReVar::from_usize(idx))))
            .collect();

        Self {
            graph,
            true_node,
            universal_nodes,
            existential_nodes,
        }
    }

    fn transform_term(&self, term: RegionFormulaTerm) -> NodeIndex {
        match term {
            RegionFormulaTerm::True => self.true_node,
            RegionFormulaTerm::Universal(var) => self.universal_nodes[var],
            RegionFormulaTerm::Existential(var) => self.existential_nodes[var],
        }
    }

    pub fn push_axiom(
        &mut self,
        lhs: impl IntoIterator<Item = RegionFormulaTerm>,
        rhs: impl IntoIterator<Item = RegionFormulaTerm>,
    ) {
        todo!()
    }

    pub fn push_checked(
        &mut self,
        lhs: impl IntoIterator<Item = RegionFormulaTerm>,
        rhs: impl IntoIterator<Item = RegionFormulaTerm>,
    ) {
        todo!()
    }

    fn lower_lhs(&mut self, lhs: impl IntoIterator<Item = RegionFormulaTerm>) -> Option<NodeIndex> {
        let mut lhs = lhs.into_iter().fuse();

        match (lhs.next(), lhs.next()) {
            (None, None) => {
                // Vacuous
                return None;
            }
            (Some(node), None) => Some(self.transform_term(node)),
            (Some(first), Some(second)) => {
                let joiner = self.graph.add_node(FormulaNode::And);

                for lhs in [first, second].into_iter().chain(lhs) {
                    self.graph.add_edge(self.transform_term(lhs), joiner, ());
                }

                Some(joiner)
            }
            (None, Some(_)) => unreachable!(),
        }
    }

    fn check_implication(&mut self, lhs: NodeIndex, rhs: NodeIndex) {
        // Create LHS-alive and RHS-dead logical formulas.
        let mut builder = SatNaiveBuilder::default();
        let mut inf_cycle_set = FastHashSet::default();
        let mut inf_dedup = FastHashMap::default();
        let mut universals = FastIndexMap::default();

        let lhs_live = SatLivenessCollector {
            mode: SatLivenessMode::Lhs,
            graph: &self.graph,
            builder: &mut builder,
            inf_cycle_set: &mut inf_cycle_set,
            inf_dedup: &mut inf_dedup,
            universals: &mut universals,
        }
        .translate(lhs);

        inf_dedup.clear();

        let rhs_dead = SatLivenessCollector {
            mode: SatLivenessMode::Rhs,
            graph: &self.graph,
            builder: &mut builder,
            inf_cycle_set: &mut inf_cycle_set,
            inf_dedup: &mut inf_dedup,
            universals: &mut universals,
        }
        .translate(rhs);

        // Attempt to use the brute-force approach to solve this equation.
        let mut lhs_universals = 0;
        let mut rhs_universals = 0;

        for universal in universals.values() {
            if universal.in_lhs {
                lhs_universals += 1;
            }

            if universal.in_rhs {
                rhs_universals += 1;
            }
        }

        if lhs_universals < rhs_universals && lhs_universals < BRUTE_FORCE_VAR_LIMIT {
            todo!()
        }

        if rhs_universals < lhs_universals && rhs_universals < BRUTE_FORCE_VAR_LIMIT {
            todo!()
        }

        // Otherwise, punt it to a proper SAT solver.
        todo!();
    }
}

struct SatLivenessCollector<'a, B: SatBuilder> {
    mode: SatLivenessMode,
    graph: &'a Graph<FormulaNode, ()>,
    builder: &'a mut B,
    inf_cycle_set: &'a mut FastHashSet<InferReVar>,
    inf_dedup: &'a mut FastHashMap<InferReVar, B::Term>,
    universals: &'a mut FastIndexMap<UniversalReVar, SatLivenessUniversal<B>>,
}

#[derive(Copy, Clone)]
enum SatLivenessMode {
    Lhs,
    Rhs,
}

struct SatLivenessUniversal<B: SatBuilder> {
    var: B::Var,
    in_lhs: bool,
    in_rhs: bool,
}

impl<B: SatBuilder> SatLivenessCollector<'_, B> {
    fn translate(&mut self, node: NodeIndex) -> B::Term {
        match self.graph[node] {
            FormulaNode::True => <B::Term as SatTerm>::truthy(),
            FormulaNode::And => {
                let terms = self
                    .graph
                    .edges_directed(node, Direction::Incoming)
                    .map(|edge| self.translate(edge.source()))
                    .collect::<SmallVec<[_; 4]>>();

                match self.mode {
                    SatLivenessMode::Lhs => self.builder.join_and(terms),
                    SatLivenessMode::Rhs => self.builder.join_or(terms),
                }
            }
            FormulaNode::Existential(var) => {
                if let Some(pre_lowered) = self.inf_dedup.get(&var) {
                    return *pre_lowered;
                }

                if self.inf_cycle_set.insert(var) {
                    return <B::Term as SatTerm>::truthy();
                }

                let terms = self
                    .graph
                    .edges_directed(node, Direction::Incoming)
                    .map(|edge| self.translate(edge.source()))
                    .collect::<SmallVec<[_; 4]>>();

                self.inf_cycle_set.remove(&var);

                let out_term = match self.mode {
                    SatLivenessMode::Lhs => self.builder.join_or(terms),
                    SatLivenessMode::Rhs => self.builder.join_and(terms),
                };

                self.inf_dedup.insert(var, out_term);

                out_term
            }
            FormulaNode::Universal(var) => {
                let universal =
                    self.universals
                        .entry(var)
                        .or_insert_with(|| SatLivenessUniversal {
                            var: self.builder.fresh_var(),
                            in_lhs: false,
                            in_rhs: false,
                        });

                match self.mode {
                    SatLivenessMode::Lhs => {
                        universal.in_lhs = true;
                        universal.var.to_term()
                    }
                    SatLivenessMode::Rhs => {
                        universal.in_rhs = true;
                        !universal.var.to_term()
                    }
                }
            }
        }
    }
}
