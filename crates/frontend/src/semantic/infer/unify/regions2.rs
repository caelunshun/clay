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
//! - To assert well-formedness, we create universal implications of the form `A & B -> C`. If a
//!   universal is not part of the set of universals mentioned in the LHS and RHS, we assume it is
//!   false to leave the system as unconstrained as possible since those options would be available
//!   to us anyways.
//!
//!   Be careful with this step! For RHS-driven lowerings (see below), we have to ensure that
//!   universals mentioned in the LHS remain true rather than false.
//!
//! We can employ some shortcuts to simplify the formula before passing it to a SAT solver...
//!
//! - **LHS-driven solving:** If the number of unique universals mentioned transitively in the
//!   LHS is lower than the number of universals in the RHS, we could use the set of universals in
//!   the LHS and set all the remaining universals to `false`.
//!
//!   This works because setting additional universals could only make a falsy RHS truthy.
//!
//! - **RHS-driven solving:** Likewise, if the number of unique universals mentioned transitively in
//!   the RHS is lower than the number of universals in the LHS, we could use the set of universals
//!   in the RHS and set all the remaining universals to `true`.
//!
//!   This works because unsetting additional universals could only make a truthy LHS falsy.
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
    infer::{
        ReAndReUnifyError,
        unify::sat::{
            BruteSatBuilder, BruteSatTerm, BruteSatisfied, NopSatBuilder, NopSatTerm, SatBuilder,
            SatTerm, SatVar,
        },
    },
    syntax::{InferReVar, UniversalReVar},
};
use clay_core::{FastHashMap, FastIndexMap};
use hashbrown::hash_map;
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

    fn transform_term(&self, term: RegionFormulaTerm) -> NodeIndex {
        match term {
            RegionFormulaTerm::True => self.true_node,
            RegionFormulaTerm::Universal(var) => self.universal_nodes[var],
            RegionFormulaTerm::Existential(var) => self.existential_nodes[var],
        }
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
}

// === RegionFormulaSolver::check_implication === //

#[derive(Copy, Clone)]
enum SolveDrivingSide {
    Lhs,
    Rhs,
}

bitflags::bitflags! {
    #[derive(Copy, Clone, Default)]
    struct UniversalMentionMask: u8 {
        const IN_LHS = 1 << 0;
        const IN_RHS = 1 << 1;
    }
}

impl RegionFormulaSolver {
    fn check_implication(
        &mut self,
        lhs: NodeIndex,
        rhs: NodeIndex,
    ) -> Result<(), ReAndReUnifyError> {
        // Determine which universals are used in our terms.
        let all_universal_mentions = {
            let mut builder = NopSatBuilder::default();
            let mut all_universal_mentions =
                FastHashMap::<NodeIndex, UniversalMentionMask>::default();

            SatLivenessLower::new(
                SatLivenessLowerMode::Alive,
                &self.graph,
                &mut builder,
                |_builder, node| {
                    *all_universal_mentions.entry(node).or_default() |=
                        UniversalMentionMask::IN_LHS;
                    NopSatTerm
                },
            )
            .lower(lhs);

            SatLivenessLower::new(
                SatLivenessLowerMode::Dead,
                &self.graph,
                &mut builder,
                |_builder, node| {
                    *all_universal_mentions.entry(node).or_default() |=
                        UniversalMentionMask::IN_RHS;
                    NopSatTerm
                },
            )
            .lower(rhs);

            all_universal_mentions
        };

        let mut lhs_universal_count = 0;
        let mut rhs_universal_count = 0;

        for universal in all_universal_mentions.values() {
            if universal.contains(UniversalMentionMask::IN_LHS) {
                lhs_universal_count += 1;
            }

            if universal.contains(UniversalMentionMask::IN_RHS) {
                rhs_universal_count += 1;
            }
        }

        // Select a solving strategy
        let (driving_side, min_var_count) = {
            if lhs_universal_count < rhs_universal_count {
                (SolveDrivingSide::Lhs, lhs_universal_count)
            } else {
                (SolveDrivingSide::Rhs, rhs_universal_count)
            }
        };

        return if min_var_count < BRUTE_FORCE_VAR_LIMIT {
            self.check_implication_brute(driving_side, lhs, rhs, &all_universal_mentions)
        } else {
            // Punt to proper solver.
            todo!();
        };
    }

    fn check_implication_brute(
        &mut self,
        side: SolveDrivingSide,
        lhs: NodeIndex,
        rhs: NodeIndex,
        all_universal_mentions: &FastHashMap<NodeIndex, UniversalMentionMask>,
    ) -> Result<(), ReAndReUnifyError> {
        let mut builder = BruteSatBuilder::default();
        let mut driver_universals = FastIndexMap::default();

        // Assert that `LHS => !RHS`.
        let (lhs, rhs) = match side {
            SolveDrivingSide::Lhs => {
                let lhs = SatLivenessLower::new(
                    SatLivenessLowerMode::Alive,
                    &self.graph,
                    &mut builder,
                    |builder, node| {
                        driver_universals
                            .entry(node)
                            .or_insert_with(|| builder.fresh_var())
                            .to_term()
                    },
                )
                .lower(lhs);

                let rhs = SatLivenessLower::new(
                    SatLivenessLowerMode::Dead,
                    &self.graph,
                    &mut builder,
                    |_builder, node| match driver_universals.get(&node) {
                        Some(var) => var.to_term(),
                        None => BruteSatTerm::falsy(),
                    },
                )
                .lower(rhs);

                (lhs, rhs)
            }
            SolveDrivingSide::Rhs => {
                let rhs = SatLivenessLower::new(
                    SatLivenessLowerMode::Dead,
                    &self.graph,
                    &mut builder,
                    |builder, node| {
                        driver_universals
                            .entry(node)
                            .or_insert_with(|| builder.fresh_var())
                            .to_term()
                    },
                )
                .lower(rhs);

                let lhs = SatLivenessLower::new(
                    SatLivenessLowerMode::Alive,
                    &self.graph,
                    &mut builder,
                    |_builder, node| match driver_universals.get(&node) {
                        Some(var) => var.to_term(),
                        None => BruteSatTerm::truthy(),
                    },
                )
                .lower(lhs);

                (lhs, rhs)
            }
        };

        builder.assert_implies(lhs, !rhs);

        // Assert that the universals are well-formed.
        for (&universal_node, &universal_var) in &driver_universals {
            let universal_forced_live = SatLivenessLower::new(
                SatLivenessLowerMode::Alive,
                &self.graph,
                &mut builder,
                |_builder, node| {
                    // Assume unmentioned universals are falsy.
                    if !all_universal_mentions.contains_key(&node) {
                        return BruteSatTerm::falsy();
                    }

                    // Otherwise, attempt to resolve the universal.
                    match driver_universals.get(&node) {
                        Some(&var) => var.to_term(),
                        None => match side {
                            SolveDrivingSide::Lhs => BruteSatTerm::falsy(),
                            SolveDrivingSide::Rhs => BruteSatTerm::truthy(),
                        },
                    }
                },
            )
            .lower(universal_node);

            builder.assert_implies(universal_forced_live, universal_var.to_term());
        }

        // Solve!
        let Ok(BruteSatisfied { model }) = builder.solve() else {
            // Formula accepted.
            return Ok(());
        };

        todo!();
    }
}

// === SatLivenessLower === //

struct SatLivenessLower<'a, B, F>
where
    B: SatBuilder,
    F: FnMut(&mut B, NodeIndex) -> B::Term,
{
    mode: SatLivenessLowerMode,
    graph: &'a Graph<FormulaNode, ()>,
    builder: &'a mut B,
    lookup_forced_universal_liveness: F,
    inf_dedup_and_reentrancy: FastHashMap<InferReVar, Option<B::Term>>,
}

#[derive(Copy, Clone)]
enum SatLivenessLowerMode {
    Alive,
    Dead,
}

impl<'a, B, F> SatLivenessLower<'a, B, F>
where
    B: SatBuilder,
    F: FnMut(&mut B, NodeIndex) -> B::Term,
{
    fn new(
        mode: SatLivenessLowerMode,
        graph: &'a Graph<FormulaNode, ()>,
        builder: &'a mut B,
        lookup_forced_universal_liveness: F,
    ) -> Self {
        Self {
            mode,
            graph,
            builder,
            lookup_forced_universal_liveness,
            inf_dedup_and_reentrancy: FastHashMap::default(),
        }
    }

    /// Returns whether the term has been forced to be live (if `side == LHS`) or dead (if `side ==
    /// RHS`).
    fn lower(&mut self, node: NodeIndex) -> B::Term {
        match self.graph[node] {
            FormulaNode::True => <B::Term as SatTerm>::truthy(),
            FormulaNode::And => {
                let terms = self
                    .graph
                    .edges_directed(node, Direction::Incoming)
                    .map(|edge| self.lower(edge.source()))
                    .collect::<SmallVec<[_; 4]>>();

                match self.mode {
                    SatLivenessLowerMode::Alive => self.builder.join_and(terms),
                    SatLivenessLowerMode::Dead => self.builder.join_or(terms),
                }
            }
            FormulaNode::Existential(var) => {
                match self.inf_dedup_and_reentrancy.entry(var) {
                    hash_map::Entry::Occupied(entry) => {
                        return match entry.get() {
                            Some(pre_lowered) => *pre_lowered,
                            // This is a cycle.
                            None => <B::Term as SatTerm>::truthy(),
                        };
                    }
                    hash_map::Entry::Vacant(entry) => {
                        entry.insert_entry(None);
                    }
                }

                let terms = self
                    .graph
                    .edges_directed(node, Direction::Incoming)
                    .map(|edge| self.lower(edge.source()))
                    .collect::<SmallVec<[_; 4]>>();

                let out_term = if !terms.is_empty() {
                    match self.mode {
                        SatLivenessLowerMode::Alive => self.builder.join_or(terms),
                        SatLivenessLowerMode::Dead => self.builder.join_and(terms),
                    }
                } else {
                    <B::Term as SatTerm>::falsy()
                };

                *self.inf_dedup_and_reentrancy.get_mut(&var).unwrap() = Some(out_term);

                out_term
            }
            FormulaNode::Universal(_) => {
                let var = (self.lookup_forced_universal_liveness)(self.builder, node);

                match self.mode {
                    SatLivenessLowerMode::Alive => var,
                    SatLivenessLowerMode::Dead => !var,
                }
            }
        }
    }
}
