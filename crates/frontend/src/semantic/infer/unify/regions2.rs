//! Clay's region solver. Because the runtime also uses region solving to perform borrow-checking,
//! we make this system generic to the underlying representation of regions.
//!
//! ## Underlying Theory
//!
//! Region constraints take the form...
//!
//! ```text
//! 'lhs_1 + ... + 'lhs_n: 'rhs_1 + ... + 'rhs_n
//! ```
//!
//! ...where the `+` denotes a set of regions. For example, the source code region constraint
//! `(&'a (), &'b ()): &longer (&'c (), &'d ())` would be represented in the solver as the formula
//! `'a + 'b: 'c + 'd`.
//!
//! Given a set of precondition formulae, a new formula can be determined sound *iff* it meets the
//! following logical equation...
//!
//! ```text
//! forall<'universal_1, ..., 'universal_n>
//!     (exists<'infer_1, ..., 'infer_n>
//!         (
//!             'precond_1_rhs_1 && ... 'precond_1_rhs_n
//!             ==>
//!             'precond_1_lhs_1 && ... && 'precond_1_lhs_n
//!         )
//!         &&
//!         ...
//!         &&
//!         (
//!             'precond_m_rhs_1 && ... 'precond_m_rhs_n
//!             ==>
//!             'precond_m_lhs_1 && ... && 'precond_m_lhs_n
//!         )
//!     )
//!     ==>
//!     (exists<'infer_1, ..., 'infer_n>
//!         (
//!             'precond_1_rhs_1 && ... 'precond_1_rhs_n
//!             ==>
//!             'precond_1_lhs_1 && ... && 'precond_1_lhs_n
//!         )
//!         &&
//!         ...
//!         &&
//!         (
//!             'precond_m_rhs_1 && ... 'precond_m_rhs_n
//!             ==>
//!             'precond_m_lhs_1 && ... && 'precond_m_lhs_n
//!         )
//!         &&
//!         (
//!             'consequent_rhs_1 && ... && 'consequent_rhs_n
//!             ==>
//!             'consequent_lhs_1 && ... && 'consequent_lhs_n
//!         )
//!     )
//! ```
//!
//! A few notes...
//!
//! 1. We use two existential binders to handle inference variables rather than writing
//!    `forall<...> exists<...> precond => consequent` because, otherwise, the inference variables
//!    could be chosen to potentially make the preconditions falsy regardless of the consequent.
//!
//! 2. The special region `'gc` is treated as a logical truth.
//!
//! 3. The term `'lhs: &longer 'rhs` becomes `'rhs ==> 'lhs` where each variable denotes the
//!    liveness of a given region. This may seem unintuitive until you consider an example like
//!    `'lhs: &longer 'gc`. `'lhs` should always be alive so this should be read as `true ==> 'lhs`.
//!
//! ## Simple Solving
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
//! t_1 -> ?1
//! f_1 -> ?1
//!
//! ...
//!
//! t_n -> ?n
//! f_n -> ?n
//!
//! ?1 && ... && ?n -> rhs
//! ```
//!
//! ...where `?x` denotes an inference variable and the remaining variables are universals.
//!
//! Likewise, consider the following input—this time, exponential in the number of ways in which
//! it could be made falsy...
//!
//! ```text
//! t_1 + f_1 -> ?a
//! ...
//! t_n + f_n -> ?a
//!
//! lhs -> ?a
//! ```
//!
//! Unfortunately, one can reduce a 3-SAT problem into our solver like so...
//!
//! ```text
//! (A || !B || C) && (!A || !B || C)
//!
//! // Creates the following universals
//! A_t
//! B_t
//! C_t
//!
//! A_f
//! B_f
//! C_f
//!
//! // Disjunction
//! A_t + A_f -> false_if_not_both
//! B_t + B_f -> false_if_not_both
//! C_t + C_f -> false_if_not_both
//!
//! A_t -> ?true_if_at_least_one_A
//! A_f -> ?true_if_at_least_one_A
//! B_t -> ?true_if_at_least_one_B
//! B_f -> ?true_if_at_least_one_B
//! C_t -> ?true_if_at_least_one_C
//! C_f -> ?true_if_at_least_one_C
//! ?true_if_at_least_one_A + ?true_if_at_least_one_B + ?true_if_at_least_one_C -> ?true_if_non_empty
//!
//! // 3-SAT triples
//! A_t -> ?term_1_truthy
//! B_f -> ?term_1_truthy
//! C_t -> ?term_1_truthy
//!
//! A_f -> ?term_2_truthy
//! B_f -> ?term_2_truthy
//! C_t -> ?term_2_truthy
//!
//! ?term_1_truthy + ?term_2_truthy -> ?terms_truthy
//!
//! // Final consequent (all terms above were preconditions)
//! ?true_if_non_empty + ?terms_truthy -> false_if_not_both
//! ```
//!
//! The 3-SAT formula is satisfiable *iff* we can come up with a set of universals that cause a
//! contradiction in our formula:
//!
//! - If we try to select `A_t` and `A_f`, we'll be forced to enable the `false_if_not_both`
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
//!     fn new() -> Self {
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
//!     'false_if_not_both:
//!         &longer (&'a_t (), &'a_f ()) +  // a_t + a_f -> false_if_not_both
//!         &longer (&'b_t (), &'b_f ()) +  // b_t + b_f -> false_if_not_both
//!         &longer (&'c_t (), &'c_f ()),   // c_t + c_f -> false_if_not_both
//! >() {
//!     let true_if_at_least_one_a = Binder::new();
//!     true_if_at_least_one_a.longer::<'a_t>();  // 'a_t -> ?true_if_at_least_one_a
//!     true_if_at_least_one_a.longer::<'a_f>();  // 'a_f -> ?true_if_at_least_one_a
//!
//!     let true_if_at_least_one_b = Binder::new();
//!     true_if_at_least_one_b.longer::<'b_t>();  // 'b_t -> ?true_if_at_least_one_b
//!     true_if_at_least_one_b.longer::<'b_f>();  // 'b_f -> ?true_if_at_least_one_b
//!
//!     let true_if_at_least_one_c = Binder::new();
//!     true_if_at_least_one_c.longer::<'c_t>();  // 'c_t -> ?true_if_at_least_one_c
//!     true_if_at_least_one_c.longer::<'c_f>();  // 'c_f -> ?true_if_at_least_one_c
//!
//!     let term_1_truthy = Binder::new();
//!     term_1_truthy.longer::<'a_t>();  // 'a_t -> ?term_1_truthy
//!     term_1_truthy.longer::<'b_f>();  // 'b_f -> ?term_1_truthy
//!     term_1_truthy.longer::<'c_t>();  // 'c_t -> ?term_1_truthy
//!
//!     let term_2_truthy = Binder::new();
//!     term_2_truthy.longer::<'a_f>();  // 'a_f -> ?term_2_truthy
//!     term_2_truthy.longer::<'b_f>();  // 'b_f -> ?term_2_truthy
//!     term_2_truthy.longer::<'c_t>();  // 'c_t -> ?term_2_truthy
//!
//!     // ?true_if_at_least_one_a + ?true_if_at_least_one_b + ?true_if_at_least_one_c +
//!     //    ?term_1_truthy + ?term_2_truthy -> 'false_if_not_both
//!     assert_all_imply::<'_, '_, '_, '_, '_, 'false_if_not_both>(
//!         true_if_at_least_one_a,
//!         true_if_at_least_one_b,
//!         true_if_at_least_one_c,
//!         term_1_truthy,
//!         term_2_truthy,
//!     );
//! }
//! ```
//!
//! Using just `&longer <type>` universal constraints, one can reduce SAT-3 to Clay. This is all
//! very unfortunate!
