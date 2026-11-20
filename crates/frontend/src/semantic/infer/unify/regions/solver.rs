use crate::{
    base::ErrorGuaranteed,
    bool_enum,
    semantic::{
        infer::ReAndReUnifyError,
        syntax::{InferReVar, Re, UniversalReVar},
    },
};
use index_vec::IndexVec;
use petgraph::{Graph, graph::NodeIndex};
use smallvec::SmallVec;

// === RegionFormulaSolver === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum RegionFormulaTerm {
    True,
    Universal(UniversalReVar),
    Existential(InferReVar),
}

impl RegionFormulaTerm {
    pub fn from_re(re: Re) -> Result<Self, ErrorGuaranteed> {
        match re {
            Re::Gc => Ok(RegionFormulaTerm::True),
            Re::InferVar(var) => Ok(RegionFormulaTerm::Existential(var)),
            Re::UniversalVar(var) => Ok(RegionFormulaTerm::Universal(var)),
            Re::Error(err) => Err(err),
            Re::HrtbVar(_) => unreachable!(),
        }
    }

    pub fn to_re(self) -> Re {
        match self {
            RegionFormulaTerm::True => Re::Gc,
            RegionFormulaTerm::Universal(var) => Re::UniversalVar(var),
            RegionFormulaTerm::Existential(var) => Re::InferVar(var),
        }
    }
}

#[derive(Clone)]
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

bool_enum! {
    enum ShouldValidate {
        true => Yes;
        false => No;
    }
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
        self.push_common(ShouldValidate::No, lhs, rhs).unwrap();
    }

    pub fn push_checked(
        &mut self,
        lhs: impl IntoIterator<Item = RegionFormulaTerm>,
        rhs: impl IntoIterator<Item = RegionFormulaTerm>,
    ) -> Result<(), ReAndReUnifyError> {
        self.push_common(ShouldValidate::Yes, lhs, rhs)
    }

    fn push_common(
        &mut self,
        should_validate: ShouldValidate,
        lhs: impl IntoIterator<Item = RegionFormulaTerm>,
        rhs: impl IntoIterator<Item = RegionFormulaTerm>,
    ) -> Result<(), ReAndReUnifyError> {
        let rhs = rhs
            .into_iter()
            .filter(|term| !matches!(term, RegionFormulaTerm::True))
            .map(|term| self.transform_term(term))
            .collect::<SmallVec<[NodeIndex; 4]>>();

        if rhs.is_empty() {
            return Ok(());
        }

        let lhs = self.lower_lhs(lhs);

        if should_validate.is_truthy() {
            // No need to push our edges before ensuring that all RHS terms pass because additional
            // edges cannot contribute to whether this condition passes.

            for &rhs in &rhs {
                #[cfg(test)]
                {
                    let res_sat = self.check_implication_sat(lhs, rhs);
                    let res_smt = self.check_implication_smt(lhs, rhs);

                    assert!(
                        res_sat.is_ok() == res_smt.is_ok(),
                        "mismatch between solver strategies: SAT {}, SMT {}",
                        match res_sat {
                            Ok(_) => "accepted",
                            Err(_) => "rejected",
                        },
                        match res_smt {
                            Ok(_) => "accepted",
                            Err(_) => "rejected",
                        }
                    );

                    () = res_sat?;
                }

                #[cfg(not(test))]
                {
                    self.check_implication_sat(lhs, rhs)?;
                }
            }
        }

        for &rhs in &rhs {
            self.graph.add_edge(lhs, rhs, ());
        }

        Ok(())
    }

    fn transform_term(&self, term: RegionFormulaTerm) -> NodeIndex {
        match term {
            RegionFormulaTerm::True => self.true_node,
            RegionFormulaTerm::Universal(var) => self.universal_nodes[var],
            RegionFormulaTerm::Existential(var) => self.existential_nodes[var],
        }
    }

    fn lower_lhs(&mut self, lhs: impl IntoIterator<Item = RegionFormulaTerm>) -> NodeIndex {
        let mut lhs = lhs
            .into_iter()
            .filter(|term| !matches!(term, RegionFormulaTerm::True))
            .fuse();

        match (lhs.next(), lhs.next()) {
            (None, None) => {
                // Vacuous
                return self.true_node;
            }
            (Some(node), None) => self.transform_term(node),
            (Some(first), Some(second)) => {
                let joiner = self.graph.add_node(FormulaNode::And);

                for lhs in [first, second].into_iter().chain(lhs) {
                    self.graph.add_edge(self.transform_term(lhs), joiner, ());
                }

                joiner
            }
            (None, Some(_)) => unreachable!(),
        }
    }
}

// === SAT-based solver === //

mod solver_sat {
    use super::*;
    use crate::semantic::syntax::RelationMode;
    use clay_core::FastHashMap;
    use hashbrown::hash_map;
    use petgraph::{Direction, algo::TarjanScc, visit::EdgeRef};
    use std::rc::Rc;
    use z3::{SatResult, Solver, ast::Bool};

    impl RegionFormulaSolver {
        pub(super) fn check_implication_sat(
            &self,
            lhs: NodeIndex,
            rhs: NodeIndex,
        ) -> Result<(), ReAndReUnifyError> {
            let solver = Solver::new();
            let mut model_vars = ModelVarSet::new(&solver, self, lhs, rhs);

            match self.graph[rhs] {
                FormulaNode::Universal(_) => {
                    // If the universals are sound, see if we can show `lhs` but not show `rhs`.
                    let cond_1 = model_vars.are_universals_sound(ConclusionMode::ExcludeConclusion);
                    let cond_2 = model_vars.is_alive(lhs, ConclusionMode::ExcludeConclusion);
                    let cond_3 = model_vars.is_alive(rhs, ConclusionMode::ExcludeConclusion);

                    solver.assert(cond_1);
                    solver.assert(cond_2);
                    solver.assert(!cond_3);
                }
                FormulaNode::Existential(_) => {
                    // If the universals are sound and the `lhs` is forced to be true without
                    // forcing the `rhs` to be true, try to force it to be true and see whether the
                    // universals are still well-formed. If they're not, this tells us that the
                    // `rhs` must be false, giving us a set of universals which disprove our
                    // conclusion.

                    let cond_1 = model_vars.are_universals_sound(ConclusionMode::ExcludeConclusion);
                    let cond_2 = model_vars.is_alive(lhs, ConclusionMode::ExcludeConclusion);
                    let cond_3 = model_vars.are_universals_sound(ConclusionMode::IncludeConclusion);

                    solver.assert(cond_1);
                    solver.assert(cond_2);
                    solver.assert(!cond_3);
                }
                FormulaNode::And | FormulaNode::True => {
                    unreachable!()
                }
            }

            // println!("{solver}");

            // TODO: create actual errors
            match solver.check() {
                SatResult::Unsat => Ok(()),
                SatResult::Sat => Err(ReAndReUnifyError {
                    lhs: Re::Gc,
                    rhs: Re::Gc,
                    mode: RelationMode::Equate,
                    causes: Vec::new(),
                }),
                SatResult::Unknown => unreachable!(),
            }
        }
    }

    struct ModelVarSet<'a> {
        solver: &'a Solver,
        formulas: &'a RegionFormulaSolver,
        universal_vars: Rc<IndexVec<UniversalReVar, Bool>>,
        existential_vars_pre: IndexVec<InferReVar, Option<Bool>>,
        existential_vars_post: IndexVec<InferReVar, Option<Bool>>,
        curr_existential_lower_cache: FastHashMap<InferReVar, Option<Bool>>,
        impl_lhs: NodeIndex,
        impl_rhs: NodeIndex,
        is_populating: bool,
    }

    bool_enum! {
        enum ConclusionMode {
            true => IncludeConclusion;
            false => ExcludeConclusion;
        }
    }

    impl<'a> ModelVarSet<'a> {
        fn new(
            solver: &'a Solver,
            formulas: &'a RegionFormulaSolver,
            impl_lhs: NodeIndex,
            impl_rhs: NodeIndex,
        ) -> Self {
            let universal_vars = formulas
                .universal_nodes
                .indices()
                .map(|var| Bool::new_const(format!("'u{}", var.index())))
                .collect::<IndexVec<UniversalReVar, _>>();

            let existential_vars = formulas
                .existential_nodes
                .indices()
                .map(|_| None)
                .collect::<IndexVec<InferReVar, _>>();

            let mut this = Self {
                solver,
                formulas,
                universal_vars: Rc::new(universal_vars),
                existential_vars_pre: existential_vars.clone(),
                existential_vars_post: existential_vars,
                curr_existential_lower_cache: FastHashMap::default(),
                impl_lhs,
                impl_rhs,
                is_populating: false,
            };

            this.populate_all_existentials();

            this
        }

        fn populate_all_existentials(&mut self) {
            let mut tarjan_scc = TarjanScc::new();

            // Create a subgraph with only edges connecting one existential to another implicand.
            let graph = &self.formulas.graph;
            let mut sub_graph = graph.filter_map(
                |_, node| {
                    Some(match *node {
                        FormulaNode::Existential(var) => Some(var),
                        FormulaNode::True | FormulaNode::Universal(_) | FormulaNode::And => None,
                    })
                },
                |edge, _| {
                    let (edge_src, edge_dst) = graph.edge_endpoints(edge).unwrap();

                    match (&graph[edge_src], graph[edge_dst]) {
                        (FormulaNode::Existential(_) | FormulaNode::And, _)
                        | (_, FormulaNode::Existential(_) | FormulaNode::And) => Some(()),
                        _ => None,
                    }
                },
            );

            // Populate `existential_vars_pre`
            tarjan_scc.run(&sub_graph, |scc| {
                self.curr_existential_lower_cache.clear();

                for &var in scc {
                    let FormulaNode::Existential(var) = graph[var] else {
                        continue;
                    };

                    self.populate_existential(var, ConclusionMode::ExcludeConclusion);
                }
            });

            // Populate `existential_vars_post`
            match (graph[self.impl_lhs], graph[self.impl_rhs]) {
                (FormulaNode::And | FormulaNode::Existential(_), FormulaNode::Existential(_)) => {
                    sub_graph.add_edge(self.impl_lhs, self.impl_rhs, ());
                }
                (_, FormulaNode::And) => unreachable!(),
                _ => {
                    // (edge not included in subgraph)
                }
            }

            tarjan_scc.run(&sub_graph, |scc| {
                self.curr_existential_lower_cache.clear();

                for &var in scc {
                    let FormulaNode::Existential(var) = graph[var] else {
                        continue;
                    };

                    self.populate_existential(var, ConclusionMode::IncludeConclusion);
                }
            });
        }

        fn populate_existential(&mut self, var: InferReVar, conclusion_mode: ConclusionMode) {
            debug_assert!(self.curr_existential_lower_cache.is_empty());

            let term = Bool::new_const(format!(
                "'i{}_{}",
                var.index(),
                match conclusion_mode {
                    ConclusionMode::ExcludeConclusion => "pre",
                    ConclusionMode::IncludeConclusion => "post",
                }
            ));

            self.is_populating = true;
            let raw_term = self.is_alive(self.formulas.existential_nodes[var], conclusion_mode);
            self.is_populating = false;

            self.solver.assert(term.eq(raw_term));

            match conclusion_mode {
                ConclusionMode::ExcludeConclusion => {
                    self.existential_vars_pre[var] = Some(term);
                }
                ConclusionMode::IncludeConclusion => {
                    self.existential_vars_post[var] = Some(term);
                }
            }

            self.curr_existential_lower_cache.clear();
        }

        fn are_universals_sound(&mut self, conclusion_mode: ConclusionMode) -> Bool {
            Bool::and(
                &self
                    .universal_vars
                    .clone()
                    .iter()
                    .zip(&self.formulas.universal_nodes)
                    .map(|(universal_var, &universal_node)| {
                        self.is_node_implied_uncached(universal_node, conclusion_mode)
                            .implies(universal_var)
                    })
                    .collect::<Vec<_>>(),
            )
        }

        fn is_alive(&mut self, node: NodeIndex, conclusion_mode: ConclusionMode) -> Bool {
            self.is_alive_reentrant(node, conclusion_mode).unwrap()
        }

        fn is_alive_reentrant(
            &mut self,
            node: NodeIndex,
            conclusion_mode: ConclusionMode,
        ) -> Option<Bool> {
            match self.formulas.graph[node] {
                FormulaNode::And => Some(Bool::and(
                    &self
                        .formulas
                        .graph
                        .edges_directed(node, Direction::Incoming)
                        .map(|edge| {
                            self.is_alive_reentrant(edge.source(), conclusion_mode)
                                .unwrap_or(Bool::from_bool(false))
                        })
                        .collect::<Vec<_>>(),
                )),
                FormulaNode::True => Some(Bool::from_bool(true)),
                FormulaNode::Universal(var) => Some(self.universal_vars[var].clone()),
                FormulaNode::Existential(var) => {
                    // See whether we've finished the term completely before.
                    let finished_cache = match conclusion_mode {
                        ConclusionMode::ExcludeConclusion => &self.existential_vars_pre,
                        ConclusionMode::IncludeConclusion => &self.existential_vars_post,
                    };

                    if let Some(term) = &finished_cache[var] {
                        return Some(term.clone());
                    }

                    // Otherwise, lower it with reentrancy. This should only happen during
                    // population if we hit another term in the strongly connected component.
                    debug_assert!(self.is_populating);

                    match self.curr_existential_lower_cache.entry(var) {
                        hash_map::Entry::Occupied(entry) => {
                            return match entry.get() {
                                Some(already_lowered_locally) => {
                                    Some(already_lowered_locally.clone())
                                }
                                None => {
                                    // Reentrant!
                                    None
                                }
                            };
                        }
                        hash_map::Entry::Vacant(entry) => {
                            entry.insert_entry(None);
                        }
                    }

                    let term = self.is_node_implied_uncached(node, conclusion_mode);

                    self.curr_existential_lower_cache
                        .insert(var, Some(term.clone()));

                    Some(term)
                }
            }
        }

        fn is_node_implied_uncached(
            &mut self,
            node: NodeIndex,
            conclusion_mode: ConclusionMode,
        ) -> Bool {
            Bool::or(
                &self
                    .formulas
                    .graph
                    .edges_directed(node, Direction::Incoming)
                    .map(|edge| edge.source())
                    .chain(
                        (conclusion_mode.is_truthy() && node == self.impl_rhs)
                            .then_some(self.impl_lhs),
                    )
                    .filter_map(|src| self.is_alive_reentrant(src, conclusion_mode))
                    .collect::<Vec<_>>(),
            )
        }
    }
}

// === SMT-based solver === //

#[cfg(test)]
mod solver_smt {
    use super::*;
    use crate::semantic::syntax::{Re, RelationMode};
    use index_vec::IndexSlice;
    use petgraph::visit::EdgeRef;
    use z3::{
        SatResult, Solver,
        ast::{Ast, Bool, exists_const, forall_const},
    };

    impl RegionFormulaSolver {
        pub(super) fn check_implication_smt(
            &self,
            lhs: NodeIndex,
            rhs: NodeIndex,
        ) -> Result<(), ReAndReUnifyError> {
            // Create the required terms
            let universals = self
                .universal_nodes
                .indices()
                .map(|idx| Bool::new_const(format!("'u{idx:?}")))
                .collect::<IndexVec<UniversalReVar, _>>();

            let existentials = self
                .existential_nodes
                .indices()
                .map(|idx| Bool::new_const(format!("'i{idx:?}")))
                .collect::<IndexVec<InferReVar, _>>();

            let precond_wf = self
                .graph
                .edge_references()
                // Filter to only include implications
                .filter(|edge| !matches!(self.graph[edge.target()], FormulaNode::And))
                .map(|edge| {
                    let lhs = is_term_truthy(self, &universals, &existentials, edge.source());
                    let rhs = is_term_truthy(self, &universals, &existentials, edge.target());

                    lhs.implies(rhs)
                })
                .collect::<Vec<_>>();

            let precond_wf = Bool::and(&precond_wf);

            let post_wf = {
                let lhs = is_term_truthy(self, &universals, &existentials, lhs);
                let rhs = is_term_truthy(self, &universals, &existentials, rhs);

                (&precond_wf) & lhs.implies(rhs)
            };

            // Construct the full formula
            let full = {
                let full_lhs = exists_const(
                    &existentials
                        .iter()
                        .map(|v| v as &dyn Ast)
                        .collect::<Vec<_>>(),
                    &[],
                    &precond_wf,
                );

                let full_rhs = exists_const(
                    &existentials
                        .iter()
                        .map(|v| v as &dyn Ast)
                        .collect::<Vec<_>>(),
                    &[],
                    &post_wf,
                );

                forall_const(
                    &universals.iter().map(|v| v as &dyn Ast).collect::<Vec<_>>(),
                    &[],
                    &full_lhs.implies(full_rhs),
                )
            };

            // Solve it!
            let solver = Solver::new();

            solver.assert(full);

            match solver.check() {
                SatResult::Sat => Ok(()),
                // TODO: update
                SatResult::Unsat => Err(ReAndReUnifyError {
                    lhs: Re::Gc,
                    rhs: Re::Gc,
                    mode: RelationMode::Equate,
                    causes: Vec::new(),
                }),
                SatResult::Unknown => unreachable!(),
            }
        }
    }

    fn is_term_truthy(
        solver: &RegionFormulaSolver,
        universals: &IndexSlice<UniversalReVar, [Bool]>,
        existentials: &IndexSlice<InferReVar, [Bool]>,
        node: NodeIndex,
    ) -> Bool {
        match solver.graph[node] {
            FormulaNode::And => {
                let children = solver
                    .graph
                    .edges_directed(node, petgraph::Direction::Incoming)
                    .map(|edge| is_term_truthy(solver, universals, existentials, edge.source()))
                    .collect::<Vec<_>>();

                Bool::and(&children)
            }
            FormulaNode::True => Bool::from_bool(true),
            FormulaNode::Universal(var) => universals[var].clone(),
            FormulaNode::Existential(var) => existentials[var].clone(),
        }
    }
}

// === Tests === //

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::format::{SimpleListFormatGlue, format_list};
    use core::fmt;
    use rand::{Rng, RngExt, SeedableRng as _, rngs::Xoshiro256PlusPlus};

    #[test]
    fn prop_test() {
        let mut rng = Xoshiro256PlusPlus::seed_from_u64(4);

        for i in 0..1000 {
            println!("// >>>>>>>>> Test {i}");

            // Not sure whether `usize` has platform-dependent behavior for `rand`.
            let universal_count = rng.random_range::<u32, _>(1..=4);
            let existential_count = rng.random_range::<u32, _>(1..=4);

            println!(
                "let mut solver = RegionFormulaSolver::new({universal_count}, {existential_count});"
            );
            println!();

            let mut solver =
                RegionFormulaSolver::new(universal_count as usize, existential_count as usize);

            // Setup axioms
            for _ in 0..rng.random_range(0..=8) {
                let lhs = (0..rng.random_range(1..=3))
                    .map(|_| random_term(&mut rng, universal_count, existential_count))
                    .collect::<SmallVec<[_; 3]>>();

                let rhs = random_term(&mut rng, universal_count, existential_count);

                println!(
                    "// AXIOM: {} -> {}",
                    format_list(
                        lhs.iter().copied().map(format_term_comment),
                        SimpleListFormatGlue::new_delimited(" ^ ")
                    ),
                    format_term_comment(rhs),
                );

                println!(
                    "solver.push_axiom([{}], [{}]);",
                    format_list(
                        lhs.iter().copied().map(format_term_code),
                        SimpleListFormatGlue::COMMA_LIST
                    ),
                    format_term_code(rhs),
                );
                println!();

                solver.push_axiom(lhs.iter().copied(), [rhs]);
            }

            // Check equations
            for _ in 0..8 {
                let lhs = (0..rng.random_range(1..=3))
                    .map(|_| random_term(&mut rng, universal_count, existential_count))
                    .collect::<SmallVec<[_; 3]>>();

                let rhs = random_term(&mut rng, universal_count, existential_count);

                println!(
                    "// ASSERTION: {} -> {}",
                    format_list(
                        lhs.iter().copied().map(format_term_comment),
                        SimpleListFormatGlue::new_delimited(" ^ ")
                    ),
                    format_term_comment(rhs),
                );
                println!(
                    "_ = solver.push_checked([{}], [{}]);",
                    format_list(
                        lhs.iter().copied().map(format_term_code),
                        SimpleListFormatGlue::COMMA_LIST
                    ),
                    format_term_code(rhs),
                );
                println!();

                _ = solver.push_checked(lhs, [rhs]);
            }
        }
    }

    fn random_term(
        mut rng: impl Rng,
        universal_count: u32,
        existential_count: u32,
    ) -> RegionFormulaTerm {
        match rng.random_range(0..=2) {
            0 => RegionFormulaTerm::Universal(UniversalReVar::from_usize(
                rng.random_range::<u32, _>(0..universal_count) as usize,
            )),
            1 => RegionFormulaTerm::Existential(InferReVar::from_usize(
                rng.random_range::<u32, _>(0..existential_count) as usize,
            )),
            2 => RegionFormulaTerm::True,
            _ => unreachable!(),
        }
    }

    fn format_term_comment(term: RegionFormulaTerm) -> impl fmt::Display {
        fmt::from_fn(move |f| {
            match term {
                RegionFormulaTerm::True => {
                    f.write_str("T")?;
                }
                RegionFormulaTerm::Universal(var) => {
                    write!(f, "'u{}", var.index())?;
                }
                RegionFormulaTerm::Existential(var) => {
                    write!(f, "'i{}", var.index())?;
                }
            }

            Ok(())
        })
    }

    fn format_term_code(term: RegionFormulaTerm) -> impl fmt::Display {
        fmt::from_fn(move |f| {
            f.write_str("RegionFormulaTerm::")?;

            match term {
                RegionFormulaTerm::True => {
                    f.write_str("True")?;
                }
                RegionFormulaTerm::Universal(var) => {
                    write!(f, "Universal(UniversalReVar::from_usize({}))", var.index())?;
                }
                RegionFormulaTerm::Existential(var) => {
                    write!(f, "Existential(InferReVar::from_usize({}))", var.index())?;
                }
            }

            Ok(())
        })
    }

    #[test]
    fn simple_infer() {
        let mut solver = RegionFormulaSolver::new(0, 2);
        _ = solver.push_checked(
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(1))],
        );
    }

    #[test]
    fn generated_1() {
        let mut solver = RegionFormulaSolver::new(1, 1);

        // AXIOM: 'i0 -> 'u0
        solver.push_axiom(
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(0))],
        );

        // ASSERTION: 'u0 -> 'i0
        _ = solver.push_checked(
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(0))],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
        );
    }

    #[test]
    fn generated_2() {
        let mut solver = RegionFormulaSolver::new(1, 1);

        // AXIOM: 'i0 ^ 'u0 -> 'u0
        _ = solver.push_axiom(
            [
                RegionFormulaTerm::Existential(InferReVar::from_usize(0)),
                RegionFormulaTerm::Universal(UniversalReVar::from_usize(0)),
            ],
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(0))],
        );

        // ASSERTION: 'u0 -> 'i0
        _ = solver.push_checked(
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(0))],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
        );
    }

    #[test]
    fn generated_3() {
        let mut solver = RegionFormulaSolver::new(1, 1);

        // AXIOM: 'i0 ^ 'u0 -> 'u0
        _ = solver.push_axiom(
            [
                RegionFormulaTerm::Existential(InferReVar::from_usize(0)),
                RegionFormulaTerm::Universal(UniversalReVar::from_usize(0)),
            ],
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(0))],
        );

        // AXIOM: T -> 'i0
        _ = solver.push_axiom(
            [RegionFormulaTerm::True],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
        );

        // ASSERTION: 'i0 -> 'i0
        _ = solver.push_checked(
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
        );
    }

    #[test]
    fn generated_4() {
        let mut solver = RegionFormulaSolver::new(1, 1);

        // ASSERTION: 'i0 -> 'i0
        _ = solver.push_axiom(
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
        );

        // ASSERTION: 'i0 -> 'u0
        _ = solver.push_checked(
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(0))],
        );
    }

    #[test]
    fn generated_5() {
        let mut solver = RegionFormulaSolver::new(2, 1);

        // AXIOM: 'u0 -> 'i0
        solver.push_axiom(
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(0))],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
        );

        // ASSERTION: 'u0 ^ 'i0 -> 'u1
        _ = solver.push_checked(
            [
                RegionFormulaTerm::Universal(UniversalReVar::from_usize(0)),
                RegionFormulaTerm::Existential(InferReVar::from_usize(0)),
            ],
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(1))],
        );
    }

    #[test]
    fn generated_6() {
        let mut solver = RegionFormulaSolver::new(1, 1);

        // AXIOM: 'i0 -> 'u0
        solver.push_axiom(
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(0))],
        );

        // AXIOM: 'i0 -> 'i0
        solver.push_axiom(
            [
                RegionFormulaTerm::Existential(InferReVar::from_usize(0)),
                RegionFormulaTerm::Existential(InferReVar::from_usize(0)),
            ],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
        );

        // ASSERTION: T -> 'i0
        _ = solver.push_checked(
            [RegionFormulaTerm::True],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
        );
    }

    #[test]
    fn generated_7() {
        let mut solver = RegionFormulaSolver::new(2, 1);

        // ASSERTION: 'i0 ^ 'u0 -> 'i0
        _ = solver.push_checked(
            [
                RegionFormulaTerm::Existential(InferReVar::from_usize(0)),
                RegionFormulaTerm::Universal(UniversalReVar::from_usize(0)),
            ],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
        );

        // ASSERTION: 'i0 -> 'u1
        _ = solver.push_checked(
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(1))],
        );
    }

    #[test]
    fn generated_8() {
        let mut solver = RegionFormulaSolver::new(2, 3);

        // AXIOM: 'u1 -> 'i2
        solver.push_axiom(
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(1))],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(2))],
        );

        // AXIOM: 'i1 -> 'u0
        solver.push_axiom(
            [RegionFormulaTerm::Existential(InferReVar::from_usize(1))],
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(0))],
        );

        // AXIOM: 'i2 ^ 'i0 -> 'u0
        _ = solver.push_axiom(
            [
                RegionFormulaTerm::Existential(InferReVar::from_usize(2)),
                RegionFormulaTerm::Existential(InferReVar::from_usize(0)),
            ],
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(0))],
        );

        // AXIOM: 'i1 -> 'i2
        _ = solver.push_axiom(
            [RegionFormulaTerm::Existential(InferReVar::from_usize(1))],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(2))],
        );

        // ASSERTION: 'i2 -> 'i1
        _ = solver.push_checked(
            [RegionFormulaTerm::Existential(InferReVar::from_usize(2))],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(1))],
        );
    }

    #[test]
    fn generated_9() {
        let mut solver = RegionFormulaSolver::new(1, 1);

        // AXIOM: 'i0 -> 'u0
        solver.push_axiom(
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(0))],
        );

        // AXIOM: 'u0 -> 'i0
        _ = solver.push_axiom(
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(0))],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
        );

        // ASSERTION: T -> 'i0
        _ = solver.push_checked(
            [RegionFormulaTerm::True],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
        );
    }

    #[test]
    fn generated_10() {
        let mut solver = RegionFormulaSolver::new(1, 4);

        // AXIOM: 'i2 -> 'i3
        solver.push_axiom(
            [RegionFormulaTerm::Existential(InferReVar::from_usize(2))],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(3))],
        );

        // AXIOM: T -> 'i0
        solver.push_axiom(
            [RegionFormulaTerm::True],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
        );

        // AXIOM: 'i2 -> 'i1
        _ = solver.push_axiom(
            [RegionFormulaTerm::Existential(InferReVar::from_usize(2))],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(1))],
        );

        // AXIOM: 'i1 -> 'u0
        _ = solver.push_axiom(
            [RegionFormulaTerm::Existential(InferReVar::from_usize(1))],
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(0))],
        );

        // AXIOM: 'i2 ^ 'i3 -> 'i1
        _ = solver.push_axiom(
            [
                RegionFormulaTerm::Existential(InferReVar::from_usize(2)),
                RegionFormulaTerm::Existential(InferReVar::from_usize(3)),
            ],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(1))],
        );

        // AXIOM: 'i0 -> 'i3
        _ = solver.push_axiom(
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(3))],
        );

        // ASSERTION: 'i3 -> 'i2
        _ = solver.push_checked(
            [RegionFormulaTerm::Existential(InferReVar::from_usize(3))],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(2))],
        );
    }
}
