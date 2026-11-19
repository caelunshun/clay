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
    use crate::semantic::{
        infer::unify::regions::sat::{
            BruteSatBuilder, BruteSatisfied, SatBuilder, SatTerm, SatVar as _,
        },
        syntax::{Re, RelationMode},
    };
    use clay_core::{FastHashMap, FastIndexMap};
    use hashbrown::hash_map;
    use petgraph::{Direction, visit::EdgeRef as _};

    const BRUTE_FORCE_VAR_LIMIT: u32 = 10;

    impl RegionFormulaSolver {
        pub(super) fn check_implication_sat(
            &self,
            lhs: NodeIndex,
            rhs: NodeIndex,
        ) -> Result<(), ReAndReUnifyError> {
            let mut builder = BruteSatBuilder::default();
            let mut universals = FastIndexMap::default();

            let lhs_forced_live = SatForcedLiveLowerer {
                state: SatForceLowererState::new(&self.graph, &mut builder),
                universals: &mut universals,
            }
            .lower_naturally(lhs);

            let rhs_forced_dead = SatForcedDeadLowerer {
                state: SatForceLowererState::new(&self.graph, &mut builder),
                universals: &mut universals,
            }
            .lower_naturally(rhs);

            if universals.len() > BRUTE_FORCE_VAR_LIMIT as usize {
                todo!();
            }

            for (&universal_node, &universal_var) in &universals {
                let needs_to_be_live = SatUniversalForcedTrueByWf {
                    state: SatForceLowererState::new(&self.graph, &mut builder),
                    universals: &universals,
                }
                .lower_naturally(universal_node);

                builder.assert_implies(needs_to_be_live, universal_var.to_term());
            }

            builder.assert_and([lhs_forced_live, rhs_forced_dead]);

            match builder.solve() {
                Ok(BruteSatisfied { model }) => {
                    // TODO: update
                    Err(ReAndReUnifyError {
                        lhs: Re::Gc,
                        rhs: Re::Gc,
                        mode: RelationMode::Equate,
                        causes: Vec::new(),
                    })
                }
                Err(_) => Ok(()),
            }
        }
    }

    #[derive(Copy, Clone)]
    enum SatForceLowererMode {
        Alive,
        Dead,
    }

    struct SatForceLowererState<'a, B: 'a + SatBuilder> {
        graph: &'a Graph<FormulaNode, ()>,
        builder: &'a mut B,
        inf_dedup_and_reentrancy: FastHashMap<NodeIndex, Option<B::Term>>,
    }

    impl<'a, B: SatBuilder> SatForceLowererState<'a, B> {
        fn new(graph: &'a Graph<FormulaNode, ()>, builder: &'a mut B) -> Self {
            Self {
                graph,
                builder,
                inf_dedup_and_reentrancy: FastHashMap::default(),
            }
        }
    }

    trait SatForceLowerer<'a, B: 'a + SatBuilder> {
        fn mode(&self) -> SatForceLowererMode;

        fn state<'b>(&'b self) -> &'b SatForceLowererState<'a, B>
        where
            'a: 'b;

        fn state_mut<'b>(&'b mut self) -> &'b mut SatForceLowererState<'a, B>
        where
            'a: 'b;

        fn graph(&self) -> &'a Graph<FormulaNode, ()> {
            self.state().graph
        }

        fn builder_mut<'b>(&'b mut self) -> &'b mut B
        where
            'a: 'b,
        {
            self.state_mut().builder
        }

        fn lower_naturally(&mut self, node: NodeIndex) -> B::Term {
            match self.state().graph[node] {
                FormulaNode::True => self.lower_true(),
                FormulaNode::And => self.lower_as_conjunction(node),
                FormulaNode::Existential(_) => self.lower_as_existential(node),
                FormulaNode::Universal(_) => self.lower_as_universal(node),
            }
        }

        fn lower_true(&mut self) -> B::Term {
            match self.mode() {
                SatForceLowererMode::Alive => <B::Term as SatTerm>::truthy(),
                SatForceLowererMode::Dead => <B::Term as SatTerm>::falsy(),
            }
        }

        fn lower_as_conjunction(&mut self, node: NodeIndex) -> B::Term {
            let terms = self
                .graph()
                .edges_directed(node, Direction::Incoming)
                .map(|edge| self.lower_naturally(edge.source()))
                .collect::<SmallVec<[_; 4]>>();

            debug_assert!(!terms.is_empty());

            match self.mode() {
                SatForceLowererMode::Alive => self.builder_mut().join_and(terms),
                SatForceLowererMode::Dead => self.builder_mut().join_or(terms),
            }
        }

        fn lower_as_universal(&mut self, node: NodeIndex) -> B::Term;

        fn lower_as_existential(&mut self, node: NodeIndex) -> B::Term {
            match self.state_mut().inf_dedup_and_reentrancy.entry(node) {
                hash_map::Entry::Occupied(entry) => {
                    return match entry.get() {
                        Some(pre_lowered) => *pre_lowered,
                        // This is a cycle. Determine this fact coinductively.
                        None => <B::Term as SatTerm>::truthy(),
                    };
                }
                hash_map::Entry::Vacant(entry) => {
                    entry.insert_entry(None);
                }
            }

            let terms = self
                .graph()
                .edges_directed(
                    node,
                    match self.mode() {
                        SatForceLowererMode::Alive => Direction::Incoming,
                        SatForceLowererMode::Dead => Direction::Outgoing,
                    },
                )
                .map(|edge| self.lower_naturally(edge.source()))
                .collect::<SmallVec<[_; 4]>>();

            let out_term = if !terms.is_empty() {
                self.builder_mut().join_or(terms)
            } else {
                // We can't force this term to be alive/dead.
                <B::Term as SatTerm>::falsy()
            };

            *self
                .state_mut()
                .inf_dedup_and_reentrancy
                .get_mut(&node)
                .unwrap() = Some(out_term);

            out_term
        }
    }

    /// Returns whether a term is forced to be live assuming the universals used to derive that fact
    /// are well-formed.
    struct SatForcedLiveLowerer<'a, B: 'a + SatBuilder> {
        state: SatForceLowererState<'a, B>,
        universals: &'a mut FastIndexMap<NodeIndex, B::Var>,
    }

    impl<'a, B: 'a + SatBuilder> SatForceLowerer<'a, B> for SatForcedLiveLowerer<'a, B> {
        fn mode(&self) -> SatForceLowererMode {
            SatForceLowererMode::Alive
        }

        fn state<'b>(&'b self) -> &'b SatForceLowererState<'a, B>
        where
            'a: 'b,
        {
            &self.state
        }

        fn state_mut<'b>(&'b mut self) -> &'b mut SatForceLowererState<'a, B>
        where
            'a: 'b,
        {
            &mut self.state
        }

        fn lower_as_universal(&mut self, node: NodeIndex) -> <B as SatBuilder>::Term {
            self.universals
                .entry(node)
                .or_insert_with(|| self.state.builder.fresh_var())
                .to_term()
        }
    }

    /// Returns whether a term is forced to be dead assuming the universals used to derive that fact
    /// are well-formed.
    struct SatForcedDeadLowerer<'a, B: 'a + SatBuilder> {
        state: SatForceLowererState<'a, B>,
        universals: &'a mut FastIndexMap<NodeIndex, B::Var>,
    }

    impl<'a, B: 'a + SatBuilder> SatForceLowerer<'a, B> for SatForcedDeadLowerer<'a, B> {
        fn mode(&self) -> SatForceLowererMode {
            SatForceLowererMode::Dead
        }

        fn state<'b>(&'b self) -> &'b SatForceLowererState<'a, B>
        where
            'a: 'b,
        {
            &self.state
        }

        fn state_mut<'b>(&'b mut self) -> &'b mut SatForceLowererState<'a, B>
        where
            'a: 'b,
        {
            &mut self.state
        }

        fn lower_as_universal(&mut self, node: NodeIndex) -> <B as SatBuilder>::Term {
            !self
                .universals
                .entry(node)
                .or_insert_with(|| self.state.builder.fresh_var())
                .to_term()
        }
    }

    /// Returns whether a universal is forced to be true depending on the states of all the
    /// universals mentioned during forced-live and forced-dead collection. This is used for
    /// universal well-formedness checking.
    struct SatUniversalForcedTrueByWf<'a, B: 'a + SatBuilder> {
        state: SatForceLowererState<'a, B>,
        universals: &'a FastIndexMap<NodeIndex, B::Var>,
    }

    impl<'a, B: 'a + SatBuilder> SatForceLowerer<'a, B> for SatUniversalForcedTrueByWf<'a, B> {
        fn mode(&self) -> SatForceLowererMode {
            SatForceLowererMode::Alive
        }

        fn state<'b>(&'b self) -> &'b SatForceLowererState<'a, B>
        where
            'a: 'b,
        {
            &self.state
        }

        fn state_mut<'b>(&'b mut self) -> &'b mut SatForceLowererState<'a, B>
        where
            'a: 'b,
        {
            &mut self.state
        }

        fn lower_as_universal(&mut self, node: NodeIndex) -> <B as SatBuilder>::Term {
            if let Some(var) = self.universals.get(&node) {
                var.to_term()
            } else {
                // TODO: differential testing passes but why is this sound? Doesn't it assume that
                //  unmentioned universals can be false?
                self.lower_as_existential(node)
            }
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
        Solver,
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
                z3::SatResult::Sat => Ok(()),
                // TODO: update
                z3::SatResult::Unsat => Err(ReAndReUnifyError {
                    lhs: Re::Gc,
                    rhs: Re::Gc,
                    mode: RelationMode::Equate,
                    causes: Vec::new(),
                }),
                z3::SatResult::Unknown => unreachable!(),
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
            println!("// Test {i}");

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
    fn first_complex() {
        let mut solver = RegionFormulaSolver::new(1, 1);

        // AXIOM: 'u0 -> 'i0
        solver.push_axiom(
            [RegionFormulaTerm::Universal(UniversalReVar::from_usize(0))],
            [RegionFormulaTerm::Existential(InferReVar::from_usize(0))],
        );

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
}
