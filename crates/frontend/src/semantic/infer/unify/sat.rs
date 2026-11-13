use std::{hash, ops::Not};

pub trait SatBuilder {
    type Var: SatVar<Term = Self::Term>;
    type Term: SatTerm<Var = Self::Var>;

    fn fresh_var(&mut self) -> Self::Var;

    fn assert_or(&mut self, terms: impl IntoIterator<Item = Self::Term>);

    fn assert_nor(&mut self, terms: impl IntoIterator<Item = Self::Term>);

    fn assert_iff(&mut self, lhs: Self::Term, rhs: Self::Term);

    fn assert_implies(&mut self, lhs: Self::Term, rhs: Self::Term);

    fn assert_one(&mut self, term: Self::Term);

    fn assert_or_implies(&mut self, lhs: impl IntoIterator<Item = Self::Term>, rhs: Self::Term);

    fn assert_or_iff(&mut self, lhs: impl IntoIterator<Item = Self::Term>, rhs: Self::Term);

    fn assert_and(&mut self, terms: impl IntoIterator<Item = Self::Term>);

    fn assert_and_implies(&mut self, lhs: impl IntoIterator<Item = Self::Term>, rhs: Self::Term);

    fn assert_and_iff(&mut self, lhs: impl IntoIterator<Item = Self::Term>, rhs: Self::Term);

    fn join_or(&mut self, terms: impl IntoIterator<Item = Self::Term>) -> Self::Term;

    fn join_nor(&mut self, terms: impl IntoIterator<Item = Self::Term>) -> Self::Term;

    fn join_and(&mut self, terms: impl IntoIterator<Item = Self::Term>) -> Self::Term;

    fn join_iff(&mut self, lhs: Self::Term, rhs: Self::Term) -> Self::Term;

    fn join_implies(&mut self, lhs: Self::Term, rhs: Self::Term) -> Self::Term;
}

pub trait SatVar: Copy + hash::Hash + Eq {
    type Term: SatTerm<Var = Self>;

    fn to_term(self) -> Self::Term {
        Self::Term::from(self)
    }
}

pub trait SatTerm: Copy + hash::Hash + Eq + Not<Output = Self> + From<Self::Var> {
    type Var: SatVar<Term = Self>;

    fn constant(v: bool) -> Self;

    fn truthy() -> Self;

    fn falsy() -> Self;
}

// No-op
mod nop {
    use crate::semantic::infer::unify::sat::{SatBuilder, SatTerm, SatVar};
    use std::ops::Not;

    #[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Default)]
    pub struct NopSatVar;

    impl SatVar for NopSatVar {
        type Term = NopSatTerm;
    }

    #[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Default)]
    pub struct NopSatTerm;

    impl From<NopSatVar> for NopSatTerm {
        fn from(_value: NopSatVar) -> Self {
            NopSatTerm
        }
    }

    impl Not for NopSatTerm {
        type Output = NopSatTerm;

        fn not(self) -> Self::Output {
            self
        }
    }

    impl SatTerm for NopSatTerm {
        type Var = NopSatVar;

        fn constant(_v: bool) -> Self {
            NopSatTerm
        }

        fn truthy() -> Self {
            NopSatTerm
        }

        fn falsy() -> Self {
            NopSatTerm
        }
    }

    #[derive(Default)]
    pub struct NopSatBuilder {}

    impl SatBuilder for NopSatBuilder {
        type Var = NopSatVar;
        type Term = NopSatTerm;

        fn fresh_var(&mut self) -> Self::Var {
            NopSatVar
        }

        fn assert_or(&mut self, _terms: impl IntoIterator<Item = Self::Term>) {
            // (empty)
        }

        fn assert_nor(&mut self, _terms: impl IntoIterator<Item = Self::Term>) {
            // (empty)
        }

        fn assert_iff(&mut self, _lhs: Self::Term, _rhs: Self::Term) {
            // (empty)
        }

        fn assert_implies(&mut self, _lhs: Self::Term, _rhs: Self::Term) {
            // (empty)
        }

        fn assert_one(&mut self, _term: Self::Term) {
            // (empty)
        }

        fn assert_or_implies(
            &mut self,
            _lhs: impl IntoIterator<Item = Self::Term>,
            _rhs: Self::Term,
        ) {
            // (empty)
        }

        fn assert_or_iff(&mut self, _lhs: impl IntoIterator<Item = Self::Term>, _rhs: Self::Term) {
            // (empty)
        }

        fn assert_and(&mut self, _terms: impl IntoIterator<Item = Self::Term>) {
            // (empty)
        }

        fn assert_and_implies(
            &mut self,
            _lhs: impl IntoIterator<Item = Self::Term>,
            _rhs: Self::Term,
        ) {
            // (empty)
        }

        fn assert_and_iff(&mut self, _lhs: impl IntoIterator<Item = Self::Term>, _rhs: Self::Term) {
            // (empty)
        }

        fn join_or(&mut self, _terms: impl IntoIterator<Item = Self::Term>) -> Self::Term {
            NopSatTerm
        }

        fn join_nor(&mut self, _terms: impl IntoIterator<Item = Self::Term>) -> Self::Term {
            NopSatTerm
        }

        fn join_and(&mut self, _terms: impl IntoIterator<Item = Self::Term>) -> Self::Term {
            NopSatTerm
        }

        fn join_iff(&mut self, _lhs: Self::Term, _rhs: Self::Term) -> Self::Term {
            NopSatTerm
        }

        fn join_implies(&mut self, _lhs: Self::Term, _rhs: Self::Term) -> Self::Term {
            NopSatTerm
        }
    }
}

pub use self::nop::*;

// A low latency SAT solver for equations with a small number of variables.
mod brute {
    use super::*;
    use crate::{
        bool_enum,
        utils::lang::{IterCount, iter_two_or_more},
    };
    use index_vec::{IndexVec, define_index_type};

    // === Definitions === //

    const INSTR_START_DEFINE_OR: u32 = 0;
    const INSTR_START_ASSERT_OR: u32 = 1;
    const INSTR_START_ASSERT_NOR: u32 = 2;

    const INSTR_STREAM_MAX_VAR_EXCL: u32 = 1u32 << 30;
    const INSTR_STREAM_EOS: u32 = INSTR_STREAM_NAME_MASK;
    const INSTR_STREAM_NAME_MASK: u32 = INSTR_STREAM_NEG_BIT - 1;
    const INSTR_STREAM_NEG_BIT: u32 = 1u32 << 31;

    #[derive(Debug, Copy, Clone, Default)]
    pub struct BruteUnsatisfied;

    #[derive(Debug, Clone)]
    pub struct BruteSatisfied {
        pub model: IndexVec<BruteSatVar, bool>,
    }

    bool_enum! {
        pub enum BruteSatPolarity {
            true => Positive;
            false => Negative;
        }
    }

    define_index_type! {
        pub struct BruteSatVar = u32;
        MAX_INDEX = INSTR_STREAM_MAX_VAR_EXCL as usize;
    }

    define_index_type! {
        pub struct BruteSatIntermediate = u32;
        MAX_INDEX = (INSTR_STREAM_EOS - INSTR_STREAM_MAX_VAR_EXCL) as usize;
    }

    impl SatVar for BruteSatVar {
        type Term = BruteSatTerm;
    }

    #[derive(Copy, Clone, Hash, Eq, PartialEq)]
    pub enum BruteSatTerm {
        Const(bool),
        Var(BruteSatPolarity, BruteSatVar),
        Intermediate(BruteSatPolarity, BruteSatIntermediate),
    }

    impl From<BruteSatVar> for BruteSatTerm {
        fn from(var: BruteSatVar) -> Self {
            BruteSatTerm::Var(BruteSatPolarity::Positive, var)
        }
    }

    impl Not for BruteSatTerm {
        type Output = Self;

        fn not(self) -> Self::Output {
            match self {
                BruteSatTerm::Const(v) => BruteSatTerm::Const(!v),
                BruteSatTerm::Var(polarity, var) => BruteSatTerm::Var(polarity.flip(), var),
                BruteSatTerm::Intermediate(polarity, var) => {
                    BruteSatTerm::Intermediate(polarity.flip(), var)
                }
            }
        }
    }

    impl SatTerm for BruteSatTerm {
        type Var = BruteSatVar;

        fn constant(v: bool) -> Self {
            Self::Const(v)
        }

        fn truthy() -> Self {
            Self::Const(true)
        }

        fn falsy() -> Self {
            Self::Const(false)
        }
    }

    // === Builder === //

    pub struct BruteSatBuilder {
        instructions: Vec<u32>,
        var_gen: BruteSatVar,
        intermediate_gen: BruteSatIntermediate,
        is_fused_false: bool,
    }

    impl Default for BruteSatBuilder {
        fn default() -> Self {
            Self {
                instructions: Vec::new(),
                var_gen: BruteSatVar::from_usize(0),
                intermediate_gen: BruteSatIntermediate::from_usize(0),
                is_fused_false: false,
            }
        }
    }

    impl BruteSatBuilder {
        fn push_raw(
            &mut self,
            instr_kind: u32,
            terms: impl IntoIterator<Item = BruteSatTerm>,
        ) -> BruteSatTerm {
            let terms = match iter_two_or_more(terms) {
                IterCount::None => {
                    return BruteSatTerm::truthy();
                }
                IterCount::One(unique) => return unique,
                IterCount::TwoOrMore(v) => v,
            };

            let old_len = self.instructions.len();
            self.instructions.push(instr_kind);

            for term in terms {
                match term {
                    BruteSatTerm::Const(false) => continue,
                    BruteSatTerm::Const(true) => {
                        self.instructions.truncate(old_len);
                        return BruteSatTerm::truthy();
                    }
                    BruteSatTerm::Var(BruteSatPolarity::Positive, var) => {
                        self.instructions.push(var.raw());
                    }
                    BruteSatTerm::Var(BruteSatPolarity::Negative, var) => {
                        self.instructions.push(INSTR_STREAM_NEG_BIT | var.raw());
                    }
                    BruteSatTerm::Intermediate(BruteSatPolarity::Positive, var) => {
                        self.instructions
                            .push(INSTR_STREAM_MAX_VAR_EXCL + var.raw());
                    }
                    BruteSatTerm::Intermediate(BruteSatPolarity::Negative, var) => {
                        self.instructions
                            .push(INSTR_STREAM_NEG_BIT | (INSTR_STREAM_MAX_VAR_EXCL + var.raw()));
                    }
                }
            }

            if old_len + 1 == self.instructions.len() {
                self.instructions.truncate(old_len);
                return BruteSatTerm::falsy();
            }

            let output = self.intermediate_gen;
            self.intermediate_gen += 1;

            BruteSatTerm::Intermediate(BruteSatPolarity::Positive, output)
        }

        fn push_assert(
            &mut self,
            polarity: BruteSatPolarity,
            terms: impl IntoIterator<Item = BruteSatTerm>,
        ) {
            let out = self.push_raw(
                match polarity {
                    BruteSatPolarity::Positive => INSTR_START_ASSERT_OR,
                    BruteSatPolarity::Negative => INSTR_START_ASSERT_NOR,
                },
                terms,
            );

            match out {
                BruteSatTerm::Const(true) => {
                    if polarity == BruteSatPolarity::Negative {
                        self.is_fused_false = true;
                    }
                }
                BruteSatTerm::Const(false) => {
                    if polarity == BruteSatPolarity::Negative {
                        self.is_fused_false = true;
                    }
                }
                BruteSatTerm::Var(_, _) => {
                    // Result is completely varying
                }
                BruteSatTerm::Intermediate(_, _) => {
                    // Result is completely varying. Do not allocate intermediate at end of
                    // function.
                    self.intermediate_gen -= 1;
                }
            }
        }
    }

    impl BruteSatBuilder {
        pub fn clear(&mut self) {
            self.instructions.clear();
        }

        pub fn is_fused_false(&self) -> bool {
            self.is_fused_false
        }

        pub fn solve(&mut self) -> Result<BruteSatisfied, BruteSatisfied> {
            todo!()
        }

        pub fn eval(
            &mut self,
            solver_stack: &mut Vec<bool>,
            mut resolve_var: impl FnMut(BruteSatVar) -> bool,
        ) -> bool {
            if self.is_fused_false {
                return false;
            }

            let mut reader = self.instructions.iter().copied();
            let mut solver_stack = scopeguard::guard(solver_stack, Vec::clear);

            loop {
                let Some(start_instr) = reader.next() else {
                    break true;
                };

                let or_truthy = loop {
                    let term_instr = reader.next().unwrap();

                    let value = match term_instr & INSTR_STREAM_NAME_MASK {
                        0..INSTR_STREAM_MAX_VAR_EXCL => {
                            resolve_var(BruteSatVar::from_raw_unchecked(term_instr))
                        }
                        INSTR_STREAM_MAX_VAR_EXCL..INSTR_STREAM_EOS => {
                            solver_stack[(term_instr - INSTR_STREAM_MAX_VAR_EXCL) as usize]
                        }
                        INSTR_STREAM_EOS => {
                            break false;
                        }
                        _ => unreachable!(),
                    };

                    let value = if term_instr & INSTR_STREAM_NEG_BIT != 0 {
                        !value
                    } else {
                        value
                    };

                    if value {
                        break true;
                    }
                };

                match start_instr {
                    INSTR_START_DEFINE_OR => {
                        solver_stack.push(or_truthy);
                    }
                    INSTR_START_ASSERT_OR => {
                        if !or_truthy {
                            return false;
                        }
                    }
                    INSTR_START_ASSERT_NOR => {
                        if or_truthy {
                            return false;
                        }
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    impl SatBuilder for BruteSatBuilder {
        type Var = BruteSatVar;
        type Term = BruteSatTerm;

        fn fresh_var(&mut self) -> Self::Var {
            let var = self.var_gen;
            self.var_gen += 1;
            var
        }

        fn assert_or(&mut self, terms: impl IntoIterator<Item = Self::Term>) {
            self.push_assert(BruteSatPolarity::Positive, terms);
        }

        fn assert_nor(&mut self, terms: impl IntoIterator<Item = Self::Term>) {
            self.push_assert(BruteSatPolarity::Negative, terms);
        }

        fn assert_iff(&mut self, lhs: Self::Term, rhs: Self::Term) {
            let first = self.join_and([lhs, rhs]);
            let second = self.join_and([!lhs, !rhs]);

            self.assert_or([first, second]);
        }

        fn assert_implies(&mut self, lhs: Self::Term, rhs: Self::Term) {
            self.assert_or([!lhs, rhs]);
        }

        fn assert_one(&mut self, term: Self::Term) {
            self.assert_or([term]);
        }

        fn assert_or_implies(
            &mut self,
            lhs: impl IntoIterator<Item = Self::Term>,
            rhs: Self::Term,
        ) {
            let lhs = self.join_or(lhs);
            self.assert_implies(lhs, rhs);
        }

        fn assert_or_iff(&mut self, lhs: impl IntoIterator<Item = Self::Term>, rhs: Self::Term) {
            let lhs = self.join_or(lhs);
            self.assert_iff(lhs, rhs);
        }

        fn assert_and(&mut self, terms: impl IntoIterator<Item = Self::Term>) {
            self.assert_nor(terms.into_iter().map(Not::not));
        }

        fn assert_and_implies(
            &mut self,
            lhs: impl IntoIterator<Item = Self::Term>,
            rhs: Self::Term,
        ) {
            let lhs = self.join_and(lhs);
            self.assert_implies(lhs, rhs);
        }

        fn assert_and_iff(&mut self, lhs: impl IntoIterator<Item = Self::Term>, rhs: Self::Term) {
            let lhs = self.join_and(lhs);
            self.assert_iff(lhs, rhs);
        }

        fn join_or(&mut self, terms: impl IntoIterator<Item = Self::Term>) -> Self::Term {
            self.push_raw(INSTR_START_DEFINE_OR, terms)
        }

        fn join_nor(&mut self, terms: impl IntoIterator<Item = Self::Term>) -> Self::Term {
            !self.join_or(terms)
        }

        fn join_and(&mut self, terms: impl IntoIterator<Item = Self::Term>) -> Self::Term {
            self.join_nor(terms.into_iter().map(Not::not))
        }

        fn join_iff(&mut self, lhs: Self::Term, rhs: Self::Term) -> Self::Term {
            let first = self.join_and([lhs, rhs]);
            let second = self.join_and([!lhs, !rhs]);

            self.join_or([first, second])
        }

        fn join_implies(&mut self, lhs: Self::Term, rhs: Self::Term) -> Self::Term {
            self.join_or([!lhs, rhs])
        }
    }
}

pub use self::brute::*;
