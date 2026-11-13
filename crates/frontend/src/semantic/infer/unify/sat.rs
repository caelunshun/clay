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

// A low latency SAT solver for equations with a small number of variables.
mod naive {
    use super::*;
    use crate::{
        bool_enum,
        utils::lang::{IterCount, iter_two_or_more},
    };
    use index_vec::define_index_type;

    // === Definitions === //

    const INSTR_START_DEFINE_OR: u32 = 0;
    const INSTR_START_ASSERT_OR: u32 = 1;
    const INSTR_START_ASSERT_NOR: u32 = 2;

    const INSTR_STREAM_MAX_VAR_EXCL: u32 = 1u32 << 30;
    const INSTR_STREAM_EOS: u32 = INSTR_STREAM_NAME_MASK;
    const INSTR_STREAM_NAME_MASK: u32 = INSTR_STREAM_NEG_BIT - 1;
    const INSTR_STREAM_NEG_BIT: u32 = 1u32 << 31;

    bool_enum! {
        pub enum SetNaivePolarity {
            true => Positive;
            false => Negative;
        }
    }

    define_index_type! {
        pub struct SatNaiveVar = u32;
        MAX_INDEX = INSTR_STREAM_MAX_VAR_EXCL as usize;
    }

    define_index_type! {
        pub struct SatNaiveIntermediate = u32;
        MAX_INDEX = (INSTR_STREAM_EOS - INSTR_STREAM_MAX_VAR_EXCL) as usize;
    }

    impl SatVar for SatNaiveVar {
        type Term = SatNaiveTerm;
    }

    #[derive(Copy, Clone, Hash, Eq, PartialEq)]
    pub enum SatNaiveTerm {
        Const(bool),
        Var(SetNaivePolarity, SatNaiveVar),
        Intermediate(SetNaivePolarity, SatNaiveIntermediate),
    }

    impl From<SatNaiveVar> for SatNaiveTerm {
        fn from(var: SatNaiveVar) -> Self {
            SatNaiveTerm::Var(SetNaivePolarity::Positive, var)
        }
    }

    impl Not for SatNaiveTerm {
        type Output = Self;

        fn not(self) -> Self::Output {
            match self {
                SatNaiveTerm::Const(v) => SatNaiveTerm::Const(!v),
                SatNaiveTerm::Var(polarity, var) => SatNaiveTerm::Var(polarity.flip(), var),
                SatNaiveTerm::Intermediate(polarity, var) => {
                    SatNaiveTerm::Intermediate(polarity.flip(), var)
                }
            }
        }
    }

    impl SatTerm for SatNaiveTerm {
        type Var = SatNaiveVar;

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

    pub struct SatNaiveBuilder {
        instructions: Vec<u32>,
        var_gen: SatNaiveVar,
        intermediate_gen: SatNaiveIntermediate,
        is_fused_false: bool,
    }

    impl SatNaiveBuilder {
        fn push_raw(
            &mut self,
            instr_kind: u32,
            terms: impl IntoIterator<Item = SatNaiveTerm>,
        ) -> SatNaiveTerm {
            let terms = match iter_two_or_more(terms) {
                IterCount::None => {
                    return SatNaiveTerm::truthy();
                }
                IterCount::One(unique) => return unique,
                IterCount::TwoOrMore(v) => v,
            };

            let old_len = self.instructions.len();
            self.instructions.push(instr_kind);

            for term in terms {
                match term {
                    SatNaiveTerm::Const(false) => continue,
                    SatNaiveTerm::Const(true) => {
                        self.instructions.truncate(old_len);
                        return SatNaiveTerm::truthy();
                    }
                    SatNaiveTerm::Var(SetNaivePolarity::Positive, var) => {
                        self.instructions.push(var.raw());
                    }
                    SatNaiveTerm::Var(SetNaivePolarity::Negative, var) => {
                        self.instructions.push(INSTR_STREAM_NEG_BIT | var.raw());
                    }
                    SatNaiveTerm::Intermediate(SetNaivePolarity::Positive, var) => {
                        self.instructions
                            .push(INSTR_STREAM_MAX_VAR_EXCL + var.raw());
                    }
                    SatNaiveTerm::Intermediate(SetNaivePolarity::Negative, var) => {
                        self.instructions
                            .push(INSTR_STREAM_NEG_BIT | (INSTR_STREAM_MAX_VAR_EXCL + var.raw()));
                    }
                }
            }

            if old_len + 1 == self.instructions.len() {
                self.instructions.truncate(old_len);
                return SatNaiveTerm::falsy();
            }

            let output = self.intermediate_gen;
            self.intermediate_gen += 1;

            SatNaiveTerm::Intermediate(SetNaivePolarity::Positive, output)
        }

        fn push_assert(
            &mut self,
            polarity: SetNaivePolarity,
            terms: impl IntoIterator<Item = SatNaiveTerm>,
        ) {
            let out = self.push_raw(
                match polarity {
                    SetNaivePolarity::Positive => INSTR_START_ASSERT_OR,
                    SetNaivePolarity::Negative => INSTR_START_ASSERT_NOR,
                },
                terms,
            );

            match out {
                SatNaiveTerm::Const(true) => {
                    if polarity == SetNaivePolarity::Negative {
                        self.is_fused_false = true;
                    }
                }
                SatNaiveTerm::Const(false) => {
                    if polarity == SetNaivePolarity::Negative {
                        self.is_fused_false = true;
                    }
                }
                SatNaiveTerm::Var(_, _) => {
                    // Result is completely varying
                }
                SatNaiveTerm::Intermediate(_, _) => {
                    // Result is completely varying. Do not allocate intermediate at end of
                    // function.
                    self.intermediate_gen -= 1;
                }
            }
        }
    }

    impl SatNaiveBuilder {
        pub fn clear(&mut self) {
            self.instructions.clear();
        }

        pub fn is_fused_false(&self) -> bool {
            self.is_fused_false
        }

        pub fn eval(
            &mut self,
            solver_stack: &mut Vec<bool>,
            mut resolve_var: impl FnMut(SatNaiveVar) -> bool,
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
                            resolve_var(SatNaiveVar::from_raw_unchecked(term_instr))
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

    impl SatBuilder for SatNaiveBuilder {
        type Var = SatNaiveVar;
        type Term = SatNaiveTerm;

        fn fresh_var(&mut self) -> Self::Var {
            let var = self.var_gen;
            self.var_gen += 1;
            var
        }

        fn assert_or(&mut self, terms: impl IntoIterator<Item = Self::Term>) {
            self.push_assert(SetNaivePolarity::Positive, terms);
        }

        fn assert_nor(&mut self, terms: impl IntoIterator<Item = Self::Term>) {
            self.push_assert(SetNaivePolarity::Negative, terms);
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
