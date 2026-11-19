use crate::{
    bool_enum,
    semantic::{
        infer::{
            Promise, PromiseHandle, ReAndReUnifyError, ReConstraintOrder,
            unify::regions2::solver::RegionFormulaTerm,
        },
        syntax::{InferReVar, Re, RelationMode, UniversalReVar},
    },
    utils::lang::RangeExt as _,
};
use index_vec::{IndexVec, define_index_type};
use petgraph::Graph;
use std::range::Range;

// === ReUnifyTracker === //

define_index_type! {
    struct BufferIdx = u32;
}

define_index_type! {
    struct RelationIdx = u32;
    MAX_INDEX = (u32::MAX - 2) as usize;
}

#[derive(Clone)]
pub struct ReUnifyTracker<'sess> {
    buffer: IndexVec<BufferIdx, RegionFormulaTerm>,
    relations: IndexVec<RelationIdx, RegisteredRelation<'sess>>,
    permission_count: RelationIdx,
}

#[derive(Clone)]
struct RegisteredRelation<'sess> {
    /// A handle if this is a constraint or `None` if this is the assertion portion of a permission.
    handle: Option<PromiseHandle<'sess, ReAndReUnifyError>>,

    /// The order in which relations should be sorted for processing during verification. Lower
    /// occurs before higher. Constraint index zero is reserved for permits to simplify
    /// verification.
    order: u32,

    mode: RelationMode,
    lhs: Range<BufferIdx>,
    rhs: Range<BufferIdx>,
}

impl<'sess> ReUnifyTracker<'sess> {
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

        self.relations.push(RegisteredRelation {
            handle: None,
            order: 0,
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

        self.relations.push(RegisteredRelation {
            handle: Some(handle),
            order: order.0.get(),
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

    pub fn verify(&mut self, universal_count: usize, infer_count: usize) {
        // For permissions involving inference variables, we promote all relations that transitively
        // connect that inference variable to further terms into axioms, stopping until we reach a
        // universal variable or a `'gc`. If a relation has mixed axiomatic-ness—that is, parts of
        // it are axioms and parts aren't, as could happen with a conjunction term—we promote the
        // whole term.
        {
            bool_enum! {
                enum ShouldPropagate {
                    true => Yes;
                    false => No;
                }
            }

            const DUMMY_MARKER: RelationIdx = RelationIdx::from_raw_unchecked(u32::MAX - 1);
            const PERMISSION_MARKER: RelationIdx = RelationIdx::from_raw_unchecked(u32::MAX);

            let mut graph = Graph::new();

            let existentials = (0..infer_count)
                .map(InferReVar::from_usize)
                .map(|_| graph.add_node(ShouldPropagate::Yes))
                .collect::<IndexVec<InferReVar, _>>();

            let universals = (0..universal_count)
                .map(UniversalReVar::from_usize)
                .map(|_| graph.add_node(ShouldPropagate::No))
                .collect::<IndexVec<UniversalReVar, _>>();

            let true_node = graph.add_node(ShouldPropagate::No);

            for (relation_idx, relation) in self.relations.iter_enumerated() {
                let weight = if relation.handle.is_some() {
                    relation_idx
                } else {
                    PERMISSION_MARKER
                };

                let lhs = match self.buffer[relation.lhs.to_ops_range()].as_raw_slice() {
                    [] => continue,
                    &[unique] => unique,
                    remainder => todo!(),
                };

                let lhs = match lhs {
                    RegionFormulaTerm::True => true_node,
                    RegionFormulaTerm::Universal(var) => universals[var],
                    RegionFormulaTerm::Existential(var) => existentials[var],
                };

                for &rhs in &self.buffer[relation.rhs.to_ops_range()] {
                    let rhs = match rhs {
                        RegionFormulaTerm::True => true_node,
                        RegionFormulaTerm::Universal(var) => universals[var],
                        RegionFormulaTerm::Existential(var) => existentials[var],
                    };

                    // TODO: handle relation.mode
                    graph.add_edge(lhs, rhs, weight);
                }
            }

            // TODO
        }

        // Now, we can run our formula solver on the stream of axioms and assertions.
        // TODO
    }
}
