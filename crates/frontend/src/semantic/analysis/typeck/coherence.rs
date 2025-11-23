use crate::{
    base::Session,
    semantic::syntax::{CoherenceTy, CoherenceTyKind, SolidCoherenceTy},
    utils::{hash::FxHashMap, lang::UnionIsectBuilder},
};
use index_vec::{IndexVec, define_index_type};
use std::slice;

// === CoherenceMap === //

pub struct CoherenceMap<T> {
    entries: IndexVec<CoherenceEntryIdx, T>,
    root_layer: CoherenceMapLayer,
}

impl<T> CoherenceMap<T> {
    pub fn insert(&mut self, ty: CoherenceTy, entry: T, s: &Session) {
        let index = self.entries.push(entry);
        self.root_layer.insert(ty, index, s);
    }
}

// === CoherenceMapLayer === //

#[derive(Default)]
pub struct CoherenceMapLayer {
    universally_matched_by: Vec<CoherenceEntryIdx>,
    conditionally_matched_by: FxHashMap<CoherenceTyKind, ConditionalMatcher>,
}

define_index_type! {
    pub struct CoherenceEntryIdx = u32;
}

pub enum ConditionalMatcher {
    Terminal(Vec<CoherenceEntryIdx>),
    RequiresChildren(Box<[CoherenceMapLayer]>),
}

impl CoherenceMapLayer {
    pub fn insert(&mut self, ty: CoherenceTy, index: CoherenceEntryIdx, s: &Session) {
        match ty {
            CoherenceTy::Universal => {
                self.universally_matched_by.push(index);
            }
            CoherenceTy::Solid(SolidCoherenceTy { kind, children }) => {
                let child_tys = children.r(s);

                if child_tys.is_empty() {
                    let ConditionalMatcher::Terminal(indices) = self
                        .conditionally_matched_by
                        .entry(kind)
                        .or_insert(ConditionalMatcher::Terminal(Vec::new()))
                    else {
                        unreachable!()
                    };

                    indices.push(index);
                } else {
                    let ConditionalMatcher::RequiresChildren(child_layers) = self
                        .conditionally_matched_by
                        .entry(kind)
                        .or_insert_with(|| {
                            ConditionalMatcher::RequiresChildren(
                                child_tys
                                    .iter()
                                    .map(|_| CoherenceMapLayer::default())
                                    .collect(),
                            )
                        })
                    else {
                        unreachable!()
                    };

                    for (&ty, layer) in child_tys.iter().zip(child_layers) {
                        layer.insert(ty, index, s);
                    }
                }
            }
        }
    }

    pub fn lookup<'a>(
        &'a self,
        ty: CoherenceTy,
        set: &mut UnionIsectBuilder<slice::Iter<'a, CoherenceEntryIdx>>,
        s: &Session,
    ) {
        todo!();
    }
}
