use crate::{
    base::Session,
    semantic::syntax::{CoherenceTy, CoherenceTyKind, SolidCoherenceTy},
    utils::{
        hash::FxHashMap,
        lang::{UnionIsectBuilder, UnionIsectOp},
    },
};
use derive_where::derive_where;
use index_vec::{IndexVec, define_index_type};
use std::slice;

// === CoherenceMap === //

#[derive(Debug)]
#[derive_where(Default)]
pub struct CoherenceMap<T> {
    entries: IndexVec<CoherenceEntryIdx, T>,
    root_layer: CoherenceMapLayer,
}

impl<T> CoherenceMap<T> {
    pub fn insert(&mut self, ty: CoherenceTy, entry: T, s: &Session) {
        let index = self.entries.push(entry);
        self.root_layer.insert(ty, index, s);
    }

    pub fn lookup(&self, ty: CoherenceTy, s: &Session) -> impl Iterator<Item = &T> {
        let mut set = UnionIsectBuilder::default();
        self.root_layer.lookup(ty, &mut set, s);
        set.finish().map(|&idx| &self.entries[idx])
    }
}

// === CoherenceMapLayer === //

#[derive(Debug, Default)]
pub struct CoherenceMapLayer {
    universally_matched_by: Vec<CoherenceEntryIdx>,
    conditionally_matched_by: FxHashMap<CoherenceTyKind, ConditionalMatcher>,
}

define_index_type! {
    pub struct CoherenceEntryIdx = u32;
}

#[derive(Debug)]
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
        set.push_op(UnionIsectOp::Union);

        if !self.universally_matched_by.is_empty() {
            set.push_iter(self.universally_matched_by.iter());
        }

        if let CoherenceTy::Solid(ty) = ty {
            if let Some(matched_by) = self.conditionally_matched_by.get(&ty.kind) {
                match matched_by {
                    ConditionalMatcher::Terminal(items) => {
                        if !items.is_empty() {
                            set.push_iter(items.iter());
                        }
                    }
                    ConditionalMatcher::RequiresChildren(layers) => {
                        set.push_op(UnionIsectOp::Intersect);
                        for (&ty, layer) in ty.children.r(s).iter().zip(layers) {
                            layer.lookup(ty, set, s);
                        }
                        set.pop_op();
                    }
                }
            }
        } else {
            for matched_by in self.conditionally_matched_by.values() {
                match matched_by {
                    ConditionalMatcher::Terminal(items) => {
                        if !items.is_empty() {
                            set.push_iter(items.iter());
                        }
                    }
                    ConditionalMatcher::RequiresChildren(layers) => {
                        for layer in layers {
                            layer.lookup(CoherenceTy::Universal, set, s);
                        }
                    }
                }
            }
        }

        set.pop_op();
    }
}

// === Tests === //

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        base::arena::HasListInterner as _,
        semantic::{analysis::TyCtxt, syntax::SimpleTyKind},
        utils::hash::FxHashSet,
    };

    #[test]
    fn coherence_map() {
        let session = Session::new();
        let _guard = session.clone().bind();

        let tcx = TyCtxt::new(session);

        let mut map = CoherenceMap::<&'static str>::default();

        map.insert(CoherenceTy::Universal, "_", &tcx.session);
        map.insert(
            CoherenceTy::Solid(SolidCoherenceTy {
                kind: CoherenceTyKind::Tuple(2),
                children: tcx.intern(&[
                    CoherenceTy::Universal,
                    CoherenceTy::Solid(SolidCoherenceTy {
                        kind: CoherenceTyKind::Simple(SimpleTyKind::Bool),
                        children: tcx.intern(&[]),
                    }),
                ]),
            }),
            "(_, bool)",
            &tcx.session,
        );
        map.insert(
            CoherenceTy::Solid(SolidCoherenceTy {
                kind: CoherenceTyKind::Tuple(2),
                children: tcx.intern(&[
                    CoherenceTy::Solid(SolidCoherenceTy {
                        kind: CoherenceTyKind::Simple(SimpleTyKind::Str),
                        children: tcx.intern(&[]),
                    }),
                    CoherenceTy::Universal,
                ]),
            }),
            "(str, _)",
            &tcx.session,
        );

        assert_eq!(
            map.lookup(
                CoherenceTy::Solid(SolidCoherenceTy {
                    kind: CoherenceTyKind::Tuple(2),
                    children: tcx.intern(&[CoherenceTy::Universal, CoherenceTy::Universal]),
                }),
                &tcx.session,
            )
            .copied()
            .collect::<FxHashSet<_>>(),
            FxHashSet::from_iter(["_", "(_, bool)", "(str, _)"]),
        );

        assert_eq!(
            map.lookup(
                CoherenceTy::Solid(SolidCoherenceTy {
                    kind: CoherenceTyKind::Tuple(2),
                    children: tcx.intern(&[
                        CoherenceTy::Universal,
                        CoherenceTy::Solid(SolidCoherenceTy {
                            kind: CoherenceTyKind::Simple(SimpleTyKind::Bool),
                            children: tcx.intern(&[])
                        })
                    ]),
                }),
                &tcx.session,
            )
            .copied()
            .collect::<FxHashSet<_>>(),
            FxHashSet::from_iter(["_", "(_, bool)", "(str, _)"]),
        );

        assert_eq!(
            map.lookup(
                CoherenceTy::Solid(SolidCoherenceTy {
                    kind: CoherenceTyKind::Tuple(2),
                    children: tcx.intern(&[
                        CoherenceTy::Universal,
                        CoherenceTy::Solid(SolidCoherenceTy {
                            kind: CoherenceTyKind::Simple(SimpleTyKind::Str),
                            children: tcx.intern(&[])
                        })
                    ]),
                }),
                &tcx.session,
            )
            .copied()
            .collect::<FxHashSet<_>>(),
            FxHashSet::from_iter(["_", "(str, _)"]),
        );
    }
}
