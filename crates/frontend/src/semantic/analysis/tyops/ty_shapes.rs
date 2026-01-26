use crate::{
    base::{
        Session,
        arena::{HasListInterner as _, Obj},
    },
    semantic::{
        analysis::TyCtxt,
        syntax::{
            AdtInstance, SolidTyShape, SolidTyShapeKind, TraitItem, Ty, TyKind, TyOrRe, TyShape,
        },
    },
    utils::{
        hash::FxHashMap,
        lang::{UnionIsectBuilder, UnionIsectIter, UnionIsectOp},
    },
};
use derive_where::derive_where;
use index_vec::{IndexVec, define_index_type};
use std::slice;

// === Erasure === //

impl TyCtxt {
    pub fn shape_of_trait_def(&self, def: Obj<TraitItem>, args: &[TyOrRe], target: Ty) -> TyShape {
        let s = &self.session;

        debug_assert_eq!(args.len(), def.r(s).regular_generic_count as usize);

        TyShape::Solid(SolidTyShape {
            kind: SolidTyShapeKind::TraitImpl(def),
            children: self.intern_list(
                &([self.erase_ty_to_shape(target)]
                    .into_iter()
                    .chain(
                        args.iter()
                            .filter_map(|ty| ty.as_ty())
                            .map(|ty| self.erase_ty_to_shape(ty)),
                    )
                    .collect::<Vec<_>>()),
            ),
        })
    }

    pub fn erase_ty_to_shape(&self, ty: Ty) -> TyShape {
        let s = &self.session;

        match *ty.r(s) {
            // It's always safe to be conservative with these types.
            TyKind::SigThis
            | TyKind::HrtbVar(_)
            | TyKind::InferVar(_)
            | TyKind::UniversalVar(_)
            | TyKind::SigInfer
            | TyKind::SigGeneric(_)
            | TyKind::SigProject(_)
            | TyKind::Error(_) => TyShape::Hole,

            TyKind::Simple(kind) => TyShape::Solid(SolidTyShape {
                kind: SolidTyShapeKind::Simple(kind),
                children: self.intern_list(&[]),
            }),
            TyKind::Reference(_re, mutability, pointee) => TyShape::Solid(SolidTyShape {
                kind: SolidTyShapeKind::Re(mutability),
                children: self.intern_list(&[self.erase_ty_to_shape(pointee)]),
            }),
            TyKind::Adt(AdtInstance { def, params }) => TyShape::Solid(SolidTyShape {
                kind: SolidTyShapeKind::Adt(def),
                children: self.intern_list(
                    &params
                        .r(s)
                        .iter()
                        .filter_map(|ty| ty.as_ty())
                        .map(|ty| self.erase_ty_to_shape(ty))
                        .collect::<Vec<_>>(),
                ),
            }),
            TyKind::Trait(_re, _muta, _intern) => todo!(),
            TyKind::Tuple(children) => TyShape::Solid(SolidTyShape {
                kind: SolidTyShapeKind::Tuple(children.r(s).len() as u32),
                children: self.intern_list(
                    &children
                        .r(s)
                        .iter()
                        .map(|&ty| self.erase_ty_to_shape(ty))
                        .collect::<Vec<_>>(),
                ),
            }),
            TyKind::FnDef(obj, generics) => todo!(),
        }
    }
}

// === TyShapeMap === //

#[derive(Debug)]
#[derive_where(Default)]
pub struct TyShapeMap<T> {
    entries: IndexVec<EntryIdx, T>,
    root_layer: MapLayer,
}

impl<T> TyShapeMap<T> {
    pub fn insert(&mut self, ty: TyShape, entry: T, s: &Session) {
        let index = self.entries.push(entry);
        self.root_layer.insert(ty, index, s);
    }

    pub fn lookup(&self, ty: TyShape, s: &Session) -> TyShapeMapIter<'_, T> {
        let mut set = UnionIsectBuilder::default();

        self.root_layer.lookup(ty, &mut set, s);

        TyShapeMapIter {
            entries: &self.entries,
            iter: set.finish(),
        }
    }
}

pub struct TyShapeMapIter<'a, T> {
    entries: &'a IndexVec<EntryIdx, T>,
    iter: UnionIsectIter<slice::Iter<'a, EntryIdx>>,
}

impl<'a, T> Iterator for TyShapeMapIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|&v| &self.entries[v])
    }
}

// === MapLayer === //

define_index_type! {
    struct EntryIdx = u32;
}

#[derive(Debug, Clone, Default)]
struct MapLayer {
    universally_matched_by: Vec<EntryIdx>,
    conditionally_matched_by: FxHashMap<SolidTyShapeKind, ConditionalMatcher>,
}

#[derive(Debug, Clone)]
enum ConditionalMatcher {
    Terminal(Vec<EntryIdx>),
    RequiresChildren(Box<[MapLayer]>),
}

impl MapLayer {
    fn insert(&mut self, ty: TyShape, index: EntryIdx, s: &Session) {
        match ty {
            TyShape::Hole => {
                self.universally_matched_by.push(index);
            }
            TyShape::Solid(SolidTyShape { kind, children }) => {
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
                                child_tys.iter().map(|_| MapLayer::default()).collect(),
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

    fn lookup<'a>(
        &'a self,
        ty: TyShape,
        set: &mut UnionIsectBuilder<slice::Iter<'a, EntryIdx>>,
        s: &Session,
    ) {
        set.push_op(UnionIsectOp::Union);

        if !self.universally_matched_by.is_empty() {
            set.push_iter(self.universally_matched_by.iter());
        }

        if let TyShape::Solid(ty) = ty {
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
                            layer.lookup(TyShape::Hole, set, s);
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
        semantic::{analysis::TyCtxt, syntax::SimpleTyKind},
        utils::hash::FxHashSet,
    };

    #[test]
    fn coherence_map() {
        let session = Session::new();
        let _guard = session.clone().bind();

        let tcx = TyCtxt::new(session);

        let mut map = TyShapeMap::<&'static str>::default();

        map.insert(TyShape::Hole, "_", &tcx.session);
        map.insert(
            TyShape::Solid(SolidTyShape {
                kind: SolidTyShapeKind::Tuple(2),
                children: tcx.intern_list(&[
                    TyShape::Hole,
                    TyShape::Solid(SolidTyShape {
                        kind: SolidTyShapeKind::Simple(SimpleTyKind::Bool),
                        children: tcx.intern_list(&[]),
                    }),
                ]),
            }),
            "(_, bool)",
            &tcx.session,
        );
        map.insert(
            TyShape::Solid(SolidTyShape {
                kind: SolidTyShapeKind::Tuple(2),
                children: tcx.intern_list(&[
                    TyShape::Solid(SolidTyShape {
                        kind: SolidTyShapeKind::Simple(SimpleTyKind::Str),
                        children: tcx.intern_list(&[]),
                    }),
                    TyShape::Hole,
                ]),
            }),
            "(str, _)",
            &tcx.session,
        );

        assert_eq!(
            map.lookup(
                TyShape::Solid(SolidTyShape {
                    kind: SolidTyShapeKind::Tuple(2),
                    children: tcx.intern_list(&[TyShape::Hole, TyShape::Hole]),
                }),
                &tcx.session,
            )
            .copied()
            .collect::<FxHashSet<_>>(),
            FxHashSet::from_iter(["_", "(_, bool)", "(str, _)"]),
        );

        assert_eq!(
            map.lookup(
                TyShape::Solid(SolidTyShape {
                    kind: SolidTyShapeKind::Tuple(2),
                    children: tcx.intern_list(&[
                        TyShape::Hole,
                        TyShape::Solid(SolidTyShape {
                            kind: SolidTyShapeKind::Simple(SimpleTyKind::Bool),
                            children: tcx.intern_list(&[])
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
                TyShape::Solid(SolidTyShape {
                    kind: SolidTyShapeKind::Tuple(2),
                    children: tcx.intern_list(&[
                        TyShape::Hole,
                        TyShape::Solid(SolidTyShape {
                            kind: SolidTyShapeKind::Simple(SimpleTyKind::Str),
                            children: tcx.intern_list(&[])
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
