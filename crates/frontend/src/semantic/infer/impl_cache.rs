use crate::{
    base::{
        Session,
        arena::{HasListInterner as _, Obj},
        syntax::Symbol,
    },
    semantic::{
        infer::ClauseCx,
        syntax::{
            AdtInstance, Crate, FnDef, ImplItem, SigAdtInstance, SigTy, SigTyKind, SigTyOrRe,
            SolidTyShape, SolidTyShapeKind, TraitItem, TraitParam, TraitSpec, Ty, TyCtxt, TyKind,
            TyOrRe, TyShape,
        },
    },
    utils::lang::{UnionIsectBuilder, UnionIsectIter, UnionIsectOp},
};
use clay_core::FastHashMap;
use derive_where::derive_where;
use index_vec::{IndexVec, define_index_type};
use std::slice;

// === ImplCache === //

#[derive(Debug, Default)]
pub struct ImplCache {
    by_shape: TyShapeMap<ImplCacheEntry>,
}

#[derive(Debug, Copy, Clone)]
pub enum ImplCacheEntry {
    TraitImpl(Obj<ImplItem>),
    InherentMethod(Obj<FnDef>),
}

impl ImplCache {
    pub fn populate(&mut self, tcx: &TyCtxt, krate: Obj<Crate>) {
        let s = &tcx.session;

        for &item in &**krate.r(s).items {
            let Some(item) = item.r(s).kind.as_impl() else {
                continue;
            };

            let self_ty_shape =
                SigShapeEraser { tcx, self_ty: None }.shape_of_ty(*item.r(s).target);

            let trait_eraser = SigShapeEraser {
                tcx,
                self_ty: Some(self_ty_shape),
            };

            match *item.r(s).trait_ {
                Some(trait_) => {
                    let arg_count = *trait_.def.r(s).regular_generic_count as usize;

                    self.by_shape.insert(
                        trait_eraser.shape_of_trait_impl(
                            trait_.def,
                            &trait_.params.elems.r(s)[..arg_count],
                            *item.r(s).target,
                        ),
                        ImplCacheEntry::TraitImpl(item),
                        s,
                    );
                }
                None => {
                    for &method in &**item.r(s).methods {
                        let method = method.unwrap();

                        self.by_shape.insert(
                            trait_eraser.shape_of_inherent_function(method.r(s).name.text),
                            ImplCacheEntry::InherentMethod(method),
                            s,
                        );

                        if !*method.r(s).has_self_param {
                            continue;
                        }

                        // We perform an ad-hoc self-type substitution on the receiver to tighten
                        // its bounds. We don't need to bring in a full `ClauseCx` to do this
                        // because entries in the `ImplCache` are only approximations.
                        let receiver = method.r(s).args.r(s)[0].ty;

                        self.by_shape.insert(
                            trait_eraser.shape_of_inherent_method(receiver, method.r(s).name.text),
                            ImplCacheEntry::InherentMethod(method),
                            s,
                        );
                    }
                }
            }
        }
    }

    pub fn gather_inherent_impl_method_candidates<'a, 'tcx>(
        &'a self,
        ccx: &'a ClauseCx<'tcx>,
        receiver: Ty,
        name: Symbol,
    ) -> impl Iterator<Item = Obj<FnDef>> + 'a {
        let s = ccx.session();
        let eraser = ImportedShapeEraser { ccx };

        self.by_shape
            .lookup(eraser.shape_of_inherent_method(receiver, name), s)
            .map(|v| {
                let ImplCacheEntry::InherentMethod(v) = *v else {
                    unreachable!()
                };

                v
            })
    }

    pub fn gather_inherent_impl_function_candidates<'a>(
        &'a self,
        ccx: &'_ ClauseCx<'a>,
        self_ty: Ty,
        name: Symbol,
    ) -> impl Iterator<Item = Obj<FnDef>> + use<'a> {
        let s = ccx.session();
        let eraser = ImportedShapeEraser { ccx };

        self.by_shape
            .lookup(eraser.shape_of_inherent_function(self_ty, name), s)
            .map(|v| {
                let ImplCacheEntry::InherentMethod(v) = *v else {
                    unreachable!()
                };

                v
            })
    }

    pub fn gather_trait_impl_candidates<'a, 'tcx>(
        &'a self,
        ccx: &'a ClauseCx<'tcx>,
        lhs: Ty,
        rhs: TraitSpec,
    ) -> impl Iterator<Item = Obj<ImplItem>> + 'a {
        let s = ccx.session();
        let eraser = ImportedShapeEraser { ccx };

        self.by_shape
            .lookup(
                eraser.shape_of_trait_impl(
                    rhs.def,
                    &rhs.params.r(s)[..*rhs.def.r(s).regular_generic_count as usize]
                        .iter()
                        .map(|&v| match v {
                            TraitParam::Equals(v) => v,
                            TraitParam::Unspecified(_) => unreachable!(),
                        })
                        .collect::<Vec<_>>(),
                    lhs,
                ),
                s,
            )
            .map(|v| {
                let ImplCacheEntry::TraitImpl(v) = *v else {
                    unreachable!()
                };

                v
            })
    }
}

// === Type Erasure === //

pub struct SigShapeEraser<'a> {
    pub tcx: &'a TyCtxt,
    pub self_ty: Option<TyShape>,
}

impl SigShapeEraser<'_> {
    pub fn shape_of_trait_impl(
        &self,
        def: Obj<TraitItem>,
        args: &[SigTyOrRe],
        target: SigTy,
    ) -> TyShape {
        let s = &self.tcx.session;

        debug_assert_eq!(args.len(), *def.r(s).regular_generic_count as usize);

        TyShape::Solid(SolidTyShape {
            kind: SolidTyShapeKind::TraitImpl(def),
            children: self.tcx.intern_list(
                &([self.shape_of_ty(target)]
                    .into_iter()
                    .chain(
                        args.iter()
                            .filter_map(|ty| ty.as_ty())
                            .map(|ty| self.shape_of_ty(ty)),
                    )
                    .collect::<Vec<_>>()),
            ),
        })
    }

    pub fn shape_of_inherent_method(&self, receiver: SigTy, name: Symbol) -> TyShape {
        TyShape::Solid(SolidTyShape {
            kind: SolidTyShapeKind::InherentMethodImpl(name),
            children: self.tcx.intern_list(&[self.shape_of_ty(receiver)]),
        })
    }

    pub fn shape_of_inherent_function(&self, name: Symbol) -> TyShape {
        TyShape::Solid(SolidTyShape {
            kind: SolidTyShapeKind::InherentFunctionImpl(name),
            children: self.tcx.intern_list(&[self.self_ty.unwrap()]),
        })
    }

    pub fn shape_of_ty(&self, ty: SigTy) -> TyShape {
        let s = &self.tcx.session;

        match ty.r(s).kind {
            SigTyKind::SelfTy => self.self_ty.expect("no self type provided"),

            // It's always safe to be conservative with these types.
            SigTyKind::HrtbVar(_)
            | SigTyKind::Infer
            | SigTyKind::Generic(_)
            | SigTyKind::Alias(_, _)
            | SigTyKind::Project(_)
            | SigTyKind::FnDef(_)
            | SigTyKind::UsedDyn(_)
            | SigTyKind::Trait(_, _, _)
            | SigTyKind::Error(_) => TyShape::Hole,

            SigTyKind::Simple(kind) => TyShape::Solid(SolidTyShape {
                kind: SolidTyShapeKind::Simple(kind),
                children: self.tcx.intern_list(&[]),
            }),
            SigTyKind::Reference(_re, mutability, pointee) => TyShape::Solid(SolidTyShape {
                kind: SolidTyShapeKind::Reference(mutability),
                children: self.tcx.intern_list(&[self.shape_of_ty(pointee)]),
            }),
            SigTyKind::Adt(SigAdtInstance { def, params }) => TyShape::Solid(SolidTyShape {
                kind: SolidTyShapeKind::Adt(def),
                children: self.tcx.intern_list(
                    &params
                        .elems
                        .r(s)
                        .iter()
                        .filter_map(|ty| ty.as_ty())
                        .map(|ty| self.shape_of_ty(ty))
                        .collect::<Vec<_>>(),
                ),
            }),
            SigTyKind::Tuple(children) => TyShape::Solid(SolidTyShape {
                kind: SolidTyShapeKind::Tuple(children.r(s).len() as u32),
                children: self.tcx.intern_list(
                    &children
                        .r(s)
                        .iter()
                        .map(|&ty| self.shape_of_ty(ty))
                        .collect::<Vec<_>>(),
                ),
            }),
        }
    }
}

pub struct ImportedShapeEraser<'a, 'tcx> {
    pub ccx: &'a ClauseCx<'tcx>,
}

impl ImportedShapeEraser<'_, '_> {
    pub fn shape_of_trait_impl(&self, def: Obj<TraitItem>, args: &[TyOrRe], target: Ty) -> TyShape {
        let tcx = self.ccx.tcx();
        let s = self.ccx.session();

        debug_assert_eq!(args.len(), *def.r(s).regular_generic_count as usize);

        TyShape::Solid(SolidTyShape {
            kind: SolidTyShapeKind::TraitImpl(def),
            children: tcx.intern_list(
                &([self.shape_of_ty(target)]
                    .into_iter()
                    .chain(
                        args.iter()
                            .filter_map(|ty| ty.as_ty())
                            .map(|ty| self.shape_of_ty(ty)),
                    )
                    .collect::<Vec<_>>()),
            ),
        })
    }

    pub fn shape_of_inherent_method(&self, receiver: Ty, name: Symbol) -> TyShape {
        let tcx = self.ccx.tcx();

        TyShape::Solid(SolidTyShape {
            kind: SolidTyShapeKind::InherentMethodImpl(name),
            children: tcx.intern_list(&[self.shape_of_ty(receiver)]),
        })
    }

    pub fn shape_of_inherent_function(&self, self_ty: Ty, name: Symbol) -> TyShape {
        let tcx = self.ccx.tcx();

        TyShape::Solid(SolidTyShape {
            kind: SolidTyShapeKind::InherentFunctionImpl(name),
            children: tcx.intern_list(&[self.shape_of_ty(self_ty)]),
        })
    }

    pub fn shape_of_ty(&self, ty: Ty) -> TyShape {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        match *self.ccx.peel_ty_infer_var_without_poll(ty).r(s) {
            // It's always safe to be conservative with these types.
            TyKind::HrtbVar(_)
            | TyKind::HrtbProjection(_)
            | TyKind::InferVar(_)
            | TyKind::Universal(_)
            | TyKind::FnDef(_)
            | TyKind::Trait(_, _, _)
            | TyKind::Error(_) => TyShape::Hole,

            TyKind::Simple(kind) => TyShape::Solid(SolidTyShape {
                kind: SolidTyShapeKind::Simple(kind),
                children: tcx.intern_list(&[]),
            }),
            TyKind::Reference(_re, mutability, pointee) => TyShape::Solid(SolidTyShape {
                kind: SolidTyShapeKind::Reference(mutability),
                children: tcx.intern_list(&[self.shape_of_ty(pointee)]),
            }),
            TyKind::Adt(AdtInstance { def, params }) => TyShape::Solid(SolidTyShape {
                kind: SolidTyShapeKind::Adt(def),
                children: tcx.intern_list(
                    &params
                        .r(s)
                        .iter()
                        .filter_map(|ty| ty.as_ty())
                        .map(|ty| self.shape_of_ty(ty))
                        .collect::<Vec<_>>(),
                ),
            }),
            TyKind::Tuple(children) => TyShape::Solid(SolidTyShape {
                kind: SolidTyShapeKind::Tuple(children.r(s).len() as u32),
                children: tcx.intern_list(
                    &children
                        .r(s)
                        .iter()
                        .map(|&ty| self.shape_of_ty(ty))
                        .collect::<Vec<_>>(),
                ),
            }),
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
    conditionally_matched_by: FastHashMap<SolidTyShapeKind, ConditionalMatcher>,
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
        base::arena::HasListInterner as _,
        semantic::syntax::{SimpleTyKind, TyCtxt},
    };
    use clay_core::FastHashSet;

    #[test]
    fn impl_cache_map() {
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
            .collect::<FastHashSet<_>>(),
            FastHashSet::from_iter(["_", "(_, bool)", "(str, _)"]),
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
            .collect::<FastHashSet<_>>(),
            FastHashSet::from_iter(["_", "(_, bool)", "(str, _)"]),
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
            .collect::<FastHashSet<_>>(),
            FastHashSet::from_iter(["_", "(str, _)"]),
        );
    }
}
