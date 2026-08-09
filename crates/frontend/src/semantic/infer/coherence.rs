use crate::{
    base::{
        arena::{HasListInterner as _, Obj},
        syntax::Symbol,
    },
    semantic::{
        infer::ClauseCx,
        syntax::{
            AdtInstance, Crate, FnDef, ImplItem, SigAdtInstance, SigTy, SigTyKind, SigTyOrRe,
            SolidTyShape, SolidTyShapeKind, TraitItem, TraitParam, TraitSpec, Ty, TyCtxt, TyKind,
            TyOrRe, TyShape, TyShapeMap,
        },
    },
};

// === CoherenceMap === //

#[derive(Debug, Default)]
pub struct CoherenceMap {
    by_shape: TyShapeMap<CoherenceMapEntry>,
}

#[derive(Debug, Copy, Clone)]
pub enum CoherenceMapEntry {
    TraitImpl(Obj<ImplItem>),
    InherentMethod(Obj<FnDef>),
}

impl CoherenceMap {
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
                            &trait_.params.r(s)[..arg_count],
                            *item.r(s).target,
                        ),
                        CoherenceMapEntry::TraitImpl(item),
                        s,
                    );
                }
                None => {
                    for &method in &**item.r(s).methods {
                        let method = method.unwrap();

                        self.by_shape.insert(
                            trait_eraser.shape_of_inherent_function(method.r(s).name.text),
                            CoherenceMapEntry::InherentMethod(method),
                            s,
                        );

                        if !*method.r(s).has_self_param {
                            continue;
                        }

                        // We perform an ad-hoc self-type substitution on the receiver to tighten
                        // its bounds. We don't need to bring in a full `ClauseCx` to do this
                        // because entries in the `CoherenceMap` are only approximations.
                        let receiver = method.r(s).args.r(s)[0].ty;

                        self.by_shape.insert(
                            trait_eraser.shape_of_inherent_method(receiver, method.r(s).name.text),
                            CoherenceMapEntry::InherentMethod(method),
                            s,
                        );
                    }
                }
            }
        }
    }

    pub fn gather_inherent_impl_method_candidates<'a>(
        &'a self,
        ccx: &'a ClauseCx<'a>,
        receiver: Ty,
        name: Symbol,
    ) -> impl Iterator<Item = Obj<FnDef>> + 'a {
        let s = ccx.session();
        let eraser = ImportedShapeEraser { ccx };

        self.by_shape
            .lookup(eraser.shape_of_inherent_method(receiver, name), s)
            .map(|v| {
                let CoherenceMapEntry::InherentMethod(v) = *v else {
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
    ) -> impl Iterator<Item = Obj<FnDef>> + 'a {
        let s = ccx.session();
        let eraser = ImportedShapeEraser { ccx };

        self.by_shape
            .lookup(eraser.shape_of_inherent_function(self_ty, name), s)
            .map(|v| {
                let CoherenceMapEntry::InherentMethod(v) = *v else {
                    unreachable!()
                };

                v
            })
    }

    pub fn gather_trait_impl_candidates<'a>(
        &'a self,
        ccx: &'a ClauseCx<'a>,
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
                let CoherenceMapEntry::TraitImpl(v) = *v else {
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
            SigTyKind::Trait(_re, _muta, _intern) => todo!(),
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
            | TyKind::UniversalVar(_)
            | TyKind::FnDef(_)
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
            TyKind::Trait(_re, _muta, _intern) => todo!(),
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
