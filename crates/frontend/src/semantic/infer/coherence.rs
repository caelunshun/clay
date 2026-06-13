use crate::{
    base::{arena::Obj, syntax::Symbol},
    semantic::syntax::{
        Crate, FnDef, ImplItem, SpannedTy, TraitParam, TraitSpec, Ty, TyCtxt, TyFolder,
        TyFolderInfallibleExt, TyKind, TyShapeMap,
    },
};
use std::convert::Infallible;

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

            match *item.r(s).trait_ {
                Some(trait_) => {
                    let arg_count = *trait_.value.def.r(s).regular_generic_count as usize;
                    self.by_shape.insert(
                        tcx.shape_of_trait_def(
                            trait_.value.def,
                            &trait_.value.params.r(s)[..arg_count],
                            item.r(s).target.value,
                        ),
                        CoherenceMapEntry::TraitImpl(item),
                        s,
                    );
                }
                None => {
                    for &method in &**item.r(s).methods {
                        let method = method.unwrap();

                        self.by_shape.insert(
                            tcx.shape_of_inherent_function(
                                item.r(s).target.value,
                                method.r(s).name.text,
                            ),
                            CoherenceMapEntry::InherentMethod(method),
                            s,
                        );

                        if !*method.r(s).has_self_param {
                            continue;
                        }

                        // We perform an ad-hoc self-type substitution on the receiver to tighten
                        // its bounds. We don't need to bring in a full `ClauseCx` to do this
                        // because entries in the `CoherenceMap` are only approximations.
                        let receiver = method.r(s).args.r(s)[0].ty.value;
                        let receiver = SigSelfTypeFolder {
                            tcx,
                            self_ty: item.r(s).target.value,
                        }
                        .fold(receiver);

                        self.by_shape.insert(
                            tcx.shape_of_inherent_method(receiver, method.r(s).name.text),
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
        tcx: &'a TyCtxt,
        receiver: Ty,
        name: Symbol,
    ) -> impl Iterator<Item = Obj<FnDef>> + 'a {
        let s = &tcx.session;

        self.by_shape
            .lookup(tcx.shape_of_inherent_method(receiver, name), s)
            .map(|v| {
                let CoherenceMapEntry::InherentMethod(v) = *v else {
                    unreachable!()
                };

                v
            })
    }

    pub fn gather_inherent_impl_function_candidates<'a>(
        &'a self,
        tcx: &'a TyCtxt,
        self_ty: Ty,
        name: Symbol,
    ) -> impl Iterator<Item = Obj<FnDef>> + 'a {
        let s = &tcx.session;

        self.by_shape
            .lookup(tcx.shape_of_inherent_function(self_ty, name), s)
            .map(|v| {
                let CoherenceMapEntry::InherentMethod(v) = *v else {
                    unreachable!()
                };

                v
            })
    }

    pub fn gather_trait_impl_candidates<'a>(
        &'a self,
        tcx: &'a TyCtxt,
        lhs: Ty,
        rhs: TraitSpec,
    ) -> impl Iterator<Item = Obj<ImplItem>> + 'a {
        let s = &tcx.session;

        self.by_shape
            .lookup(
                tcx.shape_of_trait_def(
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

// === Helpers === //

struct SigSelfTypeFolder<'tcx> {
    tcx: &'tcx TyCtxt,
    self_ty: Ty,
}

impl<'tcx> TyFolder<'tcx> for SigSelfTypeFolder<'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    fn fold_ty(&mut self, ty: SpannedTy) -> Result<Ty, Self::Error> {
        let s = self.session();

        if matches!(ty.value.r(s), TyKind::SigThis) {
            return Ok(self.self_ty);
        }

        Ok(self.super_spanned(ty))
    }
}
