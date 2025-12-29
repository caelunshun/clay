use crate::{
    base::{
        arena::{HasInterner, HasListInterner, LateInit, Obj},
        syntax::Span,
    },
    semantic::{
        analysis::{TyCtxt, TyVisitable, TyVisitor, TyVisitorExt},
        syntax::{
            AnyGeneric, GenericBinder, PosInBinder, Re, RegionGeneric, TraitInstance, TraitParam,
            TraitSpec, TyKind, TyOrRe, TyOrReList, TypeGeneric,
        },
    },
};
use derive_where::derive_where;
use std::{marker::PhantomData, ops::ControlFlow};

impl TyCtxt {
    pub fn seal_generic_binder(&self, binder: GenericBinder) -> Obj<GenericBinder> {
        let s = &self.session;

        let binder = Obj::new(binder, s);

        for (i, generic) in binder.r(s).defs.iter().enumerate() {
            LateInit::init(
                match generic {
                    AnyGeneric::Re(generic) => &generic.r(s).binder,
                    AnyGeneric::Ty(generic) => &generic.r(s).binder,
                },
                PosInBinder {
                    def: binder,
                    idx: i as u32,
                },
            );
        }

        binder
    }

    pub fn convert_generic_binder_into_instance_args(
        &self,
        binder: Obj<GenericBinder>,
    ) -> TyOrReList {
        let s = &self.session;

        self.intern_list(
            &binder
                .r(s)
                .defs
                .iter()
                .map(|generic| match generic {
                    AnyGeneric::Re(generic) => TyOrRe::Re(Re::SigUniversal(*generic)),
                    AnyGeneric::Ty(generic) => {
                        TyOrRe::Ty(self.intern(TyKind::SigUniversal(*generic)))
                    }
                })
                .collect::<Vec<_>>(),
        )
    }

    pub fn convert_trait_instance_to_spec(&self, instance: TraitInstance) -> TraitSpec {
        TraitSpec {
            def: instance.def,
            params: self.intern_list(
                &instance
                    .params
                    .r(&self.session)
                    .iter()
                    .map(|&arg| TraitParam::Equals(arg))
                    .collect::<Vec<_>>(),
            ),
        }
    }

    pub fn mentioned_sig_generics<B>(
        &self,
        ty: impl TyVisitable,
        f: impl FnMut(AnyGeneric) -> ControlFlow<B>,
    ) -> ControlFlow<B> {
        SigGenericMentionVisitor {
            _ty: PhantomData,
            tcx: self,
            f,
        }
        .visit_fallible(ty)
    }
}

#[derive_where(Copy, Clone; F)]
pub struct SigGenericMentionVisitor<'tcx, F, B> {
    _ty: PhantomData<fn() -> B>,
    tcx: &'tcx TyCtxt,
    f: F,
}

impl<'tcx, F, B> SigGenericMentionVisitor<'tcx, F, B>
where
    F: FnMut(AnyGeneric) -> ControlFlow<B>,
{
    pub fn new(tcx: &'tcx TyCtxt, f: F) -> Self {
        Self {
            _ty: PhantomData,
            tcx,
            f,
        }
    }
}

impl<'tcx, F, B> TyVisitor<'tcx> for SigGenericMentionVisitor<'tcx, F, B>
where
    F: FnMut(AnyGeneric) -> ControlFlow<B>,
{
    type Break = B;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    fn visit_re_sig_universal_use(
        &mut self,
        _span: Option<Span>,
        generic: Obj<RegionGeneric>,
    ) -> ControlFlow<Self::Break> {
        (self.f)(AnyGeneric::Re(generic))
    }

    fn visit_ty_sig_universal_use(
        &mut self,
        _span: Option<Span>,
        generic: Obj<TypeGeneric>,
    ) -> ControlFlow<Self::Break> {
        (self.f)(AnyGeneric::Ty(generic))
    }
}
