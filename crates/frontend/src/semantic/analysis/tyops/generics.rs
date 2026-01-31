use crate::{
    base::arena::{LateInit, Obj},
    semantic::{
        analysis::{TyCtxt, TyVisitable, TyVisitor, TyVisitorExt},
        syntax::{AnyGeneric, GenericBinder, PosInBinder, Re, SpannedRe, SpannedTy, TyKind},
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

    fn visit_re(&mut self, re: SpannedRe) -> ControlFlow<Self::Break> {
        match re.value {
            Re::SigGeneric(generic) => {
                (self.f)(AnyGeneric::Re(generic))?;
            }
            Re::Gc
            | Re::SigInfer
            | Re::HrtbVar(_)
            | Re::InferVar(_)
            | Re::UniversalVar(_)
            | Re::Erased
            | Re::Error(_) => {
                // (not a generic)
            }
        }

        self.walk_spanned_fallible(re)?;

        ControlFlow::Continue(())
    }

    fn visit_ty(&mut self, ty: SpannedTy) -> ControlFlow<Self::Break> {
        match *ty.value.r(self.session()) {
            TyKind::SigGeneric(generic) => {
                (self.f)(AnyGeneric::Ty(generic))?;
            }

            TyKind::SigThis
            | TyKind::SigInfer
            | TyKind::SigProject(_)
            | TyKind::Simple(_)
            | TyKind::Reference(_, _, _)
            | TyKind::Adt(_)
            | TyKind::Trait(_, _, _)
            | TyKind::Tuple(_)
            | TyKind::FnDef(_)
            | TyKind::HrtbVar(_)
            | TyKind::InferVar(_)
            | TyKind::UniversalVar(_)
            | TyKind::Error(_) => {
                // (not a generic)
            }
        }

        self.walk_spanned_fallible(ty)?;

        ControlFlow::Continue(())
    }
}
