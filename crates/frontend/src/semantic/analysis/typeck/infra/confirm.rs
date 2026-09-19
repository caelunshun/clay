use crate::{
    base::{
        arena::{LateInit, Obj},
        syntax::Span,
    },
    semantic::{
        analysis::typeck::BodyCtxt,
        syntax::{SigTy, ThirExpr, ThirExprKind, Ty},
    },
    utils::mem::ArenaRc,
};
use bumpalo::Bump;
use derive_where::derive_where;
use std::{cell::Cell, mem, rc::Rc};

// === Core === //

#[derive(Default)]
pub struct ThirQueue<'a, 'tcx> {
    arena: Rc<Bump>,
    queue: Vec<ArenaRc<dyn 'a + InitTarget<'a, 'tcx>>>,
}

impl<'a, 'tcx> ThirQueue<'a, 'tcx> {
    pub fn confirm_everything(bcx: &mut BodyCtxt<'a, 'tcx>) {
        for elem in mem::take(&mut bcx.thir_queue.queue) {
            elem.ensure_init(bcx);
        }
    }
}

#[derive_where(Clone)]
pub struct ThirLateInit<'a, 'tcx, T> {
    inner: ArenaRc<dyn 'a + DataContainer<'a, 'tcx, Data = T>>,
}

trait InitTarget<'a, 'tcx> {
    fn ensure_init(&self, bcx: &mut BodyCtxt<'a, 'tcx>);
}

trait DataContainer<'a, 'tcx>: InitTarget<'a, 'tcx> {
    type Data;

    fn data(&self) -> &Self::Data;
}

struct ThirLateInitInner<T, F> {
    data: T,
    init_fn: Cell<Option<F>>,
}

impl<'a, 'tcx, T, F> InitTarget<'a, 'tcx> for ThirLateInitInner<T, F>
where
    F: FnOnce(&mut BodyCtxt<'a, 'tcx>, &T),
{
    fn ensure_init(&self, bcx: &mut BodyCtxt<'a, 'tcx>) {
        if let Some(init_fn) = self.init_fn.take() {
            init_fn(bcx, &self.data);
        }
    }
}

impl<'a, 'tcx, T, F> DataContainer<'a, 'tcx> for ThirLateInitInner<T, F>
where
    F: FnOnce(&mut BodyCtxt<'a, 'tcx>, &T),
{
    type Data = T;

    fn data(&self) -> &Self::Data {
        &self.data
    }
}

impl<'a, 'tcx, T> ThirLateInit<'a, 'tcx, T> {
    pub fn new(
        bcx: &mut BodyCtxt<'a, 'tcx>,
        data: T,
        init: impl 'a + FnOnce(&mut BodyCtxt<'a, 'tcx>, &T),
    ) -> Self
    where
        T: 'a,
    {
        let inner = ArenaRc::new(
            bcx.thir_queue.arena.clone(),
            ThirLateInitInner {
                data,
                init_fn: Cell::new(Some(init)),
            },
        );

        bcx.thir_queue
            .queue
            .push(ArenaRc::map::<dyn 'a + InitTarget<'a, 'tcx>>(
                inner.clone(),
                |v| v,
            ));

        let inner = ArenaRc::map::<dyn 'a + DataContainer<'a, 'tcx, Data = T>>(inner, |v| v);

        Self { inner }
    }

    pub fn data(&self) -> &T {
        self.inner.data()
    }

    pub fn ensure_init(&self, bcx: &mut BodyCtxt<'a, 'tcx>) {
        self.inner.ensure_init(bcx);
    }
}

// === Types === //

#[derive(Clone)]
pub struct ThirLateTy<'a, 'tcx> {
    inner: ThirLateInit<'a, 'tcx, ThirLateTypeInner>,
}

struct ThirLateTypeInner {
    span: Span,
    imported: Ty,
    exported: LateInit<SigTy>,
}

impl<'a, 'tcx> ThirLateTy<'a, 'tcx> {
    pub fn new(bcx: &mut BodyCtxt<'a, 'tcx>, span: Span, ty: Ty) -> Self {
        Self {
            inner: ThirLateInit::new(
                bcx,
                ThirLateTypeInner {
                    span,
                    imported: ty,
                    exported: LateInit::uninit(),
                },
                |bcx, value| {
                    LateInit::init(
                        &value.exported,
                        bcx.ccx_mut().export(value.span, value.imported),
                    );
                },
            ),
        }
    }

    pub fn span(&self) -> Span {
        self.inner.data().span
    }

    pub fn imported(&self) -> Ty {
        self.inner.data().imported
    }

    pub fn exported(&self, bcx: &mut BodyCtxt<'a, 'tcx>) -> SigTy {
        self.inner.ensure_init(bcx);
        *self.inner.data().exported
    }
}

// === Expressions === //

pub struct ThirLateExpr<'a, 'tcx> {
    inner: ThirLateInit<'a, 'tcx, Obj<ThirExpr>>,
}

impl<'a, 'tcx> ThirLateExpr<'a, 'tcx> {
    pub fn new(
        bcx: &mut BodyCtxt<'a, 'tcx>,
        span: Span,
        ty: ThirLateTy<'a, 'tcx>,
        init: impl 'a + FnOnce(&mut BodyCtxt<'a, 'tcx>) -> ThirExprKind,
    ) -> Self {
        let s = bcx.session();

        Self {
            inner: ThirLateInit::new(
                bcx,
                Obj::new(
                    ThirExpr {
                        span,
                        ty: LateInit::uninit(),
                        kind: LateInit::uninit(),
                    },
                    s,
                ),
                move |bcx, expr| {
                    let s = bcx.session();

                    LateInit::init(&expr.r(s).ty, ty.exported(bcx));
                    LateInit::init(&expr.r(s).kind, init(bcx));
                },
            ),
        }
    }

    pub fn expr(&self) -> Obj<ThirExpr> {
        *self.inner.data()
    }

    pub fn kind(&self, bcx: &mut BodyCtxt<'a, 'tcx>) -> &'tcx ThirExprKind {
        let s = bcx.session();

        self.inner.ensure_init(bcx);
        &self.inner.data().r(s).kind
    }
}
