use crate::{
    base::{
        arena::{LateInit, Obj},
        syntax::{HasSpan, Span},
    },
    semantic::{
        analysis::typeck::BodyCtxt,
        syntax::{HirLocal, ThirExpr, ThirExprKind, ThirLocal, Ty},
    },
    utils::mem::ArenaRc,
};
use bumpalo::Bump;
use derive_where::derive_where;
use std::{
    cell::{Cell, OnceCell},
    mem,
    rc::Rc,
};

// === ThirLateInitQueue === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum ThirConfirmPhase {
    InferHoles,
    ConfirmLocals,
    ConfirmExprs,
}

#[derive(Default)]
pub struct ThirLateInitQueue<'a, 'tcx> {
    arena: Rc<Bump>,
    queue: Vec<ThirLateInitQueueEntry<'a, 'tcx>>,
}

struct ThirLateInitQueueEntry<'a, 'tcx> {
    phase: ThirConfirmPhase,
    target: ArenaRc<dyn 'a + AnyErasedConfirm<'a, 'tcx>>,
}

trait AnyErasedConfirm<'a, 'tcx> {
    fn ensure_confirmed(&self, bcx: &mut BodyCtxt<'a, 'tcx>);
}

struct FnInitTarget<F>(Cell<Option<F>>);

impl<'a, 'tcx, F> AnyErasedConfirm<'a, 'tcx> for FnInitTarget<F>
where
    F: FnOnce(&mut BodyCtxt<'a, 'tcx>),
{
    fn ensure_confirmed(&self, bcx: &mut BodyCtxt<'a, 'tcx>) {
        if let Some(f) = self.0.take() {
            (f)(bcx);
        }
    }
}

impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
    pub fn queue_confirm_task(
        &mut self,
        phase: ThirConfirmPhase,
        f: impl 'a + FnOnce(&mut BodyCtxt<'a, 'tcx>),
    ) {
        self.thir_queue.queue.push(ThirLateInitQueueEntry {
            phase,
            target: ArenaRc::map::<dyn 'a + AnyErasedConfirm<'a, 'tcx>>(
                ArenaRc::new(
                    self.thir_queue.arena.clone(),
                    FnInitTarget(Cell::new(Some(f))),
                ),
                |v| v,
            ),
        });
    }

    pub fn finish_confirmation(&mut self) {
        loop {
            let mut queue = mem::take(&mut self.thir_queue.queue);
            if queue.is_empty() {
                break;
            }

            queue.sort_by_key(|v| v.phase);

            for elem in queue {
                elem.target.ensure_confirmed(self);
            }
        }
    }
}

// === ThirConfirm === //

#[derive_where(Clone)]
pub struct ThirLateInit<'a, 'tcx, T, V = ()> {
    inner: ArenaRc<dyn 'a + ErasedConfirm<'a, 'tcx, Early = T, Late = V>>,
}

trait ErasedConfirm<'a, 'tcx>: AnyErasedConfirm<'a, 'tcx> {
    type Early;
    type Late;

    fn early_data(&self) -> &Self::Early;

    fn late_data(&self, bcx: &mut BodyCtxt<'a, 'tcx>) -> &Self::Late;
}

struct ThirLateInitInner<T, V, F> {
    early_data: T,
    late_init_fn: Cell<Option<F>>,
    late_state: OnceCell<V>,
}

impl<'a, 'tcx, T, V, F> AnyErasedConfirm<'a, 'tcx> for ThirLateInitInner<T, V, F>
where
    F: FnOnce(&mut BodyCtxt<'a, 'tcx>, &T) -> V,
{
    fn ensure_confirmed(&self, bcx: &mut BodyCtxt<'a, 'tcx>) {
        _ = self.late_data(bcx);
    }
}

impl<'a, 'tcx, T, V, F> ErasedConfirm<'a, 'tcx> for ThirLateInitInner<T, V, F>
where
    F: FnOnce(&mut BodyCtxt<'a, 'tcx>, &T) -> V,
{
    type Early = T;
    type Late = V;

    fn early_data(&self) -> &Self::Early {
        &self.early_data
    }

    fn late_data(&self, bcx: &mut BodyCtxt<'a, 'tcx>) -> &Self::Late {
        self.late_state.get_or_init(|| {
            self.late_init_fn.take().expect("recursive initialization")(bcx, &self.early_data)
        })
    }
}

impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
    pub fn create_late_init<T, V, F>(
        &mut self,
        phase: ThirConfirmPhase,
        data: T,
        ensure_init: F,
    ) -> ThirLateInit<'a, 'tcx, T, V>
    where
        T: 'a,
        V: 'a,
        F: 'a + FnOnce(&mut Self, &T) -> V,
    {
        let inner = ArenaRc::new(
            self.thir_queue.arena.clone(),
            ThirLateInitInner {
                early_data: data,
                late_state: OnceCell::new(),
                late_init_fn: Cell::new(Some(ensure_init)),
            },
        );

        self.thir_queue.queue.push(ThirLateInitQueueEntry {
            phase,
            target: ArenaRc::map::<dyn 'a + AnyErasedConfirm<'a, 'tcx>>(inner.clone(), |v| v),
        });

        ThirLateInit {
            inner: ArenaRc::map::<dyn 'a + ErasedConfirm<'a, 'tcx, Early = T, Late = V>>(
                inner,
                |v| v,
            ),
        }
    }
}

impl<'a, 'tcx, T, V> ThirLateInit<'a, 'tcx, T, V> {
    pub fn early(&self) -> &T {
        self.inner.early_data()
    }

    pub fn late(&self, bcx: &mut BodyCtxt<'a, 'tcx>) -> &V {
        self.inner.late_data(bcx)
    }

    pub fn ensure_init(&self, bcx: &mut BodyCtxt<'a, 'tcx>) {
        self.late(bcx);
    }

    pub fn early_ensure_init(&self, bcx: &mut BodyCtxt<'a, 'tcx>) -> &T {
        self.ensure_init(bcx);
        self.early()
    }
}

// === Locals === //

#[derive(Clone)]
pub struct ThirLateLocal<'a, 'tcx> {
    inner: ThirLateInit<'a, 'tcx, ThirLateLocalInfo, Obj<ThirLocal>>,
}

struct ThirLateLocalInfo {
    hir: Obj<HirLocal>,
    ty: Ty,
}

impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
    pub fn create_late_local(&mut self, hir: Obj<HirLocal>, ty: Ty) -> ThirLateLocal<'a, 'tcx> {
        ThirLateLocal {
            inner: self.create_late_init(
                ThirConfirmPhase::ConfirmLocals,
                ThirLateLocalInfo { hir, ty },
                move |bcx, inner| {
                    let s = bcx.session();

                    let ty = bcx.ccx_mut().export(inner.hir.r(s).name.span(), inner.ty);

                    Obj::new(
                        ThirLocal {
                            mutability: inner.hir.r(s).mutability,
                            name: inner.hir.r(s).name,
                            ty,
                        },
                        s,
                    )
                },
            ),
        }
    }
}

impl<'a, 'tcx> ThirLateLocal<'a, 'tcx> {
    pub fn ty(&self) -> Ty {
        self.inner.early().ty
    }

    pub fn hir(&self) -> Obj<HirLocal> {
        self.inner.early().hir
    }

    pub fn thir(&self, bcx: &mut BodyCtxt<'a, 'tcx>) -> Obj<ThirLocal> {
        *self.inner.late(bcx)
    }
}

// === Expressions === //

#[derive(Clone)]
pub struct ThirLateExpr<'a, 'tcx> {
    inner: ThirLateInit<'a, 'tcx, ThirLateExprInner>,
}

struct ThirLateExprInner {
    expr: Obj<ThirExpr>,
    ty: Ty,
}

impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
    pub fn create_late_expr(
        &mut self,
        span: Span,
        ty: Ty,
        kind: impl 'a + FnOnce(&mut Self) -> ThirExprKind,
    ) -> ThirLateExpr<'a, 'tcx> {
        let s = self.session();

        ThirLateExpr {
            inner: self.create_late_init(
                ThirConfirmPhase::ConfirmExprs,
                ThirLateExprInner {
                    expr: Obj::new(
                        ThirExpr {
                            span,
                            ty: LateInit::uninit(),
                            kind: LateInit::uninit(),
                        },
                        s,
                    ),
                    ty,
                },
                move |bcx, inner| {
                    let s = bcx.session();

                    LateInit::init(
                        &inner.expr.r(s).ty,
                        bcx.ccx_mut().export(inner.expr.r(s).span, inner.ty),
                    );

                    LateInit::init(&inner.expr.r(s).kind, kind(bcx));
                },
            ),
        }
    }
}

impl<'a, 'tcx> ThirLateExpr<'a, 'tcx> {
    pub fn ty(&self) -> Ty {
        self.inner.early().ty
    }

    pub fn expr(&self) -> Obj<ThirExpr> {
        self.inner.early().expr
    }

    pub fn kind(&self, bcx: &mut BodyCtxt<'a, 'tcx>) -> &'tcx ThirExprKind {
        let s = bcx.session();

        &self.inner.early_ensure_init(bcx).expr.r(s).kind
    }
}
