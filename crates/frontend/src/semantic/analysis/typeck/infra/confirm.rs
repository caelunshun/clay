use crate::{
    base::{
        ErrorGuaranteed,
        arena::{HasInterner as _, LateInit, Obj},
        syntax::{HasSpan, Span},
    },
    semantic::{
        analysis::typeck::BodyCtxt,
        syntax::{HirLocal, ThirExpr, ThirExprKind, ThirLocal, ThirPat, ThirPatKind, Ty, TyKind},
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

impl<'a, 'tcx, T, V> ThirLateInit<'a, 'tcx, T, V> {
    pub fn new<F>(
        phase: ThirConfirmPhase,
        data: T,
        ensure_init: F,
        bcx: &mut BodyCtxt<'a, 'tcx>,
    ) -> Self
    where
        T: 'a,
        V: 'a,
        F: 'a + FnOnce(&mut BodyCtxt<'a, 'tcx>, &T) -> V,
    {
        let inner = ArenaRc::new(
            bcx.thir_queue.arena.clone(),
            ThirLateInitInner {
                early_data: data,
                late_state: OnceCell::new(),
                late_init_fn: Cell::new(Some(ensure_init)),
            },
        );

        bcx.thir_queue.queue.push(ThirLateInitQueueEntry {
            phase,
            target: ArenaRc::map::<dyn 'a + AnyErasedConfirm<'a, 'tcx>>(inner.clone(), |v| v),
        });

        Self {
            inner: ArenaRc::map::<dyn 'a + ErasedConfirm<'a, 'tcx, Early = T, Late = V>>(
                inner,
                |v| v,
            ),
        }
    }

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

impl<'a, 'tcx> ThirLateLocal<'a, 'tcx> {
    pub fn new(
        hir: Obj<HirLocal>,
        ty: Ty,
        bcx: &mut BodyCtxt<'a, 'tcx>,
    ) -> ThirLateLocal<'a, 'tcx> {
        ThirLateLocal {
            inner: ThirLateInit::new(
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
                bcx,
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

// === Patterns === //

#[derive(Clone)]
pub struct ThirLatePat<'a, 'tcx> {
    inner: ThirLateInit<'a, 'tcx, ThirLatePatInner>,
}

struct ThirLatePatInner {
    pat: Obj<ThirPat>,
    ty: Ty,
}

impl<'a, 'tcx> ThirLatePat<'a, 'tcx> {
    pub fn new(
        span: Span,
        ty: Ty,
        kind: impl 'a + FnOnce(&mut BodyCtxt<'a, 'tcx>) -> ThirPatKind,
        bcx: &mut BodyCtxt<'a, 'tcx>,
    ) -> ThirLatePat<'a, 'tcx> {
        let s = bcx.session();

        ThirLatePat {
            inner: ThirLateInit::new(
                ThirConfirmPhase::ConfirmExprs,
                ThirLatePatInner {
                    pat: Obj::new(
                        ThirPat {
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
                        &inner.pat.r(s).ty,
                        bcx.ccx_mut().export(inner.pat.r(s).span, inner.ty),
                    );

                    LateInit::init(&inner.pat.r(s).kind, kind(bcx));
                },
                bcx,
            ),
        }
    }

    pub fn ty(&self) -> Ty {
        self.inner.early().ty
    }

    pub fn thir(&self) -> Obj<ThirPat> {
        self.inner.early().pat
    }

    pub fn kind(&self, bcx: &mut BodyCtxt<'a, 'tcx>) -> &'tcx ThirPatKind {
        let s = bcx.session();

        &self.inner.early_ensure_init(bcx).pat.r(s).kind
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

impl<'a, 'tcx> ThirLateExpr<'a, 'tcx> {
    pub fn new(
        span: Span,
        ty: Ty,
        kind: impl 'a + FnOnce(&mut BodyCtxt<'a, 'tcx>) -> ThirExprKind,
        bcx: &mut BodyCtxt<'a, 'tcx>,
    ) -> ThirLateExpr<'a, 'tcx> {
        let s = bcx.session();

        ThirLateExpr {
            inner: ThirLateInit::new(
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
                bcx,
            ),
        }
    }

    pub fn new_err(
        span: Span,
        err: ErrorGuaranteed,
        bcx: &mut BodyCtxt<'a, 'tcx>,
    ) -> ThirLateExpr<'a, 'tcx> {
        let tcx = bcx.tcx();

        Self::new(
            span,
            tcx.intern(TyKind::Error(err)),
            move |_bcx| ThirExprKind::Error(err),
            bcx,
        )
    }

    pub fn ty(&self) -> Ty {
        self.inner.early().ty
    }

    pub fn thir(&self) -> Obj<ThirExpr> {
        self.inner.early().expr
    }

    pub fn kind(&self, bcx: &mut BodyCtxt<'a, 'tcx>) -> &'tcx ThirExprKind {
        let s = bcx.session();

        &self.inner.early_ensure_init(bcx).expr.r(s).kind
    }
}
