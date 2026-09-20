use crate::{
    base::{
        Diag, ErrorGuaranteed,
        arena::{HasInterner, LateInit, Obj},
        syntax::{HasSpan, Span},
    },
    semantic::{
        analysis::typeck::BodyCtxt,
        syntax::{
            HirBlock, HirExpr, HirLocal, HirPat, InferTyVar, ThirBlock, ThirExpr, ThirExprKind,
            ThirLocal, ThirPat, ThirPatKind, Ty, TyKind,
        },
    },
    utils::{hash::FxHashMap, mem::ArenaRc},
};
use bumpalo::Bump;
use derive_where::derive_where;
use std::{cell::Cell, rc::Rc};

// === Public === //

#[derive(Default)]
pub struct BodyCtxtConfirmState<'a, 'tcx> {
    arena: Rc<Bump>,
    started_confirmation: bool,
    expressions: ConfirmMap<'a, 'tcx, HirExpr, ThirExpr>,
    patterns: ConfirmMap<'a, 'tcx, HirPat, ThirPat>,
    locals: FxHashMap<Obj<HirLocal>, Obj<ThirLocal>>,
    fallback_infers: Vec<InferTyVar>,
}

#[derive(Debug, Copy, Clone)]
pub struct ThirExprResolution {
    pub pre_coerce: Obj<ThirExpr>,
    pub post_coerce: Obj<ThirExpr>,
}

#[derive(Debug, Copy, Clone)]
pub struct ThirPatResolution {
    pub inner: Obj<ThirPat>,
    pub outer: Obj<ThirPat>,
}

#[derive(Debug, Copy, Clone)]
pub struct ThirExprConfirmedWithTy {
    pub ty: Ty,
}

impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
    pub fn resolve_thir_expr(&mut self, hir: Obj<HirExpr>) -> ThirExprResolution {
        let s = self.session();

        assert!(self.confirm_state.started_confirmation);

        let ConfirmResolution { start, end } = ConfirmMap::resolve(
            self,
            |bcx| &mut bcx.confirm_state.expressions,
            ConfirmOrder::BuildingOutwards,
            hir.r(s).span,
            hir,
        );

        ThirExprResolution {
            pre_coerce: start,
            post_coerce: end,
        }
    }

    pub fn put_thir_expr(
        &mut self,
        hir: Obj<HirExpr>,
        ty: Ty,
        f: impl 'a + FnOnce(&mut Self) -> ThirExprKind,
    ) -> ThirExprConfirmedWithTy {
        assert!(!self.confirm_state.started_confirmation);

        self.confirm_state
            .expressions
            .put(self.confirm_state.arena.clone(), hir, ty, f);

        ThirExprConfirmedWithTy { ty }
    }

    pub fn put_thir_err(
        &mut self,
        hir: Obj<HirExpr>,
        err: ErrorGuaranteed,
    ) -> ThirExprConfirmedWithTy {
        let tcx = self.tcx();

        self.put_thir_expr(hir, tcx.intern(TyKind::Error(err)), move |_bcx| {
            ThirExprKind::Error(err)
        })
    }

    pub fn refine_thir_expr(
        &mut self,
        hir: Obj<HirExpr>,
        ty: Ty,
        f: impl 'a + FnOnce(&mut Self, Obj<ThirExpr>) -> ThirExprKind,
    ) {
        assert!(!self.confirm_state.started_confirmation);

        self.confirm_state
            .expressions
            .refine(self.confirm_state.arena.clone(), hir, ty, f);
    }

    pub fn assert_thir_expr_defined(&self, hir: Obj<HirExpr>) {
        assert!(!self.confirm_state.started_confirmation);

        assert!(
            self.confirm_state.expressions.is_defined(hir),
            "expression not defined"
        );
    }

    pub fn resolve_thir_pat(&mut self, hir: Obj<HirPat>) -> ThirPatResolution {
        let s = self.session();

        assert!(self.confirm_state.started_confirmation);

        let ConfirmResolution { start, end } = ConfirmMap::resolve(
            self,
            |bcx| &mut bcx.confirm_state.patterns,
            ConfirmOrder::BuildingInwards,
            hir.r(s).span,
            hir,
        );

        ThirPatResolution {
            inner: start,
            outer: end,
        }
    }

    pub fn put_thir_pat(
        &mut self,
        hir: Obj<HirPat>,
        ty: Ty,
        f: impl 'a + FnOnce(&mut Self) -> ThirPatKind,
    ) {
        assert!(!self.confirm_state.started_confirmation);

        self.confirm_state
            .patterns
            .put(self.confirm_state.arena.clone(), hir, ty, f);
    }

    pub fn refine_thir_pat(
        &mut self,
        hir: Obj<HirPat>,
        ty: Ty,
        f: impl 'a + FnOnce(&mut Self, Obj<ThirPat>) -> ThirPatKind,
    ) {
        assert!(!self.confirm_state.started_confirmation);

        self.confirm_state
            .patterns
            .refine(self.confirm_state.arena.clone(), hir, ty, f);
    }

    pub fn assert_thir_pat_defined(&self, hir: Obj<HirPat>) {
        assert!(!self.confirm_state.started_confirmation);

        assert!(
            self.confirm_state.patterns.is_defined(hir),
            "pattern not defined"
        );
    }

    pub fn register_infer_with_fallback(&mut self, var: InferTyVar) {
        self.confirm_state.fallback_infers.push(var);
    }

    pub fn resolve_thir_local(&mut self, hir: Obj<HirLocal>) -> Obj<ThirLocal> {
        let s = self.session();

        let ty = self.type_of_local(hir);

        *self.confirm_state.locals.entry(hir).or_insert_with(|| {
            let hir = hir.r(s);

            Obj::new(
                ThirLocal {
                    mutability: hir.mutability,
                    name: hir.name,
                    ty: self.ccx.export(hir.name.span(), ty),
                },
                s,
            )
        })
    }

    pub fn resolve_thir_block(&mut self, hir: Obj<HirBlock>) -> Obj<ThirBlock> {
        todo!()
    }

    pub fn begin_confirmation(&mut self) {
        assert!(!self.confirm_state.started_confirmation);

        self.confirm_state.started_confirmation = true;

        // TODO: handle fallbacks
    }
}

// === Internals === //

trait Confirmable<'a, 'tcx>: Sized + 'static {
    type Meta;
    type Body;

    fn create_placeholder(bcx: &mut BodyCtxt<'a, 'tcx>, span: Span, meta: &Self::Meta)
    -> Obj<Self>;

    fn init_placeholder(bcx: &mut BodyCtxt<'a, 'tcx>, target: Obj<Self>, body: Self::Body);

    fn create_err(bcx: &mut BodyCtxt<'a, 'tcx>, span: Span, err: ErrorGuaranteed) -> Obj<Self>;
}

impl<'a, 'tcx> Confirmable<'a, 'tcx> for ThirExpr {
    type Meta = Ty;
    type Body = ThirExprKind;

    fn create_placeholder(
        bcx: &mut BodyCtxt<'a, 'tcx>,
        span: Span,
        meta: &Self::Meta,
    ) -> Obj<Self> {
        let s = bcx.session();

        Obj::new(
            ThirExpr {
                span,
                ty: bcx.ccx_mut().export(span, *meta),
                kind: LateInit::uninit(),
            },
            s,
        )
    }

    fn init_placeholder(bcx: &mut BodyCtxt<'a, 'tcx>, target: Obj<Self>, body: Self::Body) {
        let s = bcx.session();
        LateInit::init(&target.r(s).kind, body);
    }

    fn create_err(bcx: &mut BodyCtxt<'a, 'tcx>, span: Span, err: ErrorGuaranteed) -> Obj<Self> {
        let s = bcx.session();
        let tcx = bcx.tcx();

        Obj::new(
            ThirExpr {
                span,
                ty: bcx.ccx_mut().export(span, tcx.intern(TyKind::Error(err))),
                kind: LateInit::new(ThirExprKind::Error(err)),
            },
            s,
        )
    }
}

impl<'a, 'tcx> Confirmable<'a, 'tcx> for ThirPat {
    type Meta = Ty;
    type Body = ThirPatKind;

    fn create_placeholder(
        bcx: &mut BodyCtxt<'a, 'tcx>,
        span: Span,
        meta: &Self::Meta,
    ) -> Obj<Self> {
        let s = bcx.session();

        Obj::new(
            ThirPat {
                span,
                ty: bcx.ccx_mut().export(span, *meta),
                kind: LateInit::uninit(),
            },
            s,
        )
    }

    fn init_placeholder(bcx: &mut BodyCtxt<'a, 'tcx>, target: Obj<Self>, body: Self::Body) {
        let s = bcx.session();
        LateInit::init(&target.r(s).kind, body);
    }

    fn create_err(bcx: &mut BodyCtxt<'a, 'tcx>, span: Span, err: ErrorGuaranteed) -> Obj<Self> {
        let s = bcx.session();
        let tcx = bcx.tcx();

        Obj::new(
            ThirPat {
                span,
                ty: bcx.ccx_mut().export(span, tcx.intern(TyKind::Error(err))),
                kind: LateInit::new(ThirPatKind::Error(err)),
            },
            s,
        )
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
enum ConfirmOrder {
    BuildingOutwards,
    BuildingInwards,
}

#[derive_where(Default)]
struct ConfirmMap<'a, 'tcx, K, V>
where
    K: 'static,
    V: Confirmable<'a, 'tcx>,
{
    entries: FxHashMap<Obj<K>, ConfirmEntry<'a, 'tcx, V>>,
}

#[derive_where(Default)]
struct ConfirmEntry<'a, 'tcx, V>
where
    V: Confirmable<'a, 'tcx>,
{
    definition: Option<ConfirmDefinition<'a, 'tcx, V>>,
    resolution: Option<ConfirmResolution<V>>,
}

struct ConfirmDefinition<'a, 'tcx, V>
where
    V: Confirmable<'a, 'tcx>,
{
    base_meta: V::Meta,
    base_func: ArenaRc<dyn 'a + Fn(&mut BodyCtxt<'a, 'tcx>) -> V::Body>,
    refinements: Vec<ConfirmRefinement<'a, 'tcx, V>>,
}

struct ConfirmRefinement<'a, 'tcx, V>
where
    V: Confirmable<'a, 'tcx>,
{
    meta: V::Meta,
    func: ArenaRc<dyn 'a + Fn(&mut BodyCtxt<'a, 'tcx>, Obj<V>) -> V::Body>,
}

#[derive_where(Copy, Clone)]
struct ConfirmResolution<V: 'static> {
    start: Obj<V>,
    end: Obj<V>,
}

impl<'a, 'tcx, K, V> ConfirmMap<'a, 'tcx, K, V>
where
    K: 'static,
    V: Confirmable<'a, 'tcx>,
{
    fn resolve<FP>(
        bcx: &mut BodyCtxt<'a, 'tcx>,
        mut project: FP,
        order: ConfirmOrder,
        hir_span: Span,
        hir: Obj<K>,
    ) -> ConfirmResolution<V>
    where
        FP: for<'r> FnMut(&'r mut BodyCtxt<'a, 'tcx>) -> &'r mut Self,
    {
        let state = project(bcx).entries.entry(hir).or_default();

        if let Some(resolution) = state.resolution {
            return resolution;
        }

        match state.definition.take() {
            Some(ConfirmDefinition {
                base_meta,
                base_func,
                mut refinements,
            }) => {
                match order {
                    ConfirmOrder::BuildingOutwards => {
                        // (fallthrough)
                    }
                    ConfirmOrder::BuildingInwards => {
                        refinements.reverse();
                    }
                }

                // Create placeholders for the start and end of the refinement chain to allow for
                // reentrant resolution.
                let start = V::create_placeholder(bcx, hir_span, &base_meta);

                let end = refinements.last().map_or(start, |refinement| {
                    V::create_placeholder(bcx, hir_span, &refinement.meta)
                });

                let resolution = ConfirmResolution { start, end };

                project(bcx).entries.get_mut(&hir).unwrap().resolution = Some(resolution);

                // Initialize expressions.
                let body = base_func(bcx);
                V::init_placeholder(bcx, start, body);

                let mut prev = start;

                for (idx, refinement) in refinements.iter().enumerate() {
                    let body = (refinement.func)(bcx, prev);

                    if idx == refinements.len() - 1 {
                        V::init_placeholder(bcx, start, body);
                    } else {
                        prev = V::create_placeholder(bcx, hir_span, &refinement.meta);
                        V::init_placeholder(bcx, prev, body);
                    }
                }

                resolution
            }
            None => {
                let thir = V::create_err(
                    bcx,
                    hir_span,
                    Diag::span_err(hir_span, "never type-checked")
                        .to_delay_bug()
                        .emit(),
                );

                let resolved = ConfirmResolution {
                    start: thir,
                    end: thir,
                };

                project(bcx).entries.get_mut(&hir).unwrap().resolution = Some(resolved);

                resolved
            }
        }
    }

    fn put(
        &mut self,
        arena: Rc<Bump>,
        hir: Obj<K>,
        meta: V::Meta,
        f: impl 'a + FnOnce(&mut BodyCtxt<'a, 'tcx>) -> V::Body,
    ) {
        let state = self.entries.entry(hir).or_default();

        assert!(state.definition.is_none());

        state.definition = Some(ConfirmDefinition {
            base_meta: meta,
            base_func: {
                let f = Cell::new(Some(f));

                ArenaRc::map::<dyn 'a + Fn(&mut BodyCtxt<'a, 'tcx>) -> V::Body>(
                    ArenaRc::new(arena, move |bcx: &mut BodyCtxt<'a, 'tcx>| -> V::Body {
                        f.take().unwrap()(bcx)
                    }),
                    |v| v,
                )
            },
            refinements: Vec::new(),
        });
    }

    fn refine(
        &mut self,
        arena: Rc<Bump>,
        hir: Obj<K>,
        meta: V::Meta,
        f: impl 'a + FnOnce(&mut BodyCtxt<'a, 'tcx>, Obj<V>) -> V::Body,
    ) {
        self.entries
            .get_mut(&hir)
            .and_then(|v| v.definition.as_mut())
            .expect("no base set up")
            .refinements
            .push(ConfirmRefinement {
                meta,
                func: {
                    let f = Cell::new(Some(f));

                    ArenaRc::map::<dyn 'a + Fn(&mut BodyCtxt<'a, 'tcx>, Obj<V>) -> V::Body>(
                        ArenaRc::new(
                            arena,
                            move |bcx: &mut BodyCtxt<'a, 'tcx>, base: Obj<V>| -> V::Body {
                                f.take().unwrap()(bcx, base)
                            },
                        ),
                        |v| v,
                    )
                },
            });
    }

    fn is_defined(&self, hir: Obj<K>) -> bool {
        self.entries
            .get(&hir)
            .is_some_and(|v| v.definition.is_some())
    }
}
