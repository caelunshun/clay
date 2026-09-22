use crate::{
    base::{
        Diag, ErrorGuaranteed,
        arena::{HasInterner, LateInit, Obj},
        syntax::{HasSpan, Span},
    },
    semantic::{
        analysis::typeck::BodyCtxt,
        infer::FloatingInferVar,
        syntax::{
            HirBlock, HirExpr, HirLabelledBlock, HirLocal, HirPat, HirPatListFrontAndTail, HirStmt,
            InferTyVar, RelationMode, SimpleTyKind, ThirBlock, ThirExpr, ThirExprKind,
            ThirLabelledBlock, ThirLetStmt, ThirLocal, ThirPat, ThirPatKind,
            ThirPatListFrontAndTail, ThirStmt, Ty, TyKind,
        },
    },
    utils::{hash::FxHashMap, mem::ArenaRc},
};
use bumpalo::Bump;
use derive_where::derive_where;
use std::{cell::Cell, rc::Rc};

// === Infrastructure === //

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
    #[expect(unused)]
    pub inner: Obj<ThirPat>,
    pub outer: Obj<ThirPat>,
}

#[derive(Debug, Copy, Clone)]
pub struct ThirExprConfirmedWithTy {
    pub expr: Obj<HirExpr>,
    pub ty: Ty,
}

#[derive(Debug, Copy, Clone)]
pub struct ThirPatConfirmed {
    pub pat: Obj<HirPat>,
}

/// Checking
impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
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

        ThirExprConfirmedWithTy { expr: hir, ty }
    }

    pub fn put_thir_expr_err(
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

    pub fn put_thir_pat(
        &mut self,
        hir: Obj<HirPat>,
        ty: Ty,
        f: impl 'a + FnOnce(&mut Self) -> ThirPatKind,
    ) -> ThirPatConfirmed {
        assert!(!self.confirm_state.started_confirmation);

        self.confirm_state
            .patterns
            .put(self.confirm_state.arena.clone(), hir, ty, f);

        ThirPatConfirmed { pat: hir }
    }

    pub fn put_thir_pat_err(&mut self, hir: Obj<HirPat>, err: ErrorGuaranteed) -> ThirPatConfirmed {
        let tcx = self.tcx();

        self.put_thir_pat(hir, tcx.intern(TyKind::Error(err)), move |_bcx| {
            ThirPatKind::Error(err)
        })
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

    pub fn register_infer_with_fallback(&mut self, var: InferTyVar) {
        self.confirm_state.fallback_infers.push(var);
    }
}

/// Confirmation
impl BodyCtxt<'_, '_> {
    pub fn begin_confirmation(&mut self) {
        let tcx = self.tcx();

        assert!(!self.confirm_state.started_confirmation);
        self.confirm_state.started_confirmation = true;

        // Assign fallbacks to integer literal inference holes.
        self.ccx_mut().poll_obligations();

        for idx in 0..self.confirm_state.fallback_infers.len() {
            let var = self.confirm_state.fallback_infers[idx];

            let Err(FloatingInferVar { perm_set, .. }) =
                self.ccx().lookup_ty_infer_var_without_poll(var)
            else {
                continue;
            };

            let var_ty = tcx.intern(TyKind::InferVar(var));

            let Some(fallback) = perm_set.to_infer_fallback(tcx) else {
                continue;
            };

            self.ucx_mut()
                .unify_ty_and_ty(var_ty, fallback, RelationMode::Equate)
                .unwrap()
                .report_never();

            self.ccx_mut().poll_obligations();
        }
    }

    pub fn confirm_thir_expr(&mut self, hir: Obj<HirExpr>) -> ThirExprResolution {
        let s = self.session();

        assert!(self.confirm_state.started_confirmation);

        let ConfirmResolution { start, end } = ConfirmMap::confirm(
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

    pub fn confirm_thir_expr_post(&mut self, hir: Obj<HirExpr>) -> Obj<ThirExpr> {
        self.confirm_thir_expr(hir).post_coerce
    }

    pub fn confirm_thir_expr_list_post(
        &mut self,
        hir: Obj<[Obj<HirExpr>]>,
    ) -> Obj<[Obj<ThirExpr>]> {
        let s = self.session();

        self.confirm_thir_expr_iter_post(hir.r(s).iter().copied())
    }

    pub fn confirm_thir_expr_iter_post(
        &mut self,
        hir: impl IntoIterator<Item = Obj<HirExpr>, IntoIter: ExactSizeIterator>,
    ) -> Obj<[Obj<ThirExpr>]> {
        let s = self.session();

        Obj::new_iter(
            hir.into_iter().map(|hir| self.confirm_thir_expr_post(hir)),
            s,
        )
    }

    pub fn confirm_thir_pat(&mut self, hir: Obj<HirPat>) -> ThirPatResolution {
        let s = self.session();

        assert!(self.confirm_state.started_confirmation);

        let ConfirmResolution { start, end } = ConfirmMap::confirm(
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

    pub fn confirm_opt_thir_expr_post(
        &mut self,
        hir: Option<Obj<HirExpr>>,
    ) -> Option<Obj<ThirExpr>> {
        hir.map(|expr| self.confirm_thir_expr_post(expr))
    }

    pub fn confirm_thir_pat_outer(&mut self, hir: Obj<HirPat>) -> Obj<ThirPat> {
        self.confirm_thir_pat(hir).outer
    }

    pub fn confirm_opt_thir_pat_outer(&mut self, hir: Option<Obj<HirPat>>) -> Option<Obj<ThirPat>> {
        hir.map(|pat| self.confirm_thir_pat_outer(pat))
    }

    pub fn confirm_thir_pat_list_outer(&mut self, hir: Obj<[Obj<HirPat>]>) -> Obj<[Obj<ThirPat>]> {
        let s = self.session();

        Obj::new_iter(
            hir.r(s).iter().map(|&hir| self.confirm_thir_pat_outer(hir)),
            s,
        )
    }

    pub fn confirm_thir_opt_pat_list_outer(
        &mut self,
        hir: Option<Obj<[Obj<HirPat>]>>,
    ) -> Option<Obj<[Obj<ThirPat>]>> {
        hir.map(|v| self.confirm_thir_pat_list_outer(v))
    }

    pub fn confirm_thir_pat_list_front_and_tail_outer(
        &mut self,
        hir: HirPatListFrontAndTail,
    ) -> ThirPatListFrontAndTail {
        ThirPatListFrontAndTail {
            front: self.confirm_thir_pat_list_outer(hir.front),
            tail: self.confirm_thir_opt_pat_list_outer(hir.tail),
        }
    }

    pub fn confirm_thir_local(&mut self, hir: Obj<HirLocal>) -> Obj<ThirLocal> {
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
}

// === Synthesis === //

impl BodyCtxt<'_, '_> {
    pub fn confirm_thir_label(&mut self, hir: HirLabelledBlock) -> ThirLabelledBlock {
        let HirLabelledBlock { target, kind } = hir;

        ThirLabelledBlock {
            target: self.confirm_thir_expr(target).pre_coerce,
            kind,
        }
    }

    pub fn confirm_thir_block_uncached(
        &mut self,
        hir: Obj<HirBlock>,
        ret_ty: Ty,
    ) -> Obj<ThirBlock> {
        let s = self.session();
        let tcx = self.tcx();

        Obj::new(
            ThirBlock {
                span: hir.r(s).span,
                ty: self.ccx_mut().export(hir.r(s).span, ret_ty),
                stmts: hir
                    .r(s)
                    .stmts
                    .iter()
                    .map(|&stmt| match stmt {
                        HirStmt::Expr(expr) => ThirStmt::Expr(self.confirm_thir_expr_post(expr)),
                        HirStmt::Let(stmt) => ThirStmt::Let(Obj::new(
                            ThirLetStmt {
                                span: stmt.r(s).span,
                                pat: self.confirm_thir_pat(stmt.r(s).pat).outer,
                                init: self.confirm_opt_thir_expr_post(stmt.r(s).init),
                                else_clause: stmt.r(s).else_clause.map(|block| {
                                    self.confirm_thir_block_uncached(
                                        block,
                                        tcx.intern(TyKind::Simple(SimpleTyKind::Never)),
                                    )
                                }),
                            },
                            s,
                        )),
                    })
                    .collect::<Vec<_>>(),
                last_expr: self.confirm_opt_thir_expr_post(hir.r(s).last_expr),
            },
            s,
        )
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
    fn confirm<FP>(
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
}
