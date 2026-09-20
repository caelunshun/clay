use crate::{
    base::{
        Diag,
        arena::{HasInterner, LateInit, Obj},
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
use std::{cell::Cell, rc::Rc};

#[derive(Default)]
pub struct BodyCtxtConfirmState<'a, 'tcx> {
    arena: Rc<Bump>,
    started_confirmation: bool,
    expressions: FxHashMap<Obj<HirExpr>, ExprState<'a, 'tcx>>,
    patterns: FxHashMap<Obj<HirExpr>, PatState<'a, 'tcx>>,
    int_infers: Vec<InferTyVar>,
}

#[derive(Default)]
struct ExprState<'a, 'tcx> {
    definition: Option<ExprStateDefined<'a, 'tcx>>,
    resolved: Option<ThirExprResolved>,
}

struct ExprStateDefined<'a, 'tcx> {
    base: ExprStateBase<'a, 'tcx>,
    refinements: Vec<ExprStateRefinement<'a, 'tcx>>,
}

struct ExprStateBase<'a, 'tcx> {
    ty: Ty,
    func: ArenaRc<dyn 'a + Fn(&mut BodyCtxt<'a, 'tcx>) -> ThirExprKind>,
}

struct ExprStateRefinement<'a, 'tcx> {
    ty: Ty,
    func: ArenaRc<dyn 'a + Fn(&mut BodyCtxt<'a, 'tcx>, Obj<ThirExpr>) -> ThirExprKind>,
}

#[derive(Debug, Copy, Clone)]
pub struct ThirExprResolved {
    pub pre_coerce: Obj<ThirExpr>,
    pub post_coerce: Obj<ThirExpr>,
}

#[derive(Default)]
struct PatState<'a, 'tcx> {
    definition: Option<PatStateDefined<'a, 'tcx>>,
    resolved: Option<ThirPatResolved>,
}

struct PatStateDefined<'a, 'tcx> {
    base: PatStateBase<'a, 'tcx>,
    refinements: Vec<PatStateRefinement<'a, 'tcx>>,
}

struct PatStateBase<'a, 'tcx> {
    ty: Ty,
    func: ArenaRc<dyn 'a + Fn(&mut BodyCtxt<'a, 'tcx>) -> ThirPatKind>,
}

struct PatStateRefinement<'a, 'tcx> {
    ty: Ty,
    func: ArenaRc<dyn 'a + Fn(&mut BodyCtxt<'a, 'tcx>, Obj<ThirPat>) -> ThirPatKind>,
}

#[derive(Debug, Copy, Clone)]
pub struct ThirPatResolved {
    pub inner: Obj<ThirPat>,
    pub outer: Obj<ThirPat>,
}

impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
    pub fn resolve_thir_expr(&mut self, hir: Obj<HirExpr>) -> ThirExprResolved {
        let s = self.session();
        let tcx = self.tcx();

        let expr_span = hir.r(s).span;

        assert!(self.confirm_state.started_confirmation);

        let state = self.confirm_state.expressions.entry(hir).or_default();

        if let Some(resolution) = state.resolved {
            return resolution;
        }

        match state.definition.take() {
            Some(ExprStateDefined { base, refinements }) => {
                // Create placeholders for the start and end of the refinement chain to allow for
                // reentrant resolution.
                let pre_coerce = Obj::new(
                    ThirExpr {
                        span: expr_span,
                        ty: self.ccx.export(expr_span, base.ty),
                        kind: LateInit::uninit(),
                    },
                    s,
                );

                let post_coerce = refinements.last().map_or(pre_coerce, |refinement| {
                    Obj::new(
                        ThirExpr {
                            span: expr_span,
                            ty: self.ccx.export(expr_span, refinement.ty),
                            kind: LateInit::uninit(),
                        },
                        s,
                    )
                });

                let resolved = ThirExprResolved {
                    pre_coerce,
                    post_coerce,
                };
                state.resolved = Some(resolved);

                // Initialize expressions.
                LateInit::init(&pre_coerce.r(s).kind, (base.func)(self));

                let mut prev = pre_coerce;

                for (idx, refinement) in refinements.iter().enumerate() {
                    let kind = (refinement.func)(self, prev);

                    if idx == refinements.len() - 1 {
                        LateInit::init(&post_coerce.r(s).kind, kind);
                    } else {
                        prev = Obj::new(
                            ThirExpr {
                                span: expr_span,
                                ty: self.ccx.export(expr_span, refinement.ty),
                                kind: LateInit::new(kind),
                            },
                            s,
                        );
                    }
                }

                resolved
            }
            None => {
                let err = Diag::span_err(expr_span, "expression never type-checked")
                    .to_delay_bug()
                    .emit();

                let thir = Obj::new(
                    ThirExpr {
                        span: expr_span,
                        ty: self.ccx.export(expr_span, tcx.intern(TyKind::Error(err))),
                        kind: LateInit::new(ThirExprKind::Error(err)),
                    },
                    s,
                );

                let resolved = ThirExprResolved {
                    pre_coerce: thir,
                    post_coerce: thir,
                };
                state.resolved = Some(resolved);

                resolved
            }
        }
    }

    pub fn put_thir_expr(
        &mut self,
        hir: Obj<HirExpr>,
        ty: Ty,
        f: impl 'a + FnOnce(&mut Self) -> ThirExprKind,
    ) {
        assert!(!self.confirm_state.started_confirmation);

        let state = self.confirm_state.expressions.entry(hir).or_default();

        assert!(state.definition.is_none());

        state.definition = Some(ExprStateDefined {
            base: ExprStateBase {
                ty,
                func: {
                    let f = Cell::new(Some(f));

                    ArenaRc::map::<dyn 'a + Fn(&mut Self) -> ThirExprKind>(
                        ArenaRc::new(self.confirm_state.arena.clone(), move |bcx: &mut Self| {
                            f.take().unwrap()(bcx)
                        }),
                        |v| v,
                    )
                },
            },
            refinements: Vec::new(),
        });
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
            .get_mut(&hir)
            .and_then(|v| v.definition.as_mut())
            .expect("no base expression set up")
            .refinements
            .push(ExprStateRefinement {
                ty,
                func: {
                    let f = Cell::new(Some(f));

                    ArenaRc::map::<dyn 'a + Fn(&mut Self, Obj<ThirExpr>) -> ThirExprKind>(
                        ArenaRc::new(
                            self.confirm_state.arena.clone(),
                            move |bcx: &mut Self, base: Obj<ThirExpr>| f.take().unwrap()(bcx, base),
                        ),
                        |v| v,
                    )
                },
            });
    }

    pub fn resolve_thir_pat(&mut self, hir: Obj<HirPat>) -> ThirPatResolved {
        todo!()
    }

    pub fn put_thir_pat(
        &mut self,
        hir: Obj<HirPat>,
        f: impl 'a + FnOnce(&mut Self) -> Obj<ThirPat>,
    ) {
        todo!()
    }

    pub fn refine_thir_pat(
        &mut self,
        hir: Obj<HirPat>,
        f: impl 'a + FnOnce(&mut Self, Obj<HirPat>) -> Obj<ThirPat>,
    ) {
        todo!()
    }

    pub fn resolve_local(&mut self, hir: Obj<HirLocal>) -> Obj<ThirLocal> {
        todo!()
    }

    pub fn resolve_thir_block(&mut self, hir: Obj<HirBlock>) -> Obj<ThirBlock> {
        todo!()
    }

    pub fn confirm(&mut self) {
        todo!()
    }
}
