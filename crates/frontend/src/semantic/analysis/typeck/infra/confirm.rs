use crate::{
    base::arena::Obj,
    semantic::{
        analysis::typeck::BodyCtxt,
        syntax::{HirBlock, HirExpr, HirLocal, HirPat, ThirBlock, ThirExpr, ThirLocal, ThirPat},
    },
    utils::{hash::FxHashMap, mem::ArenaRc},
};
use bumpalo::Bump;
use std::rc::Rc;

#[derive(Default)]
pub struct BodyCtxtConfirmState<'a, 'tcx> {
    arena: Rc<Bump>,
    is_confirming: bool,
    expressions: FxHashMap<Obj<HirExpr>, ExprState<'a, 'tcx>>,
    patterns: FxHashMap<Obj<HirExpr>, PatState<'a, 'tcx>>,
}

type BaseFn<'a, 'tcx, T> = ArenaRc<dyn 'a + FnMut(&mut BodyCtxt<'a, 'tcx>) -> T>;
type RefinementFn<'a, 'tcx, T> = ArenaRc<dyn 'a + FnMut(&mut BodyCtxt<'a, 'tcx>, T) -> T>;

struct ExprState<'a, 'tcx> {
    base: Option<BaseFn<'a, 'tcx, Obj<ThirExpr>>>,
    refinements: Vec<RefinementFn<'a, 'tcx, Obj<ThirExpr>>>,
}

struct PatState<'a, 'tcx> {
    base: Option<BaseFn<'a, 'tcx, Obj<ThirPat>>>,
    refinements: Vec<RefinementFn<'a, 'tcx, Obj<ThirPat>>>,
}

impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
    pub fn resolve_thir_expr(&mut self, hir: Obj<HirExpr>) -> Obj<ThirExpr> {
        assert!(self.confirm_state.is_confirming);

        todo!()
    }

    pub fn resolve_thir_block(&mut self, hir: Obj<HirBlock>) -> Obj<ThirBlock> {
        todo!()
    }

    pub fn put_thir_expr(
        &mut self,
        hir: Obj<HirExpr>,
        f: impl 'a + FnOnce(&mut Self) -> Obj<ThirExpr>,
    ) {
    }

    pub fn refine_thir_expr(
        &mut self,
        hir: Obj<HirExpr>,
        f: impl 'a + FnOnce(&mut Self, Obj<ThirExpr>) -> Obj<ThirExpr>,
    ) {
        todo!()
    }

    pub fn resolve_thir_pat(&mut self, hir: Obj<HirPat>) -> Obj<ThirPat> {
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

    pub fn confirm(&mut self) {
        todo!()
    }
}
