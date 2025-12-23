use crate::{
    base::{Session, arena::Obj},
    semantic::{
        analysis::{ClauseCx, CrateTypeckVisitor, TyCtxt, TyVisitor},
        syntax::{Block, Expr, FnDef, Ty, TyAndDivergence},
    },
};
use std::{convert::Infallible, ops::ControlFlow};

impl CrateTypeckVisitor<'_> {
    pub fn visit_fn_def(&mut self, def: Obj<FnDef>) -> ControlFlow<Infallible> {
        let s = self.session();

        // WF-check the signature.
        self.visit_generic_binder(def.r(s).generics)?;

        // TODO
        // if let Some(self_param) = *def.r(s).self_param {
        //     self.visit_spanned_ty(self_param)?;
        // }

        for arg in def.r(s).args.r(s) {
            self.visit_spanned_ty(arg.ty)?;
        }

        self.visit_spanned_ty(*def.r(s).ret_ty)?;

        // Check the body
        // TODO

        ControlFlow::Continue(())
    }
}

// === FuncCx === //

pub struct FuncCx<'tcx> {
    ccx: ClauseCx<'tcx>,
}

impl<'tcx> FuncCx<'tcx> {
    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    pub fn session(&self) -> &'tcx Session {
        self.ccx.session()
    }

    pub fn check_expr(
        &mut self,
        exprs: impl IntoIterator<Item = Obj<Expr>>,
        demand: Option<Ty>,
    ) -> TyAndDivergence {
        todo!()
    }

    pub fn check_block(&mut self, block: Obj<Block>, demand: Option<Ty>) -> TyAndDivergence {
        todo!()
    }
}
