use crate::{
    base::arena::{HasInterner, Obj},
    semantic::{
        analysis::CrateTypeckVisitor,
        syntax::{FnDef, FuncDefOwner, TyKind},
    },
};
use std::{convert::Infallible, ops::ControlFlow};

impl CrateTypeckVisitor<'_> {
    pub fn visit_fn_def(&mut self, def: Obj<FnDef>) -> ControlFlow<Infallible> {
        let s = self.session();
        let tcx = self.tcx();

        // Obtain the self type.
        let self_ty = match def.r(s).owner {
            FuncDefOwner::Func(_) => tcx.intern(TyKind::SigThis),
            FuncDefOwner::Method(_, _) => todo!(),
        };

        // WF-check the signature.
        self.visit_simple_generic_binder(self_ty, def.r(s).generics);

        // TODO
        // if let Some(self_param) = *def.r(s).self_param {
        //     self.visit_spanned_ty(self_param)?;
        // }

        // TODO
        // for arg in def.r(s).args.r(s) {
        //     self.visit_spanned_ty(arg.ty)?;
        // }
        //
        // self.visit_spanned_ty(*def.r(s).ret_ty)?;

        // Check the body
        // TODO

        ControlFlow::Continue(())
    }
}
