use crate::{
    base::{Session, arena::Obj},
    semantic::{
        analysis::TyCtxt,
        syntax::{FnDef, MirBody, ThirExpr},
    },
};
use index_vec::IndexVec;

pub struct MirLowerCtxt<'tcx> {
    tcx: &'tcx TyCtxt,
    def: Obj<FnDef>,
    body: MirBody,
}

impl<'tcx> MirLowerCtxt<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, def: Obj<FnDef>) -> Self {
        Self {
            tcx,
            def,
            body: MirBody {
                locals: IndexVec::new(),
                blocks: IndexVec::new(),
            },
        }
    }

    pub fn session(&self) -> &'tcx Session {
        &self.tcx.session
    }

    pub fn lower_entry(&mut self) {
        let s = self.session();

        dbg!(*self.def.r(s).thir_body);
    }

    pub fn lower_place(&mut self, expr: Obj<ThirExpr>) {}
}
