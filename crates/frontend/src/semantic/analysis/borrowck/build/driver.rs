use crate::{
    base::{Session, arena::Obj},
    semantic::{
        analysis::{
            borrowck::build::scope::{MirBuilderScopeIdx, MirScopedBuilder},
            sigck::CrateSigckVisitor,
        },
        syntax::{FnDef, MirAssignRvalue, MirLocalIdx, MirPlace, ThirExpr, ThirLocal, TyCtxt},
    },
    utils::hash::FxHashMap,
};

pub fn build_function_mir(cx: &mut CrateSigckVisitor, def: Obj<FnDef>) {
    let s = cx.session();
    let tcx = cx.tcx();

    let Some(thir) = *def.r(s).thir_body else {
        return;
    };

    // let mut builder = MirFromThirCtx::new(tcx, def);
    // let rv = builder.lower_expr_rvalue(MirBuilderScopeIdx::ENTRY, thir);
    // TODO
}

pub struct MirFromThirCtx<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub def: Obj<FnDef>,
    pub builder: MirScopedBuilder<'tcx>,
    pub labelled_scopes: FxHashMap<Obj<ThirExpr>, LabelledScope>,
    pub thir_locals: FxHashMap<Obj<ThirLocal>, MirLocalIdx>,
}

#[derive(Debug, Clone)]
pub enum MirRvalueOrPlace {
    Rvalue(MirAssignRvalue),
    Place(MirPlace),
}

#[derive(Copy, Clone)]
pub struct LabelledScope {
    pub scope: MirBuilderScopeIdx,
    pub out_place: Option<MirPlace>,
}

impl<'tcx> MirFromThirCtx<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, def: Obj<FnDef>) -> Self {
        Self {
            tcx,
            def,
            builder: MirScopedBuilder::new(tcx),
            labelled_scopes: FxHashMap::default(),
            thir_locals: FxHashMap::default(),
        }
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    pub fn session(&self) -> &'tcx Session {
        &self.tcx.session
    }
}
