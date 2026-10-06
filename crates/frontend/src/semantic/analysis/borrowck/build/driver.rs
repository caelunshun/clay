use crate::{
    base::{Session, arena::Obj},
    semantic::{
        analysis::{
            borrowck::build::scope::{MirBuilderScopeIdx, MirScopedBuilder},
            sigck::CrateSigckVisitor,
        },
        syntax::{
            FnDef, MirAssignRvalue, MirLocalIdx, MirPlace, ThirBody, ThirExpr, ThirLocal, TyCtxt,
        },
    },
    utils::hash::FxHashMap,
};

pub fn build_function_mir(cx: &mut CrateSigckVisitor, def: Obj<FnDef>) {
    let s = cx.session();
    let tcx = cx.tcx();

    let Some(body) = &*def.r(s).thir_body else {
        return;
    };

    let mut builder = MirFromThirCtx::new(tcx, def);
    builder.lower_fn(body);
}

pub struct MirFromThirCtx<'tcx> {
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
    pub out_place: MirPlace,
}

impl<'tcx> MirFromThirCtx<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, def: Obj<FnDef>) -> Self {
        Self {
            builder: MirScopedBuilder::new(tcx, def),
            labelled_scopes: FxHashMap::default(),
            thir_locals: FxHashMap::default(),
        }
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.builder.tcx()
    }

    pub fn session(&self) -> &'tcx Session {
        self.builder.session()
    }

    pub fn def(&self) -> Obj<FnDef> {
        self.builder.def()
    }

    pub fn lower_fn(&mut self, body: &ThirBody) {
        let s = self.session();
        let tcx = self.tcx();

        let def = self.def();

        let scope = MirBuilderScopeIdx::ENTRY;

        for (idx, (hir_arg, thir_pat)) in def
            .r(s)
            .args
            .r(s)
            .iter()
            .zip(body.arg_pats.iter())
            .enumerate()
        {
            self.lower_fn_arg(
                hir_arg.span,
                scope,
                *thir_pat,
                MirPlace::new(tcx, MirLocalIdx::from_usize(1 + idx), []),
            );
        }

        self.lower_expr_place(
            scope,
            body.expr,
            Some(MirPlace::new(tcx, MirLocalIdx::RETURN, [])),
        );
    }
}
