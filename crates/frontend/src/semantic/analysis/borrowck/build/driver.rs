use crate::{
    base::{
        Session,
        arena::{LateInit, Obj},
    },
    semantic::{
        analysis::{
            borrowck::build::scope::{MirBuilderScopeIdx, MirScopedBuilder},
            sigck::CrateSigckVisitor,
        },
        syntax::{FnDef, MirLocalIdx, MirPlace, MirRvalue, ThirBody, ThirExpr, ThirLocal, TyCtxt},
    },
};
use clay_core::FastHashMap;

pub fn build_function_mir(check_cx: &mut CrateSigckVisitor, def: Obj<FnDef>) {
    let s = check_cx.session();
    let tcx = check_cx.tcx();

    let Some(body) = &*def.r(s).thir_body else {
        LateInit::init(&def.r(s).mir_body, None);
        return;
    };

    let mut build_cx = MirFromThirCtx::new(tcx, def);
    build_cx.lower_fn(body);

    LateInit::init(&def.r(s).mir_body, Some(build_cx.builder.finish()));
}

pub struct MirFromThirCtx<'tcx> {
    pub builder: MirScopedBuilder<'tcx>,
    pub labelled_scopes: FastHashMap<Obj<ThirExpr>, LabelledScope>,
    pub thir_locals: FastHashMap<Obj<ThirLocal>, MirLocalIdx>,
}

#[derive(Debug, Clone)]
pub enum MirRvalueOrPlace {
    Rvalue(MirRvalue),
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
            labelled_scopes: FastHashMap::default(),
            thir_locals: FastHashMap::default(),
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

        self.builder.push_return(scope);
    }
}
