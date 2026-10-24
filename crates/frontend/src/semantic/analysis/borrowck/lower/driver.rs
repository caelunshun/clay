use crate::{
    base::{
        Session,
        arena::{LateInit, Obj},
    },
    flags,
    semantic::{
        analysis::{
            borrowck::scopes::{MirScopedBuilder, RawMirScopedBuilder, TraitCache},
            sigck::CrateSigckVisitor,
        },
        infer::ImplCache,
        syntax::{
            FnDef, MirBody, MirLocal, MirLocalIdx, MirPlace, MirPrettyFmtCx, MirRvalue,
            MirScopeIdx, MirSourceInfo, ThirBody, ThirExpr, ThirLocal, TyCtxt,
        },
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

    let mut build_cx = MirFromThirCtx::new(tcx, check_cx.impl_cache, def);
    build_cx.lower_fn(body);
    let body = build_cx.finish();

    if flags::should_print_mir_scopes() {
        println!("{}", MirPrettyFmtCx::new(tcx, &body).flat_body());
    }

    LateInit::init(&def.r(s).mir_body, Some(body));
}

pub struct MirFromThirCtx<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub def: Obj<FnDef>,
    pub raw_builder: RawMirScopedBuilder<'tcx>,
    pub trait_cache: TraitCache<'tcx>,
    pub labelled_scopes: FastHashMap<Obj<ThirExpr>, LabelledScope>,
    pub thir_locals: FastHashMap<Obj<ThirLocal>, MirLocalIdx>,
}

impl<'tcx> MirScopedBuilder<'tcx> for MirFromThirCtx<'tcx> {
    fn raw_builder(&mut self) -> &mut RawMirScopedBuilder<'tcx> {
        &mut self.raw_builder
    }

    fn trait_cache(&mut self) -> &mut TraitCache<'tcx> {
        &mut self.trait_cache
    }
}

#[derive(Debug, Clone)]
pub enum MirRvalueOrPlace {
    Rvalue(MirRvalue),
    Place(MirPlace),
}

#[derive(Copy, Clone)]
pub struct LabelledScope {
    pub scope: MirScopeIdx,
    pub out_place: MirPlace,
}

impl<'tcx> MirFromThirCtx<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, impl_cache: &'tcx ImplCache, def: Obj<FnDef>) -> Self {
        let s = &tcx.session;

        let mut this = Self {
            tcx,
            def,
            raw_builder: RawMirScopedBuilder::new(tcx),
            trait_cache: TraitCache::new(tcx, impl_cache, def),
            labelled_scopes: FastHashMap::default(),
            thir_locals: FastHashMap::default(),
        };

        let body = this.raw_builder.body_mut();

        body.arg_count = def.r(s).args.r(s).len() as u32;
        body.locals.push(MirLocal {
            ty: *def.r(s).ret_ty,
        });

        for arg in def.r(s).args.r(s) {
            this.push_local(MirScopeIdx::ENTRY, MirLocal { ty: arg.ty });
        }

        this
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    pub fn session(&self) -> &'tcx Session {
        &self.tcx.session
    }

    pub fn lower_fn(&mut self, body: &ThirBody) {
        let s = self.session();
        let tcx = self.tcx();

        let scope = MirScopeIdx::ENTRY;

        for (idx, (hir_arg, thir_pat)) in self
            .def
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

        self.push_return(scope, MirSourceInfo::BlockFallthrough);
    }

    pub fn finish(mut self) -> MirBody {
        let s = self.session();

        self.raw_builder
            .finish(self.trait_cache.can_omit_drop(*self.def.r(s).ret_ty))
    }
}
