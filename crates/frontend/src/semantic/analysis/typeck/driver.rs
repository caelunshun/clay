use crate::{
    base::{ErrorGuaranteed, Session, arena::Obj},
    semantic::{
        analysis::{sigck::CrateSigckVisitor, typeck::infra::confirm::BodyCtxtConfirmState},
        infer::{ClauseCx, ClauseImportEnv, HrtbUniverse, UnifyCx, UnifyCxMode},
        syntax::{
            Crate, FnDef, HirLabelledBlock, HirLocal, InferTyVarSourceInfo, Item, Ty, TyCtxt,
        },
    },
    utils::hash::FxHashMap,
};

// === Driver === //

pub fn type_check_function(cx: &mut CrateSigckVisitor, def: Obj<FnDef>) {
    let s = cx.session();
    let tcx = cx.tcx();

    // Setup a `ClauseCx` for signature validation.
    let mut ccx = ClauseCx::new(tcx, cx.coherence, cx.krate, UnifyCxMode::RegionBlind);
    let env_sig = ccx.universal_env_for_fn_def(def);

    // WF-check the signature.
    cx.visit_generic_binder(&mut ccx, &env_sig, def.r(s).generics);

    // Check the body
    if let Some(body) = *def.r(s).hir_body {
        let mut bcx = BodyCtxt::new(&mut ccx, def, &env_sig);

        for arg in def.r(s).args.r(s) {
            let env = bcx.import_env;
            let ascription = bcx.ccx_mut().import_here(env, arg.ty);

            bcx.check_pat_demand(arg.pat, ascription, None);
        }

        bcx.check_expr_demand(body, bcx.return_ty)
            .ignore_divergence();

        bcx.begin_confirmation();
    } else {
        for arg in def.r(s).args.r(s) {
            ccx.import_here(&env_sig, arg.ty);
        }

        ccx.import_here(&env_sig, *def.r(s).ret_ty);
    }

    ccx.verify();
}

// === BodyCtxt === //

pub(super) struct BodyCtxt<'a, 'tcx> {
    pub ccx: &'a mut ClauseCx<'tcx>,
    pub def: Obj<FnDef>,
    pub import_env: &'a ClauseImportEnv,
    pub local_types: FxHashMap<Obj<HirLocal>, Ty>,
    pub block_break_demands: FxHashMap<HirLabelledBlock, Option<Ty>>,
    pub confirm_state: BodyCtxtConfirmState<'a, 'tcx>,
    pub return_ty: Ty,
}

impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
    pub fn new(
        ccx: &'a mut ClauseCx<'tcx>,
        def: Obj<FnDef>,
        import_env: &'a ClauseImportEnv,
    ) -> Self {
        let s = ccx.session();

        let return_ty = ccx.import_here(import_env, *def.r(s).ret_ty);

        Self {
            ccx,
            def,
            import_env,
            local_types: FxHashMap::default(),
            block_break_demands: FxHashMap::default(),
            confirm_state: BodyCtxtConfirmState::default(),
            return_ty,
        }
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    pub fn session(&self) -> &'tcx Session {
        self.ccx.session()
    }

    pub fn krate(&self) -> Obj<Crate> {
        self.ccx().krate()
    }

    pub fn item(&self) -> Obj<Item> {
        let s = self.session();
        self.def.r(s).owner.as_item(s)
    }

    pub fn ccx(&self) -> &ClauseCx<'tcx> {
        self.ccx
    }

    pub fn ccx_mut(&mut self) -> &mut ClauseCx<'tcx> {
        self.ccx
    }

    #[expect(unused)]
    pub fn ucx(&self) -> &UnifyCx<'tcx> {
        self.ccx.ucx()
    }

    #[expect(unused)]
    pub fn ucx_mut(&mut self) -> &mut UnifyCx<'tcx> {
        self.ccx.ucx_mut()
    }

    pub fn type_of_local(&mut self, local: Obj<HirLocal>) -> Ty {
        let s = self.session();

        *self.local_types.entry(local).or_insert_with(|| {
            self.ccx.fresh_ty_infer(
                HrtbUniverse::ROOT,
                InferTyVarSourceInfo::Local {
                    name: local.r(s).name,
                },
            )
        })
    }
}
