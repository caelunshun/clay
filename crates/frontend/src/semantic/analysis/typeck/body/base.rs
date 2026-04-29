use crate::{
    base::{ErrorGuaranteed, Session, arena::Obj},
    semantic::{
        analysis::{
            ClauseCx, ClauseImportEnvRef, CrateTypeckVisitor, HrtbUniverse, UnifyCx, UnifyCxMode,
        },
        syntax::{
            Crate, FnDef, HirExpr, HirLabelledBlock, HirLocal, HirPat, InferTyVar,
            InferTyVarSourceInfo, Item, ThirLocal, Ty, TyCtxt,
        },
    },
    utils::hash::FxHashMap,
};

// === Driver === //

impl<'tcx> CrateTypeckVisitor<'tcx> {
    pub fn visit_fn_def(&mut self, def: Obj<FnDef>) {
        let s = self.session();
        let tcx = self.tcx();

        // Setup a `ClauseCx` for signature validation.
        let mut ccx = ClauseCx::new(tcx, self.coherence, self.krate, UnifyCxMode::RegionBlind);
        let env_sig = ccx.create_universal_env_for_fn_def(HrtbUniverse::ROOT_REF, def);

        // WF-check the signature.
        self.visit_generic_binder(&mut ccx, env_sig.as_ref(), def.r(s).generics);

        // Check the body
        if let Some(body) = *def.r(s).hir_body {
            let env_body = ccx.create_universal_env_for_fn_def(HrtbUniverse::ROOT_REF, def);

            let mut bcx = BodyCtxt::new(&mut ccx, def, env_body.as_ref());

            for arg in def.r(s).args.r(s) {
                let env = bcx.import_env;
                let ascription = bcx
                    .ccx_mut()
                    .import_report_here(&HrtbUniverse::ROOT, env, arg.ty);

                bcx.check_pat_demand(arg.pat, ascription, None);
            }

            bcx.check_expr_demand(body, bcx.return_ty).ignore();
            bcx.confirm(body);
        } else {
            for arg in def.r(s).args.r(s) {
                ccx.import_report_here(&HrtbUniverse::ROOT, env_sig.as_ref(), arg.ty);
            }

            ccx.import_report_here(&HrtbUniverse::ROOT, env_sig.as_ref(), *def.r(s).ret_ty);
        }

        ccx.verify();
    }
}

// === BodyCtxt === //

pub struct BodyCtxt<'a, 'tcx> {
    pub ccx: &'a mut ClauseCx<'tcx>,
    pub def: Obj<FnDef>,
    pub import_env: ClauseImportEnvRef<'a>,
    pub local_types: FxHashMap<Obj<HirLocal>, Ty>,
    pub local_confirmations: FxHashMap<Obj<HirLocal>, Obj<ThirLocal>>,
    pub block_break_demands: FxHashMap<HirLabelledBlock, Option<Ty>>,
    pub int_infers: Vec<InferTyVar>,
    pub expr_types_pre_coerce: FxHashMap<Obj<HirExpr>, Ty>,
    pub overload_resolutions: FxHashMap<Obj<HirExpr>, OverloadResolution>,
    pub pat_types_pre_adjust: FxHashMap<Obj<HirPat>, Ty>,
    pub return_ty: Ty,
}

#[derive(Debug, Copy, Clone)]
pub enum OverloadResolution {
    Primitive,
    Call,
    Error(ErrorGuaranteed),
}

impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
    pub fn new(
        ccx: &'a mut ClauseCx<'tcx>,
        def: Obj<FnDef>,
        import_env: ClauseImportEnvRef<'a>,
    ) -> Self {
        let s = ccx.session();

        let return_ty = ccx.import_report_here(&HrtbUniverse::ROOT, import_env, *def.r(s).ret_ty);

        Self {
            ccx,
            def,
            import_env,
            local_types: FxHashMap::default(),
            local_confirmations: FxHashMap::default(),
            block_break_demands: FxHashMap::default(),
            int_infers: Vec::new(),
            expr_types_pre_coerce: FxHashMap::default(),
            overload_resolutions: FxHashMap::default(),
            pat_types_pre_adjust: FxHashMap::default(),
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

    pub fn ucx(&self) -> &UnifyCx<'tcx> {
        self.ccx.ucx()
    }

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
