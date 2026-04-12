use crate::{
    base::{
        Diag, ErrorGuaranteed, Session,
        analysis::SpannedViewEncode,
        arena::{HasInterner, HasListInterner as _, Obj},
        syntax::HasSpan,
    },
    parse::ast::{AstLit, AstUnOpKind},
    semantic::{
        analysis::{
            ClauseCx, ClauseError, ClauseImportEnvRef, ClauseOrigin, ClauseOriginKind,
            CrateTypeckVisitor, EquateOrSet, HrtbUniverse, TyCtxt, TyFolderInfallibleExt,
            TyVisitorInfallibleExt, UnifyCx, UnifyCxMode, peel_ref_for_prim_op,
            typeck::body::lookup::LookupMethodResult,
        },
        lower::generics::normalize_positional_generic_arity,
        syntax::{
            AdtInstance, Crate, Divergence, FnDef, FnInstanceInner, HirBlock, HirExpr, HirExprKind,
            HirLabelTargetKind, HirLabelledBlock, HirLocal, HirPat, HirStmt, InferTyVar,
            InferTyVarSourceInfo, Item, Re, RelationMode, SimpleTyKind, SimpleTySet,
            SpannedFnInstanceView, SpannedFnOwnerView, SpannedTyView, ThirLocal, TraitParam,
            TraitSpec, Ty, TyAndDivergence, TyKind, TyOrRe,
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
        let env_sig = ccx.import_fn_def_env_as_universal(
            &ClauseOrigin::empty_report(),
            HrtbUniverse::ROOT_REF,
            def,
        );

        // WF-check the signature.
        self.visit_generic_binder(&mut ccx, env_sig.as_ref(), def.r(s).generics);

        // Check the body
        if let Some(body) = *def.r(s).hir_body {
            let env_body = ccx.import_fn_def_env_as_universal(
                &ClauseOrigin::empty_report(),
                HrtbUniverse::ROOT_REF,
                def,
            );

            let mut bcx = BodyCtxt::new(&mut ccx, def, env_body.as_ref());

            for arg in def.r(s).args.r(s) {
                let env = bcx.import_env;
                let ascription = bcx
                    .ccx_mut()
                    .importer(&ClauseOrigin::empty_report(), HrtbUniverse::ROOT, env)
                    .fold_preserved(arg.ty);

                bcx.ccx_mut()
                    .wf_visitor(HrtbUniverse::ROOT)
                    .visit_spanned(ascription);

                bcx.check_pat_demand(arg.pat, ascription.value, None);
            }

            bcx.check_expr_demand(body, bcx.return_ty).ignore();
            bcx.confirm(body);
        } else {
            for arg in def.r(s).args.r(s) {
                let arg = ccx
                    .importer(
                        &ClauseOrigin::empty_report(),
                        HrtbUniverse::ROOT,
                        env_sig.as_ref(),
                    )
                    .fold_preserved(arg.ty);

                ccx.wf_visitor(HrtbUniverse::ROOT).visit_spanned(arg);
            }

            let ret_ty = ccx
                .importer(
                    &ClauseOrigin::empty_report(),
                    HrtbUniverse::ROOT,
                    env_sig.as_ref(),
                )
                .fold_preserved(*def.r(s).ret_ty);

            ccx.wf_visitor(HrtbUniverse::ROOT).visit_spanned(ret_ty);
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

        let return_ty = ccx
            .importer(
                &ClauseOrigin::empty_report(),
                HrtbUniverse::ROOT,
                import_env,
            )
            .fold_spanned(*def.r(s).ret_ty);

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
