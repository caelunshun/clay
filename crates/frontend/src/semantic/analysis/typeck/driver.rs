use crate::{
    base::{Obj, Session},
    semantic::{
        analysis::{TyCtxt, typeck::infra::confirm::BodyCtxtConfirmState},
        infer::{ClauseCx, ClauseImportEnv, HrtbUniverse, UnifyCxMode},
        syntax::{
            FnDef, HirLabelledBlock, HirLocal, InferTyVarSourceInfo, Item, LangItems, ThirBody, Ty,
        },
    },
    utils::mem::LateInit,
};
use clay_core::FastHashMap;

// === Driver === //

impl TyCtxt<'_> {
    pub fn type_check_function(&self, def: Obj<FnDef>) {
        let s = self.session();

        // Setup a `ClauseCx` for signature validation.
        {
            let mut ccx = ClauseCx::new(self, UnifyCxMode::RegionAware);
            let env_sig = ccx.universal_env_for_fn_def(def);

            // WF-check the signature.
            self.visit_generic_binder(&mut ccx, &env_sig, def.r(s).generics);

            for arg in def.r(s).args.r(s) {
                ccx.import_here(&env_sig, arg.ty);
            }

            ccx.import_here(&env_sig, *def.r(s).ret_ty);

            ccx.verify();
        }

        // Check the body
        let mut ccx = ClauseCx::new(self, UnifyCxMode::RegionBlind);
        let env_sig = ccx.universal_env_for_fn_def(def);

        let Some(body) = *def.r(s).hir_body else {
            LateInit::init(&def.r(s).thir_body, None);
            return;
        };

        let mut bcx = BodyCtxt::new(&mut ccx, def, &env_sig);

        for arg in def.r(s).args.r(s) {
            let env = bcx.import_env;
            let ascription = bcx.ccx_mut().import_elsewhere(env, arg.ty);

            bcx.check_pat_demand(arg.pat, ascription, None);
        }

        bcx.check_expr_demand(body, bcx.return_ty)
            .ignore_divergence();

        bcx.begin_confirmation();

        let arg_pats = def
            .r(s)
            .args
            .r(s)
            .iter()
            .map(|arg| bcx.confirm_thir_pat_outer(arg.pat))
            .collect::<Vec<_>>();

        let body = bcx.confirm_thir_expr_post(body);

        LateInit::init(
            &def.r(s).thir_body,
            Some(ThirBody {
                arg_pats,
                expr: body,
            }),
        );

        drop(bcx);

        ccx.verify();
    }
}

// === BodyCtxt === //

pub(super) struct BodyCtxt<'a, 'sess> {
    pub ccx: &'a mut ClauseCx<'sess>,
    pub def: Obj<FnDef>,
    pub import_env: &'a ClauseImportEnv,
    pub local_types: FastHashMap<Obj<HirLocal>, Ty>,
    pub block_break_demands: FastHashMap<HirLabelledBlock, Option<Ty>>,
    pub confirm_state: BodyCtxtConfirmState<'a, 'sess>,
    pub return_ty: Ty,
}

impl<'a, 'sess> BodyCtxt<'a, 'sess> {
    pub fn new(
        ccx: &'a mut ClauseCx<'sess>,
        def: Obj<FnDef>,
        import_env: &'a ClauseImportEnv,
    ) -> Self {
        let s = ccx.session();

        let return_ty = ccx.import_elsewhere(import_env, *def.r(s).ret_ty);

        Self {
            ccx,
            def,
            import_env,
            local_types: FastHashMap::default(),
            block_break_demands: FastHashMap::default(),
            confirm_state: BodyCtxtConfirmState::default(),
            return_ty,
        }
    }

    pub fn session(&self) -> &'sess Session {
        self.ccx.session()
    }

    pub fn lang_items(&self) -> &'sess LangItems {
        self.ccx().lang_items()
    }

    pub fn item(&self) -> Obj<Item> {
        let s = self.session();
        self.def.r(s).owner.as_item(s)
    }

    pub fn ccx(&self) -> &ClauseCx<'sess> {
        self.ccx
    }

    pub fn ccx_mut(&mut self) -> &mut ClauseCx<'sess> {
        self.ccx
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
