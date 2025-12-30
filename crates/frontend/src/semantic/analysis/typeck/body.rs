use crate::{
    base::arena::{HasInterner, Obj},
    semantic::{
        analysis::{
            ClauseCx, ClauseImportEnv, CrateTypeckVisitor, TyFolderInfalliblePreservesSpans,
            TyVisitorInfallibleExt, UnifyCxMode,
        },
        syntax::{FnDef, FuncDefOwner, TyKind},
    },
};

impl<'tcx> CrateTypeckVisitor<'tcx> {
    pub fn visit_fn_def(&mut self, def: Obj<FnDef>) {
        let s = self.session();
        let tcx = self.tcx();

        // Setup a `ClauseCx` for signature validation.
        let mut ccx = ClauseCx::new(tcx, self.coherence, UnifyCxMode::RegionAware);
        let env = self.setup_env_for_fn_def(def, &mut ccx);

        // WF-check the signature.
        self.visit_generic_binder(
            &mut ccx,
            env.self_ty,
            &env.sig_generic_substs,
            def.r(s).generics,
        );

        // TODO
        // if let Some(self_param) = *def.r(s).self_param {
        //     self.visit_spanned_ty(self_param)?;
        // }

        for arg in def.r(s).args.r(s) {
            let arg = ccx
                .importer(env.self_ty, &env.sig_generic_substs)
                .fold_spanned_ty(arg.ty);

            ccx.wf_visitor().visit_spanned(arg);
        }

        let ret_ty = ccx
            .importer(env.self_ty, &env.sig_generic_substs)
            .fold_spanned_ty(*def.r(s).ret_ty);

        ccx.wf_visitor().visit_spanned(ret_ty);

        // Check the body
        // TODO
    }

    fn setup_env_for_fn_def(
        &mut self,
        def: Obj<FnDef>,
        ccx: &mut ClauseCx<'tcx>,
    ) -> ClauseImportEnv {
        let s = self.session();
        let tcx = self.tcx();

        let mut env = match def.r(s).owner {
            FuncDefOwner::Func(_item) => ClauseImportEnv {
                self_ty: tcx.intern(TyKind::SigThis),
                sig_generic_substs: Vec::new(),
            },
            FuncDefOwner::Method(def, _idx) => ccx.import_impl_block_env(def),
        };

        env.sig_generic_substs
            .extend_from_slice(&ccx.import_fn_item_env(env.self_ty, def));

        env
    }
}
