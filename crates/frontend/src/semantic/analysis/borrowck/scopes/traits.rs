use crate::{
    base::arena::Obj,
    bool_enum,
    semantic::{
        infer::{ClauseCx, ClauseImportEnv, ImplCache, UnifyCxMode},
        syntax::{FnDef, MirOperandMode, SigTy, TyCtxt},
    },
};

bool_enum! {
    pub enum CanOmitDrop {
        true => Yes;
        false => No;
    }
}

pub struct TraitCache<'tcx> {
    ccx: ClauseCx<'tcx>,
    env: ClauseImportEnv,
}

impl<'tcx> TraitCache<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, impl_cache: &'tcx ImplCache, def: Obj<FnDef>) -> Self {
        let s = &tcx.session;

        let mut ccx = ClauseCx::new(
            tcx,
            impl_cache,
            def.r(s).owner.as_item(s).r(s).krate,
            UnifyCxMode::RegionBlind,
        );

        let env = ccx.universal_env_for_fn_def(def);

        Self { ccx, env }
    }

    pub fn operand_mode(&mut self, ty: SigTy) -> MirOperandMode {
        MirOperandMode::Move
    }

    pub fn can_omit_drop(&mut self, ty: SigTy) -> CanOmitDrop {
        CanOmitDrop::Yes
    }
}
