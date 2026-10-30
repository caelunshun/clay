use crate::{
    base::{Session, arena::Obj},
    bool_enum,
    semantic::{
        infer::{ClauseCx, ClauseImportEnv, ImplCache, UnifyCxMode},
        syntax::{FnDef, MirOperandMode, SigTy, SigTyKind, TyCtxt},
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

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    pub fn session(&self) -> &'tcx Session {
        &self.tcx().session
    }

    pub fn operand_mode(&mut self, ty: SigTy) -> MirOperandMode {
        // TODO
        MirOperandMode::Move
    }

    pub fn can_omit_drop(&mut self, ty: SigTy) -> CanOmitDrop {
        let s = self.session();

        match &ty.r(s).kind {
            SigTyKind::Tuple(ty) => {
                if ty.r(s).is_empty() {
                    return CanOmitDrop::Yes;
                }
            }
            _ => {
                // (fallthrough)
            }
        }

        CanOmitDrop::No
    }
}
