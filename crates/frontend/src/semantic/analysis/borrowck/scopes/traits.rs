use crate::{
    base::{Obj, Session},
    bool_enum,
    semantic::{
        analysis::TyCtxt,
        infer::{ClauseCx, ClauseImportEnv, UnifyCxMode},
        syntax::{FnDef, MirOperandMode, SigTy, SigTyKind},
    },
};

bool_enum! {
    pub enum CanOmitDrop {
        true => Yes;
        false => No;
    }
}

pub struct TraitCache<'sess> {
    ccx: ClauseCx<'sess>,
    env: ClauseImportEnv,
}

impl<'sess> TraitCache<'sess> {
    pub fn new(tcx: &'sess TyCtxt<'sess>, def: Obj<FnDef>) -> Self {
        let mut ccx = ClauseCx::new(tcx, UnifyCxMode::RegionBlind);

        let env = ccx.universal_env_for_fn_def(def);

        Self { ccx, env }
    }

    pub fn session(&self) -> &'sess Session {
        self.ccx.session()
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
