use crate::subst_ty::SubstTy;
use clay_core::ghost_heap::{GhostPointee, GhostPtr};

#[derive(Debug, Clone)]
pub struct Val {
    pub ty: SubstTy,
}

unsafe impl<'g> GhostPointee<'g> for Val {
    type ForLt<'new_g> = Self;
}

pub type ValPtr<'g> = GhostPtr<'g, Val>;
