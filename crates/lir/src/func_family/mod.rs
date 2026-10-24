use crate::{arena::Ptr, subst_ty::SubstTy, ty_param::TyParam};
use clay_core::ghost_heap::GhostHeap;

pub mod basic_block;
pub mod terminator;
pub mod val;

pub struct FuncFamily {
    pub ty_params: Vec<Ptr<TyParam>>,
    pub param_tys: Vec<SubstTy>,
    pub ret_ty: SubstTy,

    pub heap: GhostHeap<'static>,
}
