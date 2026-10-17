use crate::{
    arena::Ptr, func_family::val::Val, pool::LocalPool, subst_ty::SubstTy, ty_param::TyParam,
};

pub mod basic_block;
pub mod instr;
pub mod terminator;
pub mod val;

#[derive(Debug, Clone)]
pub struct FuncFamily {
    pub ty_params: Vec<Ptr<TyParam>>,
    pub param_tys: Vec<SubstTy>,
    pub ret_ty: SubstTy,

    pub val_pool: LocalPool<Val>,
}
