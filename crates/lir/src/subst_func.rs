use crate::{arena::Ptr, func_family::FuncFamily, subst_ty::SubstTyArgs};

/// Reference to an instance of a func.
#[derive(Debug, Clone)]
pub struct SubstFunc {
    pub ty_args: SubstTyArgs,
    pub family: Ptr<FuncFamily>,
}
