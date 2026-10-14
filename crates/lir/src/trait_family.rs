use crate::{adt_family::TyParam, arena::Ptr, sig_family::SigFamily};

/// A family of traits parametrized over a set of one or more type parameters.
#[derive(Debug, Clone)]
pub struct TraitFamily {
    pub ty_params: Vec<Ptr<TyParam>>,
    pub assoc_tys: Vec<Ptr<AssocTyFamily>>,
    pub assoc_funcs: Vec<Ptr<AssocFuncFamily>>,
}

#[derive(Debug, Clone)]
pub struct AssocTyFamily {
    pub ty_params: Vec<Ptr<TyParam>>,
}

#[derive(Debug, Clone)]
pub struct AssocFuncFamily {
    pub sig: SigFamily,
}
