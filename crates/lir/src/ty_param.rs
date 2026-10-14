use crate::{arena::Ptr, subst_trait::SubstTrait};

#[derive(Clone, Debug)]
pub struct TyParam {
    pub trait_bounds: Vec<TraitBound>,
}

impl TyParam {
    pub fn unconstrained() -> Self {
        Self {
            trait_bounds: Vec::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TraitBound {
    /// Forall
    pub ty_params: Vec<Ptr<TyParam>>,
    pub trait_: SubstTrait,
}
