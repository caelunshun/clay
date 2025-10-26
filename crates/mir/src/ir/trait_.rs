use crate::{
    TypeKind,
    ir::{Type, TypeParam, TypeParamId, context::TraitId},
};
use compact_str::CompactString;
use cranelift_entity::{PrimaryMap, SecondaryMap};

#[salsa::tracked(debug)]
pub struct Trait<'db> {
    #[returns(ref)]
    #[tracked]
    pub data: TraitData<'db>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct TraitData<'db> {
    pub name: CompactString,
    pub type_params: PrimaryMap<TypeParamId, TypeParam<'db>>,
    pub assoc_funcs: PrimaryMap<AssocFuncId, AssocFunc<'db>>,
}

entity_ref_16bit! {
    pub struct AssocFuncId;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct AssocFunc<'db> {
    pub name: CompactString,
    pub param_types: Vec<Type<'db>>,
    pub return_type: Type<'db>,
}

#[salsa::interned(debug)]
pub struct TraitInstance<'db> {
    pub trait_: TraitId,
    #[returns(ref)]
    pub type_args: SecondaryMap<TypeParamId, Option<TypeKind<'db>>>,
}

#[salsa::tracked(debug)]
pub struct TraitImpl<'db> {
    #[returns(ref)]
    #[tracked]
    pub data: TraitImplData<'db>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct TraitImplData<'db> {
    pub type_params: PrimaryMap<TypeParamId, TypeParam<'db>>,
    /// Note: can refer to a type parameter....
    pub impl_for_type: Type<'db>,
    pub trait_: TraitInstance<'db>,
}
