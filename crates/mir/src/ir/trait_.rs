use crate::ir::{AbstractFuncInstance, Type, TypeArgs, TypeParams, context::TraitId};
use compact_str::CompactString;
use cranelift_entity::{PrimaryMap, SecondaryMap};
use salsa::Database;

#[salsa::tracked(debug)]
pub struct Trait<'db> {
    #[returns(ref)]
    #[tracked]
    pub data: TraitData<'db>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct TraitData<'db> {
    pub name: CompactString,
    pub type_params: TypeParams<'db>,
    pub assoc_funcs: PrimaryMap<AssocFuncId, AssocFunc<'db>>,
}

entity_ref_16bit! {
    pub struct AssocFuncId;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct AssocFunc<'db> {
    pub name: CompactString,
    pub type_params: TypeParams<'db>,
    pub param_types: Vec<Type<'db>>,
    pub return_type: Type<'db>,
}

#[salsa::interned(debug)]
pub struct TraitInstance<'db> {
    pub trait_: TraitId,
    #[returns(ref)]
    pub type_args: TypeArgs<'db>,
}

impl<'db> TraitInstance<'db> {
    pub fn substitute_type_args(&self, db: &'db dyn Database, type_args: &TypeArgs<'db>) -> Self {
        Self::new(
            db,
            self.trait_(db),
            self.type_args(db)
                .iter()
                .map(|(&param, ty)| (param, ty.substitute_type_args(db, type_args)))
                .collect::<TypeArgs<'db>>(),
        )
    }
}

#[salsa::tracked(debug)]
pub struct TraitImpl<'db> {
    #[returns(ref)]
    #[tracked]
    pub data: TraitImplData<'db>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct TraitImplData<'db> {
    pub type_params: TypeParams<'db>,
    /// Note: can refer to a type parameter....
    pub impl_for_type: Type<'db>,
    pub trait_: TraitInstance<'db>,
    /// Binds associated functions in the trait
    /// to the FuncInstances they should reference.
    pub assoc_func_bindings: SecondaryMap<AssocFuncId, Option<AbstractFuncInstance<'db>>>,
}
