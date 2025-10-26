use crate::ir::{Type, trait_::TraitInstance};
use cranelift_entity::{PrimaryMap, SecondaryMap};

entity_ref_16bit! {
    pub struct TypeParamId;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct TypeParam<'db> {
    /// Only allowed on trait type parameters.
    pub is_assoc_type: bool,
    /// Whether this is a "mirage" type parameter.
    /// Such a type is not allowed to be used
    /// anywhere. It only exists to terminate
    /// the otherwise infinite sequence of associated
    /// types that can arise.
    pub is_mirage: bool,
    /// Traits which must be implemented by the substituted type.
    pub trait_bounds: Vec<TraitInstance<'db>>,
}

/// List of type parameters for some item (trait impl, function, ADT, or trait).
pub type TypeParams<'db> = PrimaryMap<TypeParamId, TypeParam<'db>>;

/// Type arguments passed as type parameters.
pub type TypeArgs<'db> = SecondaryMap<TypeParamId, Option<Type<'db>>>;
