use crate::ir::{
    AlgebraicTypeId, AssocFuncId, ContextLike, FuncId, TraitId, TraitImplId, Type,
    trait_::TraitInstance,
};
use compact_str::CompactString;
use cranelift_entity::PrimaryMap;
use salsa::Database;
use std::collections::BTreeMap;

entity_ref_16bit! {
    pub struct TypeParamIndex;
}

/// Uniquely identifies a type parameter in a particular scope.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, salsa::Update)]
pub struct TypeParamId {
    pub idx: TypeParamIndex,
    pub scope: TypeParamScope,
}

impl TypeParamId {
    pub fn resolve<'a, 'db>(
        self,
        db: &'db dyn Database,
        cx: &'a impl ContextLike<'db>,
    ) -> &'a TypeParam<'db> {
        match self.scope {
            TypeParamScope::Trait(trait_id) => {
                &trait_id.resolve(db, cx).data(db).type_params[self.idx]
            }
            TypeParamScope::Func(func_id) => &func_id.resolve_header(db, cx).type_params[self.idx],
            TypeParamScope::AssocFunc(trait_id, assoc_func_id) => {
                &trait_id.resolve(db, cx).data(db).assoc_funcs[assoc_func_id].type_params[self.idx]
            }
            TypeParamScope::Adt(algebraic_type_id) => {
                &algebraic_type_id.resolve(db, cx).type_params(db)[self.idx]
            }
            TypeParamScope::TraitImpl(trait_impl_id) => {
                &trait_impl_id.resolve(db, cx).data(db).type_params[self.idx]
            }
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, salsa::Update)]
pub enum TypeParamScope {
    Trait(TraitId),
    Func(FuncId),
    AssocFunc(TraitId, AssocFuncId),
    Adt(AlgebraicTypeId),
    TraitImpl(TraitImplId),
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
    pub name: CompactString,
}

/// List of type parameters for some item (trait impl, function, ADT, or trait).
pub type TypeParams<'db> = PrimaryMap<TypeParamIndex, TypeParam<'db>>;

/// Type arguments passed as type parameters.
pub type TypeArgs<'db> = BTreeMap<TypeParamId, Type<'db>>;

pub fn merge_type_args<'db>(a: &TypeArgs<'db>, b: &TypeArgs<'db>) -> TypeArgs<'db> {
    a.iter()
        .map(|(k, v)| (*k, *v))
        .chain(b.iter().map(|(k, v)| (*k, *v)))
        .collect()
}
