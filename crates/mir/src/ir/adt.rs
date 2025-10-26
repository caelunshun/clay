use crate::ir::{
    context::AlgebraicTypeId,
    typ::{StructTypeData, Type, TypeKind},
    type_param::{TypeParam, TypeParamId},
};
use compact_str::CompactString;
use cranelift_entity::{PrimaryMap, SecondaryMap};
use salsa::Database;

/// A type that can have generic parameters.
#[salsa::tracked(debug)]
pub struct AlgebraicType<'db> {
    #[returns(ref)]
    pub name: CompactString,
    #[tracked]
    #[returns(ref)]
    pub type_params: PrimaryMap<TypeParamId, TypeParam<'db>>,
    #[tracked]
    #[returns(ref)]
    pub data: AlgebraicTypeData<'db>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub enum AlgebraicTypeData<'db> {
    Struct(StructTypeData<'db>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct AlgebraicTypeInstance<'db> {
    pub adt: AlgebraicTypeId,
    pub type_args: SecondaryMap<TypeParamId, Option<Type<'db>>>,
}

impl<'db> AlgebraicTypeInstance<'db> {
    /// Substitute type arguments into type parameters.
    pub fn substitute_type_args(&self, typ: Type<'db>, db: &'db dyn Database) -> Type<'db> {
        match typ.kind(db) {
            TypeKind::TypeParam(p) => self.type_args[*p].clone().unwrap(),
            typ => Type::new(
                db,
                typ.map_inner_types(|typ| self.substitute_type_args(typ, db)),
            ),
        }
    }
}
