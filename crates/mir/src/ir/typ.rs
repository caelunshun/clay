use crate::ir::{AlgebraicTypeInstance, TypeParamId};
use compact_str::CompactString;
use cranelift_entity::PrimaryMap;
use salsa::Database;

/// An interned version of `TypeKind`.
#[salsa::interned(debug)]
pub struct Type<'db> {
    #[returns(ref)]
    pub kind: TypeKind<'db>,
}

impl<'db> Type<'db> {
    pub fn int(db: &'db dyn Database) -> Self {
        Type::new(db, TypeKind::int())
    }

    pub fn real(db: &'db dyn Database) -> Self {
        Type::new(db, TypeKind::real())
    }

    pub fn bool(db: &'db dyn Database) -> Self {
        Type::new(db, TypeKind::bool())
    }

    pub fn byte(db: &'db dyn Database) -> Self {
        Type::new(db, TypeKind::byte())
    }

    pub fn unit(db: &'db dyn Database) -> Self {
        Type::new(db, TypeKind::unit())
    }

    pub fn str(db: &'db dyn Database) -> Self {
        Type::new(db, TypeKind::str())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub enum TypeKind<'db> {
    Prim(PrimType),
    /// Reference to an object managed by the garbage collector,
    /// or to a field of an object managed by the garbage collector,
    /// or to an element of a list.
    /// It has indefinite lifetime.
    MRef(Type<'db>),
    Func(FuncTypeData<'db>),
    /// Dynamically resized array.
    List(Type<'db>),
    Algebraic(AlgebraicTypeInstance<'db>),
    /// Generic type in the current scope.
    TypeParam(TypeParamId),
    /// Only valid inside a trait definition.
    Self_,
}

impl<'db> TypeKind<'db> {
    pub fn bool() -> Self {
        Self::Prim(PrimType::Bool)
    }

    pub fn int() -> Self {
        Self::Prim(PrimType::Int)
    }

    pub fn real() -> Self {
        Self::Prim(PrimType::Real)
    }

    pub fn byte() -> Self {
        Self::Prim(PrimType::Byte)
    }

    pub fn str() -> Self {
        Self::Prim(PrimType::Str)
    }

    pub fn unit() -> Self {
        Self::Prim(PrimType::Unit)
    }

    pub fn map_inner_types(&self, mut map: impl FnMut(Type<'db>) -> Type<'db>) -> Self {
        match self {
            TypeKind::Prim(_) | TypeKind::TypeParam(_) | TypeKind::Self_ => self.clone(),
            TypeKind::MRef(type_kind) => TypeKind::MRef(map(*type_kind)),
            TypeKind::Func(func_type_data) => TypeKind::Func(FuncTypeData {
                param_types: func_type_data
                    .param_types
                    .iter()
                    .copied()
                    .map(&mut map)
                    .collect(),
                return_type: map(func_type_data.return_type),
            }),
            TypeKind::List(type_kind) => TypeKind::List(map(*type_kind)),
            TypeKind::Algebraic(algebraic_type_instance) => {
                TypeKind::Algebraic(AlgebraicTypeInstance {
                    adt: algebraic_type_instance.adt,
                    type_args: algebraic_type_instance
                        .type_args
                        .iter()
                        .map(|(arg, ty)| {
                            if let Some(ty) = ty {
                                (arg, Some(map(*ty)))
                            } else {
                                (arg, None)
                            }
                        })
                        .collect(),
                })
            }
        }
    }
}

/// Type built in to the engine.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, salsa::Update)]
pub enum PrimType {
    /// 64-bit signed integer.
    Int,
    /// 64-bit float.
    Real,
    /// 8-bit unsigned value.
    Byte,
    /// Boolean.
    Bool,
    /// Immutable UTF-8 string.
    Str,
    /// The empty type, having only one value.
    Unit,
}

/// A closure object, consisting of a dynamic
/// function reference and a reference to an opaque
/// captures struct.
#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct FuncTypeData<'db> {
    pub param_types: Vec<Type<'db>>,
    pub return_type: Type<'db>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct StructTypeData<'db> {
    pub fields: PrimaryMap<FieldId, Field<'db>>,
}

entity_ref_16bit! {
    pub struct FieldId;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct Field<'db> {
    pub name: CompactString,
    pub typ: Type<'db>,
}
