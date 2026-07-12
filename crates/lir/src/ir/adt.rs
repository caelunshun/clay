use crate::ir::{TypeParams, typ::StructTypeData};
use compact_str::CompactString;

/// A type that can have generic parameters.
#[salsa::tracked(debug)]
pub struct AlgebraicType<'db> {
    #[returns(ref)]
    pub name: CompactString,
    #[tracked]
    #[returns(ref)]
    pub type_params: TypeParams<'db>,
    #[tracked]
    #[returns(ref)]
    pub kind: AlgebraicTypeKind<'db>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub enum AlgebraicTypeKind<'db> {
    Struct(StructTypeData<'db>),
}
