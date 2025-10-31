use crate::backend::{FloatBitness, IntBitness, ValId, ValTy};
use bumpalo::Bump;
use core::slice;
use mir::AlgebraicTypeKind;
use salsa::Database;

/// Representation of an mir value as an aggregate
/// of backend values. Effectively implements scalar
/// replacement of aggregates (SRoA).
#[derive(Debug, Copy, Clone)]
pub enum Compound<'bump> {
    Unit,
    Int(ValId),
    Real(ValId),
    Bool(ValId),
    Byte(ValId),
    Str {
        part0: ValId,
        part1: ValId,
    },
    /// For references, we track both the tagged
    /// pointer and the decoded (normalized) pointer,
    /// and rely on the backend to optimize out the
    /// unused portion if needed.
    MRef {
        tagged: ValId,
        untagged: ValId,
    },
    Bufref {
        ptr_tagged: ValId,
        ptr_untagged: ValId,
        len: ValId,
    },
    Struct {
        /// Ordered in the same order as the StructTypeData.fields.
        fields: &'bump [Compound<'bump>],
    },
}

impl<'bump> Compound<'bump> {
    /// Returns a flattened representation of all the backend vals
    /// in the compound value.
    ///
    /// The order is the same as the order of ValTys returned by `scalarize_type`.
    pub fn flatten(&'bump self, bump: &'bump Bump) -> &'bump [ValId] {
        match self {
            Compound::Unit => &[],
            Compound::Int(val_id)
            | Compound::Real(val_id)
            | Compound::Bool(val_id)
            | Compound::Byte(val_id) => slice::from_ref(val_id),
            Compound::Str { part0, part1 } => bump.alloc_slice_copy(&[*part0, *part1]),
            Compound::MRef { tagged, untagged } => bump.alloc_slice_copy(&[*tagged, *untagged]),
            Compound::Bufref {
                ptr_tagged,
                ptr_untagged,
                len,
            } => bump.alloc_slice_copy(&[*ptr_tagged, *ptr_untagged, *len]),
            Compound::Struct { fields } => {
                let vec = bumpalo::collections::Vec::from_iter_in(
                    fields.iter().flat_map(|f| f.flatten(bump).iter().copied()),
                    bump,
                );
                vec.into_bump_slice()
            }
        }
    }
}

/// Returns a flat representation of the ValTys corresponding to the given
/// mir Type, which is useful for constructing e.g. signatures.
pub fn scalarize_type<'bump, 'db>(
    db: &'db dyn Database,
    mir_cx: mir::Context<'db>,
    typ: mir::Type<'db>,
    bump: &'bump Bump,
) -> &'bump [ValTy] {
    match typ.kind(db) {
        mir::TypeKind::Prim(prim_type) => match *prim_type {
            mir::PrimType::Int => &[ValTy::Int(IntBitness::B64)],
            mir::PrimType::Real => &[ValTy::Float(FloatBitness::B64)],
            mir::PrimType::Byte | mir::PrimType::Bool => &[ValTy::Int(IntBitness::B8)],
            mir::PrimType::Str => &[ValTy::Int(IntBitness::B64), ValTy::Int(IntBitness::B64)],
            mir::PrimType::Unit => &[],
        },
        mir::TypeKind::MRef(_) => &[ValTy::Int(IntBitness::B64), ValTy::Int(IntBitness::B64)],
        mir::TypeKind::Bufref(_) => &[
            ValTy::Int(IntBitness::B64),
            ValTy::Int(IntBitness::B64),
            ValTy::Int(IntBitness::B64),
        ],
        mir::TypeKind::Algebraic(adt_instance) => {
            let AlgebraicTypeKind::Struct(struct_) = adt_instance.adt.resolve(db, mir_cx).kind(db);

            let mut tys = bumpalo::collections::Vec::new_in(bump);

            for field in struct_.fields.values() {
                tys.extend_from_slice_copy(scalarize_type(
                    db,
                    mir_cx,
                    field.typ.substitute_type_args(db, &adt_instance.type_args),
                    bump,
                ));
            }

            tys.into_bump_slice()
        }
        mir::TypeKind::TypeParam(_) => {
            panic!("type parameters must have been substituted")
        }

        mir::TypeKind::Self_ => panic!("Self type must be substituted during monomorphization"),
    }
}
