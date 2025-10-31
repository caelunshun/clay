//! Memory layout calculations for fir types.

use cranelift_entity::SecondaryMap;
use mir::{AlgebraicType, AlgebraicTypeKind, Context, PrimType, TypeArgs};
use salsa::Database;
use std::{alloc::Layout, cmp};

/// Returns the layout of the given MIR type.
#[salsa::tracked]
pub fn layout_of<'db>(
    db: &'db dyn Database,
    cx: Context<'db>,
    typ: mir::Type<'db>,
    type_args: TypeArgs<'db>,
) -> Layout {
    match typ.kind(db) {
        mir::TypeKind::Prim(prim) => layout_of_prim(*prim),
        mir::TypeKind::MRef(_) => Layout::new::<usize>(),
        // Fat pointer: (ptr, len).
        mir::TypeKind::Bufref(_) => Layout::from_size_align(16, 16).unwrap(),
        mir::TypeKind::Algebraic(adt_instance) => {
            let adt_type_args = adt_instance
                .type_args
                .iter()
                .map(|(param, arg)| (*param, arg.substitute_type_args(db, &type_args)))
                .collect();
            fields_layout_of_struct(db, cx, adt_instance.adt.resolve(db, cx), adt_type_args)
                .total_layout()
        }
        mir::TypeKind::TypeParam(type_param_id) => {
            layout_of(db, cx, type_args[type_param_id], type_args.clone())
        }
        mir::TypeKind::Self_ => panic!("Self type must be substituted during monomorphization"),
    }
}

pub fn layout_of_prim(prim: PrimType) -> Layout {
    match prim {
        PrimType::Int => Layout::new::<i64>(),
        PrimType::Real => Layout::new::<f64>(),
        PrimType::Byte => Layout::new::<u8>(),
        PrimType::Bool => Layout::new::<bool>(),
        PrimType::Str => Layout::from_size_align(16, 16).unwrap(),
        PrimType::Unit => Layout::new::<()>(),
    }
}

/// Computes the offsets of each field in a struct relative to the struct base.
#[salsa::tracked]
pub fn fields_layout_of_struct<'db>(
    db: &'db dyn Database,
    cx: Context<'db>,
    adt: AlgebraicType<'db>,
    type_args: TypeArgs<'db>,
) -> FieldsLayout {
    let AlgebraicTypeKind::Struct(struct_) = adt.kind(db);

    // Strategy: order fields from greatest to smallest alignment,
    // which minimizes total padding under the assumption that
    // each field's size is a multiple of its alignment.

    let mut sorted_field_layouts = struct_
        .fields
        .iter()
        .map(|(field_id, field)| (field_id, layout_of(db, cx, field.typ, type_args.clone())))
        .collect::<Vec<_>>();

    // We want a stable sort here to ensure determinism.
    sorted_field_layouts.sort_by_key(|(_, layout)| cmp::Reverse(layout.align()));

    let mut total_layout = Layout::new::<()>();
    let mut field_offsets = SecondaryMap::new();

    for (field_id, field_layout) in sorted_field_layouts {
        let (new_total_layout, field_offset) =
            total_layout.extend(field_layout).expect("layout overflow");
        total_layout = new_total_layout;
        field_offsets[field_id] = field_offset;
    }

    FieldsLayout {
        field_offsets,
        total_layout,
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FieldsLayout {
    field_offsets: SecondaryMap<mir::FieldId, usize>,
    total_layout: Layout,
}

impl FieldsLayout {
    pub fn offset_of(&self, field: mir::FieldId) -> usize {
        self.field_offsets[field]
    }

    pub fn total_layout(&self) -> Layout {
        self.total_layout
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelift_entity::PrimaryMap;
    use mir::{
        AlgebraicTypeInstance, AlgebraicTypeKind, ContextBuilder, Field, StructTypeData, Type,
        TypeKind, TypeParams,
    };
    use salsa::DatabaseImpl;

    #[test]
    fn optimized_struct_layout() {
        let db = DatabaseImpl::new();

        #[salsa::tracked]
        fn helper<'db>(db: &'db dyn Database) {
            let mut fields = PrimaryMap::new();
            let f0 = fields.push(Field {
                name: "f0".into(),
                typ: Type::byte(db),
            });
            let f1 = fields.push(Field {
                name: "f1".into(),
                typ: Type::str(db),
            });
            let f2 = fields.push(Field {
                name: "f2".into(),
                typ: Type::int(db),
            });
            let struct_ = AlgebraicType::new(
                db,
                "Big".into(),
                TypeParams::default(),
                AlgebraicTypeKind::Struct(StructTypeData { fields }),
            );

            let mut cx = ContextBuilder::new();
            let struct_id = cx.add_adt(struct_);
            let cx = cx.finish(db);

            let struct_layout = layout_of(
                db,
                cx,
                Type::new(
                    db,
                    TypeKind::Algebraic(AlgebraicTypeInstance {
                        adt: struct_id,
                        type_args: Default::default(),
                    }),
                ),
                TypeArgs::default(),
            );
            assert_eq!(struct_layout.size(), 25);
            assert_eq!(struct_layout.align(), 16);

            let fields_layout = fields_layout_of_struct(db, cx, struct_, TypeArgs::default());
            assert_eq!(fields_layout.total_layout(), struct_layout);
            assert_eq!(fields_layout.offset_of(f0), 24);
            assert_eq!(fields_layout.offset_of(f1), 0);
            assert_eq!(fields_layout.offset_of(f2), 16);
        }

        helper(&db);
    }
}
