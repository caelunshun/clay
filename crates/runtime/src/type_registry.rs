use crate::{engine::Module, ptr::MRef, Func};
use bytecode::{module::Field, LocalType, ModuleData, PrimitiveType};
use cranelift_entity::{EntityRef, PrimaryMap, SecondaryMap};
use hashbrown::HashMap;
use std::{alloc::Layout, cmp};
use zyon_bytecode::entity_ref;

entity_ref! {
    /// ID of a type in an `Engine`.
    pub struct Type;
}

pub struct TypeRegistry {
    /// Types used in modules.
    pub types: PrimaryMap<Type, TypeData>,
    /// Quick access to type layouts.
    pub layouts: SecondaryMap<Type, Option<Layout>>,
    /// Maps `LocalType` IDs within each module to an engine-global
    /// `Type`.
    pub module_mapping: SecondaryMap<Module, SecondaryMap<LocalType, Type>>,

    /// Type constant for `int`.
    pub int_type: Type,
    /// Type constant for `real`.
    pub real_type: Type,
    /// Type constant for `bool`.
    pub bool_type: Type,
    /// Type constant for `()`.
    pub unit_type: Type,
}

impl Default for TypeRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeRegistry {
    pub fn new() -> Self {
        let mut types = PrimaryMap::new();
        let int_type = types.push(TypeData::primitive(PrimitiveType::Int));
        let real_type = types.push(TypeData::primitive(PrimitiveType::Real));
        let bool_type = types.push(TypeData::primitive(PrimitiveType::Bool));
        let unit_type = types.push(TypeData::primitive(PrimitiveType::Unit));

        Self {
            types,
            layouts: SecondaryMap::default(),
            module_mapping: SecondaryMap::default(),
            int_type,
            real_type,
            bool_type,
            unit_type,
        }
    }

    pub fn primitive(&self, typ: PrimitiveType) -> Type {
        match typ {
            PrimitiveType::Int => self.int_type,
            PrimitiveType::Real => self.real_type,
            PrimitiveType::Bool => self.bool_type,
            PrimitiveType::Unit => self.unit_type,
        }
    }

    /// Gets the `TypeData` registration for a type given its module
    /// and local type ID.
    pub fn local_type_data(&self, module: Module, typ: LocalType) -> &TypeData {
        &self.types[self.module_mapping[module][typ]]
    }

    pub fn load_module_types(&mut self, module_id: Module, module: &ModuleData) {
        // Since there can be cycles / recursions in the type graph,
        // we need to first compute the ID mapping (by assuming internal behaviors
        // for PrimaryMap) before constructing the TypeDatas.
        let mut id_mapping = SecondaryMap::with_capacity(module.types.len());
        let mut next_id = self.types.len();
        for (type_id, typ) in &module.types {
            let mapped_id = match typ {
                bytecode::TypeData::Primitive(p) => self.primitive(*p),
                // TypeData::Import TODO
                _ => {
                    let id = Type::new(next_id);
                    next_id += 1;
                    id
                }
            };
            id_mapping[type_id] = mapped_id;
        }

        let mut structs_to_lay_out = Vec::new();

        for (local_type_id, typ) in &module.types {
            let mapped_id = match typ {
                bytecode::TypeData::Reference(t) => self.types.push(TypeData {
                    kind: TypeKind::Reference(id_mapping[*t]),
                    local_ids: HashMap::new(),
                }),
                bytecode::TypeData::Func(f) => self.types.push(TypeData {
                    kind: TypeKind::Func(FuncType {
                        param_types: f.param_types.iter().map(|&id| id_mapping[id]).collect(),
                        return_type: id_mapping[f.return_type],
                    }),
                    local_ids: HashMap::new(),
                }),
                bytecode::TypeData::Lazy(l) => self.types.push(TypeData {
                    kind: TypeKind::Lazy(id_mapping[l.inner_type]),
                    local_ids: HashMap::new(),
                }),
                bytecode::TypeData::Struct(_) => {
                    structs_to_lay_out.push(local_type_id);
                    self.types.push(TypeData {
                        kind: TypeKind::Struct(StructLayout::placeholder()),
                        local_ids: HashMap::new(),
                    })
                }
                bytecode::TypeData::Primitive(p) => self.primitive(*p),
            };

            debug_assert_eq!(mapped_id, id_mapping[local_type_id]);

            self.types[mapped_id]
                .local_ids
                .insert(module_id, local_type_id);
        }

        for struct_id in structs_to_lay_out {
            let typ = &self.types[id_mapping[struct_id]];
            let TypeKind::Struct(s) = &typ.kind else {
                unreachable!()
            };
            if !s.initialized {
                let bytecode::TypeData::Struct(s_bytecode) = &module.types[struct_id] else {
                    unreachable!()
                };
                self.types[id_mapping[struct_id]].kind = TypeKind::Struct(StructLayout::compute(
                    s_bytecode,
                    module,
                    self,
                    &mut Vec::new(),
                    &id_mapping,
                ));
            }
        }

        for local_type_id in module.types.keys() {
            let type_id = id_mapping[local_type_id];
            self.layouts[type_id] = Some(self.types[type_id].kind.layout(self));
        }

        self.module_mapping[module_id] = id_mapping;
    }

    /// Traverses all references stored inline in the given type
    /// by providing their byte offsets from the start of this object.
    pub fn traverse_references(&self, typ: Type, mut callback: impl FnMut(usize)) {
        self.traverse_references_inner(typ, &mut callback, 0)
    }

    fn traverse_references_inner(
        &self,
        typ: Type,
        callback: &mut impl FnMut(usize),
        start_offset: usize,
    ) {
        let type_data = &self.types[typ];
        match &type_data.kind {
            TypeKind::Struct(s) => {
                for field in s.fields.values() {
                    self.traverse_references_inner(
                        field.field_type,
                        callback,
                        start_offset + field.offset,
                    );
                }
            }
            TypeKind::Primitive(_) => {}
            TypeKind::Reference(_) => {
                callback(start_offset);
            }
            TypeKind::Lazy(t) => self.traverse_references_inner(
                *t,
                callback,
                start_offset + LazyLayout::new(self.layouts[*t].unwrap()).value_offset,
            ),
            TypeKind::Func(_) => {
                callback(start_offset + FuncLayout::new().captures_offset);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeData {
    pub kind: TypeKind,
    /// ID of the type within each module that uses it.
    pub local_ids: HashMap<Module, bytecode::LocalType>,
}

impl TypeData {
    fn primitive(prim: PrimitiveType) -> Self {
        Self {
            kind: TypeKind::Primitive(prim),
            local_ids: HashMap::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeKind {
    Struct(StructLayout),
    Primitive(PrimitiveType),
    Reference(Type),
    Lazy(Type),
    Func(FuncType),
}

impl TypeKind {
    pub fn layout(&self, registry: &TypeRegistry) -> Layout {
        match self {
            TypeKind::Struct(s) => s.overall,
            TypeKind::Primitive(p) => match *p {
                PrimitiveType::Int => Layout::new::<i64>(),
                PrimitiveType::Real => Layout::new::<f64>(),
                PrimitiveType::Bool => Layout::new::<bool>(),
                PrimitiveType::Unit => Layout::new::<()>(),
            },
            TypeKind::Reference(_) => Layout::new::<MRef>(),
            TypeKind::Lazy(value_type) => {
                let value_layout = registry.types[*value_type].kind.layout(registry);
                LazyLayout::new(value_layout).overall
            }
            TypeKind::Func(_) => FuncLayout::new().overall,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructLayout {
    pub overall: Layout,
    pub fields: SecondaryMap<Field, LayoutFieldEntry>,
    initialized: bool,
}

impl StructLayout {
    /// Placeholder value used before layout initialization.
    fn placeholder() -> Self {
        Self {
            overall: Layout::new::<()>(),
            fields: SecondaryMap::default(),
            initialized: false,
        }
    }

    /// Computes a struct layout from the fields in the bytecode,
    /// panicking if the layout forms a cycle.
    fn compute(
        struct_: &bytecode::module::StructTypeData,
        module: &bytecode::ModuleData,
        type_registry: &mut TypeRegistry,
        visited: &mut Vec<Type>,
        id_mapping: &SecondaryMap<LocalType, Type>,
    ) -> Self {
        let mut layout = Layout::new::<()>();
        let mut fields = SecondaryMap::with_capacity(struct_.fields.len());

        // Heuristic: by ordering larger fields first,
        // we try to reduce the amount of padding in between fields.
        let mut fields_sorted = struct_
            .fields
            .iter()
            .map(|(field, field_data)| {
                let field_type = id_mapping[field_data.typ];
                let field_layout = match &type_registry.types[field_type].kind {
                    TypeKind::Struct(s) if !s.initialized => {
                        assert!(
                            !visited.contains(&field_type),
                            "recursive struct encountered"
                        );
                        visited.push(field_type);
                        let bytecode::TypeData::Struct(s2) = &module.types[field_data.typ] else {
                            unreachable!()
                        };
                        type_registry.types[field_type].kind = TypeKind::Struct(
                            StructLayout::compute(s2, module, type_registry, visited, id_mapping),
                        );
                        type_registry.types[field_type].kind.layout(type_registry)
                    }
                    k => k.layout(type_registry),
                };
                (field, field_data, field_layout)
            })
            .collect::<Vec<_>>();
        fields_sorted.sort_unstable_by_key(|(_, _, layout)| cmp::Reverse(layout.size()));

        for (field, field_data, field_layout) in fields_sorted {
            let field_type = id_mapping[field_data.typ];
            let (new_layout, field_offset) = layout
                .extend(field_layout)
                .expect("layout overflow in struct");
            fields[field] = LayoutFieldEntry {
                field_type,
                offset: field_offset,
                size: field_layout.size(),
            };
            layout = new_layout;
        }

        Self {
            overall: layout,
            fields,
            initialized: true,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct LayoutFieldEntry {
    pub field_type: Type,
    /// Offset from the start of the struct.
    pub offset: usize,
    pub size: usize,
}

#[derive(Copy, Clone, Debug)]
pub struct LazyLayout {
    pub overall: Layout,
    pub value_offset: usize,
    #[expect(unused)]
    pub flag_offset: usize,
}

impl LazyLayout {
    pub fn new(value_layout: Layout) -> Self {
        let (overall, flag_offset) = value_layout.extend(Layout::new::<u8>()).unwrap();
        Self {
            overall,
            value_offset: 0,
            flag_offset,
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct FuncLayout {
    pub overall: Layout,
    #[expect(unused)]
    pub fnptr_offset: usize,
    pub captures_offset: usize,
}

impl FuncLayout {
    pub fn new() -> Self {
        let fnptr_layout = Layout::new::<Func>();
        let (overall, captures_offset) = fnptr_layout.extend(Layout::new::<MRef>()).unwrap();
        Self {
            overall,
            fnptr_offset: 0,
            captures_offset,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncType {
    pub param_types: Vec<Type>,
    pub return_type: Type,
}
