use crate::{engine::Module, ptr::MRef, Func};
use bytecode::{module::Field, ModuleData, PrimitiveType, Type};
use bytemuck::{Pod, Zeroable};
use cranelift_entity::{EntityRef, PrimaryMap, SecondaryMap};
use hashbrown::HashMap;
use parking_lot::{Once, OnceState};
use std::{alloc::Layout, cmp};
use fir_bytecode::entity_ref;

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
    pub module_mapping: SecondaryMap<Module, SecondaryMap<Type, Type>>,

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
    pub fn local_type_data(&self, module: Module, typ: Type) -> &TypeData {
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
                bytecode::TypeData::LazyReference(_) => {
                    let id = Type::new(next_id);
                    next_id += 2; // extra ID allocated for the Lazy type
                    id
                }
                _ => {
                    let id = Type::new(next_id);
                    next_id += 1;
                    id
                }
            };
            id_mapping[type_id] = mapped_id;
        }

        let mut structs_to_lay_out = Vec::new();
        let mut lazies_to_lay_out = Vec::new();

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
                bytecode::TypeData::LazyReference(l) => {
                    let lazy_type = self.types.push(TypeData {
                        kind: TypeKind::Lazy(LazyType {
                            value_type: id_mapping[l.inner_type],
                            layout: LazyLayout::placeholder(),
                        }),
                        local_ids: HashMap::new(),
                    });
                    lazies_to_lay_out.push(lazy_type);
                    self.types.push(TypeData {
                        kind: TypeKind::LazyReference(lazy_type),
                        local_ids: HashMap::new(),
                    })
                }
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

        for lazy_id in lazies_to_lay_out {
            let TypeKind::Lazy(lazy) = &mut self.types[lazy_id].kind else {
                unreachable!()
            };
            let value_layout = self.layouts[lazy.value_type].unwrap();
            lazy.layout = LazyLayout::new(value_layout);
        }

        for local_type_id in module.types.keys() {
            let type_id = id_mapping[local_type_id];
            self.layouts[type_id] = Some(self.types[type_id].kind.layout(self));
        }

        self.module_mapping[module_id] = id_mapping;
    }

    /// Traverses all references stored inline in the given type.
    pub unsafe fn traverse_references(
        &self,
        ptr: *const u8,
        typ: Type,
        mut callback: impl FnMut(MRef),
    ) {
        self.traverse_references_inner(ptr, typ, &mut callback)
    }

    unsafe fn traverse_references_inner(
        &self,
        ptr: *const u8,
        typ: Type,
        callback: &mut impl FnMut(MRef),
    ) {
        let type_data = &self.types[typ];
        match &type_data.kind {
            TypeKind::Struct(s) => {
                for field in s.fields.values() {
                    self.traverse_references_inner(
                        ptr.add(field.offset),
                        field.field_type,
                        callback,
                    );
                }
            }
            TypeKind::Primitive(_) => {}
            TypeKind::Reference(_) | TypeKind::LazyReference(_) => {
                callback(*ptr.cast::<MRef>());
            }
            TypeKind::Func(_) => callback((*ptr.cast::<FuncObject>()).captures),
            TypeKind::Lazy(lazy) => {
                let func_ptr = lazy.layout.get_initializer_func_ptr(ptr);
                callback(func_ptr.captures);

                let once = lazy.layout.get_once_ptr(ptr);
                if once.state() == OnceState::Done {
                    self.traverse_references_inner(
                        lazy.layout.get_value_ptr(ptr),
                        lazy.value_type,
                        callback,
                    );
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeData {
    pub kind: TypeKind,
    /// ID of the type within each module that uses it.
    pub local_ids: HashMap<Module, bytecode::Type>,
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
    LazyReference(Type),
    Lazy(LazyType),
    Func(FuncType),
}

impl TypeKind {
    pub fn layout(&self, _registry: &TypeRegistry) -> Layout {
        match self {
            TypeKind::Struct(s) => s.overall,
            TypeKind::Primitive(p) => match *p {
                PrimitiveType::Int => Layout::new::<i64>(),
                PrimitiveType::Real => Layout::new::<f64>(),
                PrimitiveType::Bool => Layout::new::<bool>(),
                PrimitiveType::Unit => Layout::new::<()>(),
            },
            TypeKind::Reference(_) | TypeKind::LazyReference(_) => Layout::new::<MRef>(),
            TypeKind::Lazy(l) => l.layout.overall,
            TypeKind::Func(_) => Layout::new::<FuncObject>(),
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
        id_mapping: &SecondaryMap<Type, Type>,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LazyType {
    pub value_type: Type,
    pub layout: LazyLayout,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct LazyLayout {
    pub overall: Layout,
    pub initializer_func_offset: usize,
    pub value_offset: usize,
    pub once_offset: usize,
}

impl LazyLayout {
    pub fn new(value_layout: Layout) -> Self {
        let (overall, initializer_func_offset) =
            value_layout.extend(Layout::new::<FuncObject>()).unwrap();
        let (overall, once_offset) = overall.extend(Layout::new::<Once>()).unwrap();

        Self {
            overall,
            value_offset: 0,
            initializer_func_offset,
            once_offset,
        }
    }

    /// Placeholder value used before layout initialization.
    pub fn placeholder() -> Self {
        Self {
            overall: Layout::new::<()>(),
            initializer_func_offset: 0,
            value_offset: 0,
            once_offset: 0,
        }
    }

    pub unsafe fn get_value_ptr(&self, p: *const u8) -> *const u8 {
        p.add(self.value_offset)
    }

    pub unsafe fn get_once_ptr(&self, p: *const u8) -> &Once {
        &*p.add(self.once_offset).cast()
    }

    pub unsafe fn get_initializer_func_ptr(&self, p: *const u8) -> &FuncObject {
        &*p.add(self.initializer_func_offset).cast()
    }
}

/// In-memory representation of a function object.
#[derive(Copy, Clone, Debug, Pod, Zeroable)]
// alignment of 16 ensures 128-bit atomics can be used
#[repr(C, align(16))]
pub struct FuncObject {
    /// Pointer to captures passed to the function.
    pub captures: MRef,
    /// Function implementation.
    pub func: Func,
    /// Unused; used to force 128-bit size so we atomically
    /// load/store a function object.
    pub padding: u32,
}

impl FuncObject {
    pub fn to_u128(self) -> u128 {
        u128::from_le_bytes(bytemuck::bytes_of(&self).try_into().unwrap())
    }

    pub fn from_u128(x: u128) -> Self {
        *bytemuck::from_bytes(&x.to_le_bytes())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncType {
    pub param_types: Vec<Type>,
    pub return_type: Type,
}
