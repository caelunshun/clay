use crate::instr::InstrData;
use compact_str::CompactString;
use cranelift_entity::{EntityList, EntitySet, ListPool, PrimaryMap, SecondaryMap};
use indexmap::IndexMap;
use salsa::Database;
use std::{
    hash::{Hash, Hasher},
    mem,
};

/// An mir context is a collection of functions and types
/// that can refer to each other.
#[salsa::tracked]
pub struct Context<'db> {
    #[returns(ref)]
    #[tracked]
    pub data: ContextData<'db>,
}

/// Builder for `ContextData` that allows
/// lazy initialization of each type and function.
#[derive(Debug, Clone)]
pub struct ContextBuilder<'db> {
    types: PrimaryMap<TypeRef, Option<Type<'db>>>,
    types_by_data: IndexMap<TypeKind, TypeRef, hashbrown::DefaultHashBuilder>,
    funcs: PrimaryMap<FuncRef, Option<Func<'db>>>,
}

impl<'db> ContextBuilder<'db> {
    pub fn new(db: &'db dyn Database) -> Self {
        let mut cx = Self {
            types: Default::default(),
            types_by_data: Default::default(),
            funcs: Default::default(),
        };
        for prim in [
            PrimType::Int,
            PrimType::Bool,
            PrimType::Real,
            PrimType::Byte,
            PrimType::Str,
            PrimType::Unit,
        ] {
            cx.get_or_create_type_ref_with_data(db, TypeKind::Prim(prim));
        }
        cx
    }

    pub fn prim_type_ref(&self, prim: PrimType) -> TypeRef {
        self.types_by_data[&TypeKind::Prim(prim)]
    }

    pub fn int_type_ref(&self) -> TypeRef {
        self.prim_type_ref(PrimType::Int)
    }

    pub fn bool_type_ref(&self) -> TypeRef {
        self.prim_type_ref(PrimType::Bool)
    }

    pub fn real_type_ref(&self) -> TypeRef {
        self.prim_type_ref(PrimType::Real)
    }

    pub fn byte_type_ref(&self) -> TypeRef {
        self.prim_type_ref(PrimType::Byte)
    }

    pub fn str_type_ref(&self) -> TypeRef {
        self.prim_type_ref(PrimType::Str)
    }

    pub fn unit_type_ref(&self) -> TypeRef {
        self.prim_type_ref(PrimType::Unit)
    }

    /// Creates a `TypeRef` without binding the corresponding
    /// type data. It must be bound before finalization
    /// or a panic will occur.
    pub fn alloc_type(&mut self) -> TypeRef {
        self.types.push(None)
    }

    /// Binds the value of a type.
    pub fn bind_type(&mut self, db: &'db dyn Database, type_ref: TypeRef, typ: Type<'db>) {
        assert!(self.types[type_ref].is_none(), "type bound twice");
        self.types[type_ref] = Some(typ);
        self.types_by_data.insert(typ.data(db).clone(), type_ref);
    }

    pub fn resolve_type(&self, r: TypeRef) -> Type<'db> {
        self.types[r].expect("attempted to resolve unbound type")
    }

    pub fn get_or_create_type_ref(&mut self, db: &'db dyn Database, typ: Type<'db>) -> TypeRef {
        *self
            .types_by_data
            .entry(typ.data(db).clone())
            .or_insert_with(|| self.types.push(Some(typ)))
    }

    pub fn get_or_create_type_ref_with_data(
        &mut self,
        db: &'db dyn Database,
        typ: TypeKind,
    ) -> TypeRef {
        self.get_or_create_type_ref(db, Type::new(db, typ))
    }

    pub fn alloc_func(&mut self) -> FuncRef {
        self.funcs.push(None)
    }

    pub fn bind_func(&mut self, func_ref: FuncRef, func: Func<'db>) {
        assert!(self.funcs[func_ref].is_none(), "func bound twice");
        self.funcs[func_ref] = Some(func);
    }

    pub fn resolve_func(&self, r: FuncRef) -> Func<'db> {
        self.funcs[r].expect("attempted to resolve unbound func")
    }

    pub fn finish(self) -> ContextData<'db> {
        let mut types = PrimaryMap::new();
        let mut funcs = PrimaryMap::new();
        for (type_ref, typ) in self.types {
            assert_eq!(
                types.push(typ.expect("type not bound before finalization")),
                type_ref
            );
        }
        for (func_ref, func) in self.funcs {
            assert_eq!(
                funcs.push(func.expect("func not bound before finalization")),
                func_ref
            );
        }

        ContextData {
            types,
            funcs,
            types_by_data: self.types_by_data,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, salsa::Update)]
pub struct ContextData<'db> {
    pub types: PrimaryMap<TypeRef, Type<'db>>,
    /// Maps TypeData
    /// to the unique TypeRef for that TypeData.
    /// If a TypeData does not appear in this map
    /// then it is not referenced anywhere
    /// in this context.
    ///
    /// Note that to simplify some code, all primitive types are always defined
    /// here.
    pub types_by_data: IndexMap<TypeKind, TypeRef, hashbrown::DefaultHashBuilder>,
    pub funcs: PrimaryMap<FuncRef, Func<'db>>,
}

impl<'db> ContextData<'db> {
    pub fn prim_type_ref(&self, prim: PrimType) -> TypeRef {
        self.types_by_data[&TypeKind::Prim(prim)]
    }

    pub fn int_type_ref(&self) -> TypeRef {
        self.prim_type_ref(PrimType::Int)
    }

    pub fn bool_type_ref(&self) -> TypeRef {
        self.prim_type_ref(PrimType::Bool)
    }

    pub fn real_type_ref(&self) -> TypeRef {
        self.prim_type_ref(PrimType::Real)
    }

    pub fn byte_type_ref(&self) -> TypeRef {
        self.prim_type_ref(PrimType::Byte)
    }

    pub fn str_type_ref(&self) -> TypeRef {
        self.prim_type_ref(PrimType::Str)
    }

    pub fn unit_type_ref(&self) -> TypeRef {
        self.prim_type_ref(PrimType::Unit)
    }
}

entity_ref! {
    /// ID of a type within the same mir `Context`.
    /// Enables circular references (e.g. struct with
    /// a reference to itself, as seen in a linked list)
    pub struct TypeRef;
}

impl TypeRef {
    /// Gets the type ref corresponding to the given
    /// type data in the given context, or `None`
    /// if the type does not exist in the context.
    pub fn of(db: &dyn Database, data: TypeKind, cx: &Context) -> Option<Self> {
        cx.data(db).types_by_data.get(&data).copied()
    }

    /// Equivalent to `Self::of` but inserts a new type
    /// into the context if it does not exist.
    pub fn create<'db>(
        db: &'db dyn Database,
        data: TypeKind,
        cx: &mut ContextBuilder<'db>,
    ) -> Self {
        cx.get_or_create_type_ref_with_data(db, data)
    }

    pub fn resolve<'db>(&self, db: &'db dyn Database, cx: Context<'db>) -> Type<'db> {
        /// Wrapping this in a salsa::tracked
        /// function allows salsa to avoid
        /// recalculating a query when the returned
        /// Type doesn't change, even if the Context
        /// was partially updated.
        #[salsa::tracked]
        fn resolve_helper<'db>(
            db: &'db dyn Database,
            cx: Context<'db>,
            type_ref: TypeRef,
        ) -> Type<'db> {
            cx.data(db).types[type_ref]
        }

        resolve_helper(db, cx, *self)
    }

    pub fn resolve_in_builder<'db>(&self, cx: &ContextBuilder<'db>) -> Type<'db> {
        cx.resolve_type(*self)
    }

    pub fn data<'db>(&self, db: &'db dyn Database, cx: Context<'db>) -> &'db TypeKind {
        self.resolve(db, cx).data(db)
    }
}

entity_ref! {
    /// ID of a function within the same mir `Context`.
    /// Enables circular references (e.g. recursion or mutual
    /// recursion).
    pub struct FuncRef;
}

impl FuncRef {
    pub fn create<'db>(
        db: &'db dyn Database,
        func: FuncData<'db>,
        cx: &mut ContextBuilder<'db>,
    ) -> Self {
        let this = cx.alloc_func();
        cx.bind_func(this, Func::new(db, func));
        this
    }

    pub fn resolve<'db>(&self, db: &'db dyn Database, cx: Context<'db>) -> Func<'db> {
        /// Wrapping this in a salsa::tracked
        /// function allows salsa to avoid
        /// recalculating a query when the returned
        /// Func doesn't change, even if the Context
        /// was partially updated.
        #[salsa::tracked]
        fn resolve_helper<'db>(
            db: &'db dyn Database,
            cx: Context<'db>,
            func_ref: FuncRef,
        ) -> Func<'db> {
            cx.data(db).funcs[func_ref]
        }

        resolve_helper(db, cx, *self)
    }

    pub fn resolve_in_builder<'db>(&self, cx: &ContextBuilder<'db>) -> Func<'db> {
        cx.resolve_func(*self)
    }

    pub fn data<'db>(&self, db: &'db dyn Database, cx: Context<'db>) -> &'db FuncData<'db> {
        self.resolve(db, cx).data(db)
    }
}

#[salsa::interned(debug)]
pub struct Type<'db> {
    #[returns(ref)]
    pub data: TypeKind,
}

#[salsa::tracked(debug)]
struct TypeDataWrapper<'db> {
    data: TypeKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub enum TypeKind {
    Prim(PrimType),
    /// Reference to an object managed by the garbage collector.
    /// It has indefinite lifetime.
    MRef(TypeRef),
    /// Ephemeral reference to one of:
    /// 1. An object managed by the garbage collector.
    /// 2. A field of a struct anywhere in memory.
    /// 3. A local that has been promoted to a reference.
    ///
    /// Its lifetime is constrained. ERefs cannot be stored
    /// in struct fields or globals.
    ERef(TypeRef),
    Func(FuncTypeData),
    Struct(StructTypeData),
    /// Dynamically resized array.
    List(TypeRef),
}

impl TypeKind {
    ///  Visits any types referenced / depended on by
    /// this type. Is not recursive.
    pub fn visit_used_types(&self, visit: &mut impl FnMut(TypeRef)) {
        match self {
            TypeKind::Prim(_) => {}
            TypeKind::MRef(t) | TypeKind::ERef(t) => {
                visit(*t);
            }
            TypeKind::Func(func) => {
                visit(func.return_type);
                for param in &func.param_types {
                    visit(*param);
                }
            }
            TypeKind::Struct(s) => {
                for (_, field) in &s.fields {
                    visit(field.typ);
                }
            }
            TypeKind::List(el) => {
                visit(*el);
            }
        }
    }
}

/// A closure object, consisting of a dynamic
/// function reference and a reference to an opaque
/// captures struct.
#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct FuncTypeData {
    pub param_types: Vec<TypeRef>,
    pub return_type: TypeRef,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct StructTypeData {
    pub name: CompactString,
    pub fields: PrimaryMap<Field, FieldData>,
}

entity_ref_16bit! {
    pub struct Field;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct FieldData {
    pub name: CompactString,
    pub typ: TypeRef,
}

#[salsa::tracked(debug)]
pub struct Constant<'db> {
    pub data: ConstantData,
}

#[derive(Clone, Debug)]
pub enum ConstantData {
    Int(i64),
    Real(f64),
    Bool(bool),
    Str(CompactString),
}

/// Special PartialEq that compares floats
/// with bitwise equality.
impl PartialEq for ConstantData {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ConstantData::Int(a), ConstantData::Int(b)) => a == b,
            (ConstantData::Real(a), ConstantData::Real(b)) => a.to_bits() == b.to_bits(),
            (ConstantData::Bool(a), ConstantData::Bool(b)) => a == b,
            (ConstantData::Str(a), ConstantData::Str(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for ConstantData {}

impl Hash for ConstantData {
    fn hash<H: Hasher>(&self, state: &mut H) {
        mem::discriminant(self).hash(state);
        match self {
            ConstantData::Int(x) => x.hash(state),
            ConstantData::Real(x) => x.to_bits().hash(state),
            ConstantData::Bool(x) => x.hash(state),
            ConstantData::Str(x) => x.hash(state),
        }
    }
}

impl ConstantData {
    pub fn typ(&self) -> TypeKind {
        match self {
            ConstantData::Int(_) => TypeKind::Prim(PrimType::Int),
            ConstantData::Real(_) => TypeKind::Prim(PrimType::Real),
            ConstantData::Bool(_) => TypeKind::Prim(PrimType::Bool),
            ConstantData::Str(_) => TypeKind::Prim(PrimType::Str),
        }
    }
}

#[salsa::tracked(debug)]
pub struct Func<'db> {
    #[returns(ref)]
    #[tracked]
    pub data: FuncData<'db>,
}

#[derive(Debug, Clone, PartialEq, Hash, salsa::Update)]
pub struct FuncData<'db> {
    /// Used for debugging; may be synthetic
    /// in the case of anonymous functions.
    pub name: CompactString,
    /// Type used to store the captured variables
    /// for the function. A managed reference
    /// to the captures is the first argument
    /// to the entry block of the function.
    pub captures_type: TypeRef,
    /// Set of values used by the function. Values can be assigned
    /// multiple times until after the SSA lowering pass is applied.
    pub vals: PrimaryMap<Val, ValData>,
    /// Parameters expected by the function, not including the captures.
    pub param_types: Vec<TypeRef>,
    pub return_type: TypeRef,
    /// Basic blocks in the function instruction stream.
    pub basic_blocks: PrimaryMap<BasicBlock, BasicBlockData<'db>>,
    /// Basic block where execution of this function starts.
    pub entry_block: BasicBlock,

    /// Pool of `Local` references used for lists
    /// of locals in `instrs`.
    pub val_lists: ListPool<Val>,
}

impl<'db> FuncData<'db> {
    /// Visits all types used in the function.
    /// May visit the same type multiple times.
    pub fn visit_types(&self, mut visit: impl FnMut(TypeRef)) {
        visit(self.captures_type);
        visit(self.return_type);
        for &param in &self.param_types {
            visit(param);
        }
        for (_, val_data) in &self.vals {
            visit(val_data.typ);
        }
    }

    /// Visits all basic blocks in an order such that
    /// a block B is not visited until after all blocks that
    /// appear in any *path* (not a walk) from the entry block to B (exclusive)
    /// are visited.
    pub fn visit_basic_blocks_topological(&self, mut visit: impl FnMut(BasicBlock)) {
        let acyclic_ancestors = self.compute_acyclic_ancestors();

        let mut stack = vec![self.entry_block];
        let mut visited = EntitySet::<BasicBlock>::new();
        while let Some(current) = stack.pop() {
            visit(current);
            visited.insert(current);

            self.visit_block_successors(current, |suc| {
                if !visited.contains(suc)
                    && acyclic_ancestors[suc]
                        .iter()
                        .all(|anc| visited.contains(anc))
                {
                    stack.push(suc);
                }
            });
        }
    }

    /// Computes the set of blocks reachable by paths
    /// (not walks) from the entry block to each block
    /// (excluding the destination block).
    pub fn compute_acyclic_ancestors(&self) -> SecondaryMap<BasicBlock, EntitySet<BasicBlock>> {
        // For each block, calculate blocks that appear in a path from the entry block
        let mut acyclic_ancestors: SecondaryMap<BasicBlock, EntitySet<BasicBlock>> =
            Default::default();

        let mut stack = vec![(self.entry_block, EntitySet::<BasicBlock>::new())];
        while let Some((current_block, mut current_path)) = stack.pop() {
            for ancestor in current_path.iter() {
                acyclic_ancestors[current_block].insert(ancestor);
            }
            current_path.insert(current_block);
            self.visit_block_successors(current_block, |suc| {
                if !current_path.contains(suc) {
                    stack.push((suc, current_path.clone()));
                }
            });
        }

        acyclic_ancestors
    }

    /// Computes the set of paths from the entry block
    /// to each block. These paths do not include
    /// the destination blocks.
    pub fn compute_paths_from_entry(&self) -> SecondaryMap<BasicBlock, Vec<EntitySet<BasicBlock>>> {
        let mut paths: SecondaryMap<BasicBlock, Vec<EntitySet<BasicBlock>>> = SecondaryMap::new();

        let mut stack = vec![(self.entry_block, EntitySet::<BasicBlock>::new())];
        while let Some((current_block, mut current_path)) = stack.pop() {
            paths[current_block].push(current_path.clone());
            current_path.insert(current_block);
            self.visit_block_successors(current_block, |suc| {
                if !current_path.contains(suc) {
                    stack.push((suc, current_path.clone()));
                }
            });
        }

        paths
    }

    pub fn is_block_edge(&self, a: BasicBlock, b: BasicBlock) -> bool {
        let mut is_edge = false;
        self.visit_block_successors(a, |b2| {
            if b2 == b {
                is_edge = true;
            }
        });
        is_edge
    }

    pub fn visit_block_successors(&self, block: BasicBlock, visit: impl FnMut(BasicBlock)) {
        self.basic_blocks[block]
            .instrs
            .last()
            .unwrap()
            .visit_successors(visit)
    }

    pub fn visit_block_predecessors(&self, block: BasicBlock, mut visit: impl FnMut(BasicBlock)) {
        self.basic_blocks.keys().for_each(|block2| {
            let mut is_predecessor = false;
            self.visit_block_successors(block2, |b| {
                if b == block {
                    is_predecessor = true;
                }
            });
            if is_predecessor {
                visit(block2);
            }
        })
    }
}

entity_ref_16bit! {
    pub struct Val;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct ValData {
    /// Type of the local.
    pub typ: TypeRef,
}

impl ValData {
    pub fn new(typ: TypeRef) -> Self {
        Self { typ }
    }
}

entity_ref_16bit! {
    pub struct BasicBlock;
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, salsa::Update)]
pub struct BasicBlockData<'db> {
    pub instrs: Vec<InstrData<'db>>,
    /// Only used after SSA transformation; empty before then, except for
    /// the entry block, where the capture pointer followed by the function arguments are assigned
    /// here.
    pub params: EntityList<Val>,
}
