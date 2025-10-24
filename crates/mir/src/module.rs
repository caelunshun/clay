use crate::instr::InstrData;
use compact_str::CompactString;
use cranelift_entity::{EntityList, EntitySet, ListPool, PrimaryMap, SecondaryMap};
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
    adts: PrimaryMap<AlgebraicTypeRef, Option<AlgebraicType<'db>>>,
    funcs: PrimaryMap<FuncRef, Option<Func<'db>>>,
    /// A function header can be known before
    /// the function body. This allows resolving
    /// recursive or mutually recursive functions.
    func_headers: SecondaryMap<FuncRef, Option<FuncHeader>>,
}

impl<'db> ContextBuilder<'db> {
    pub fn new(_db: &'db dyn Database) -> Self {
        Self {
            adts: Default::default(),
            funcs: Default::default(),
            func_headers: Default::default(),
        }
    }

    /// Creates a `AlgebraicTypeRef` without binding the corresponding
    /// type data. It must be bound before finalization
    /// or a panic will occur.
    pub fn alloc_adt(&mut self) -> AlgebraicTypeRef {
        self.adts.push(None)
    }

    /// Binds the value of an ADT.
    pub fn bind_adt(
        &mut self,
        _db: &'db dyn Database,
        type_ref: AlgebraicTypeRef,
        typ: AlgebraicType<'db>,
    ) {
        assert!(self.adts[type_ref].is_none(), "type bound twice");
        self.adts[type_ref] = Some(typ);
    }

    pub fn resolve_adt(&self, r: AlgebraicTypeRef) -> AlgebraicType<'db> {
        self.adts[r].expect("attempted to resolve unbound ADT")
    }

    pub fn alloc_func(&mut self) -> FuncRef {
        self.funcs.push(None)
    }

    pub fn bind_func_header(&mut self, func_ref: FuncRef, header: FuncHeader) {
        self.func_headers[func_ref] = Some(header);
    }

    pub fn bind_func(&mut self, func_ref: FuncRef, func: Func<'db>) {
        assert!(self.funcs[func_ref].is_none(), "func bound twice");
        self.funcs[func_ref] = Some(func);
    }

    pub fn resolve_func(&self, r: FuncRef) -> Func<'db> {
        self.funcs[r].expect("attempted to resolve unbound func")
    }

    pub fn resolve_func_header(&self, db: &'db dyn Database, r: FuncRef) -> &FuncHeader {
        self.funcs[r]
            .as_ref()
            .map(|f| &f.data(db).header)
            .unwrap_or_else(|| {
                self.func_headers[r].as_ref().expect(
                    "attempted to resolve header of a func whose header is not yet resolved",
                )
            })
    }

    pub fn finish(self) -> ContextData<'db> {
        let mut adts = PrimaryMap::new();
        let mut funcs = PrimaryMap::new();
        for (type_ref, typ) in self.adts {
            assert_eq!(
                adts.push(typ.expect("type not bound before finalization")),
                type_ref
            );
        }
        for (func_ref, func) in self.funcs {
            assert_eq!(
                funcs.push(func.expect("func not bound before finalization")),
                func_ref
            );
        }

        ContextData { adts, funcs }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, salsa::Update)]
pub struct ContextData<'db> {
    pub adts: PrimaryMap<AlgebraicTypeRef, AlgebraicType<'db>>,
    pub funcs: PrimaryMap<FuncRef, Func<'db>>,
}

entity_ref! {
    /// ID of a type within the same mir `Context`.
    /// Enables circular references (e.g. struct with
    /// a reference to itself, as seen in a linked list)
    pub struct TypeRef;
}

entity_ref! {
    pub struct AlgebraicTypeRef;
}

impl AlgebraicTypeRef {
    pub fn resolve<'db>(&self, db: &'db dyn Database, cx: Context<'db>) -> AlgebraicType<'db> {
        /// Wrapping this in a salsa::tracked
        /// function allows salsa to avoid
        /// recalculating a query when the returned
        /// Type doesn't change, even if the Context
        /// was partially updated.
        #[salsa::tracked]
        fn resolve_helper<'db>(
            db: &'db dyn Database,
            cx: Context<'db>,
            type_ref: AlgebraicTypeRef,
        ) -> AlgebraicType<'db> {
            cx.data(db).adts[type_ref]
        }

        resolve_helper(db, cx, *self)
    }

    pub fn resolve_in_builder<'db>(&self, cx: &ContextBuilder<'db>) -> AlgebraicType<'db> {
        cx.resolve_adt(*self)
    }

    pub fn data<'db>(&self, db: &'db dyn Database, cx: Context<'db>) -> &'db AlgebraicTypeData {
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

    pub fn resolve_header<'cx, 'db>(
        &self,
        db: &'db dyn Database,
        cx: &'cx ContextBuilder<'db>,
    ) -> &'cx FuncHeader {
        cx.resolve_func_header(db, *self)
    }

    pub fn data<'db>(&self, db: &'db dyn Database, cx: Context<'db>) -> &'db FuncData<'db> {
        self.resolve(db, cx).data(db)
    }
}

/// A type that can have generic parameters.
#[salsa::tracked(debug)]
pub struct AlgebraicType<'db> {
    #[returns(ref)]
    pub name: CompactString,
    #[tracked]
    #[returns(ref)]
    pub type_params: PrimaryMap<TypeParam, ()>,
    #[tracked]
    #[returns(ref)]
    pub data: AlgebraicTypeData,
}

entity_ref_16bit! {
    pub struct TypeParam;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub enum AlgebraicTypeData {
    Struct(StructTypeData),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub enum TypeKind {
    Prim(PrimType),
    /// Reference to an object managed by the garbage collector,
    /// or to a field of an object managed by the garbage collector,
    /// or to an element of a list.
    /// It has indefinite lifetime.
    MRef(Box<TypeKind>),
    Func(FuncTypeData),
    /// Dynamically resized array.
    List(Box<TypeKind>),
    Algebraic(AlgebraicTypeInstance),
    /// Generic type in the current scope.
    TypeParam(TypeParam),
    /// Only valid inside a trait definition.
    Self_,
}

impl TypeKind {
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

    pub fn map_inner_types(&self, mut map: impl FnMut(&TypeKind) -> TypeKind) -> Self {
        match self {
            TypeKind::Prim(_) | TypeKind::TypeParam(_) | TypeKind::Self_ => self.clone(),
            TypeKind::MRef(type_kind) => TypeKind::MRef(Box::new(map(type_kind))),
            TypeKind::Func(func_type_data) => TypeKind::Func(FuncTypeData {
                param_types: func_type_data.param_types.iter().map(&mut map).collect(),
                return_type: Box::new(map(&func_type_data.return_type)),
            }),
            TypeKind::List(type_kind) => TypeKind::List(Box::new(map(type_kind))),
            TypeKind::Algebraic(algebraic_type_instance) => {
                TypeKind::Algebraic(AlgebraicTypeInstance {
                    adt: algebraic_type_instance.adt,
                    type_args: Box::new(
                        algebraic_type_instance
                            .type_args
                            .iter()
                            .map(|(arg, ty)| {
                                if let Some(ty) = ty {
                                    (arg, Some(map(ty)))
                                } else {
                                    (arg, None)
                                }
                            })
                            .collect(),
                    ),
                })
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct AlgebraicTypeInstance {
    pub adt: AlgebraicTypeRef,
    pub type_args: Box<SecondaryMap<TypeParam, Option<TypeKind>>>,
}

impl AlgebraicTypeInstance {
    /// Substitute type arguments into type parameters.
    pub fn substitute_type_args(&self, typ: &TypeKind) -> TypeKind {
        match typ {
            TypeKind::TypeParam(p) => self.type_args[*p].clone().unwrap(),
            typ => typ.map_inner_types(|typ| self.substitute_type_args(typ)),
        }
    }
}

/// A closure object, consisting of a dynamic
/// function reference and a reference to an opaque
/// captures struct.
#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct FuncTypeData {
    pub param_types: Vec<TypeKind>,
    pub return_type: Box<TypeKind>,
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
    pub fields: PrimaryMap<Field, FieldData>,
}

entity_ref_16bit! {
    pub struct Field;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct FieldData {
    pub name: CompactString,
    pub typ: TypeKind,
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

/// The function header describes the signature
/// of the function but not its behavior.
#[derive(Debug, Clone, PartialEq, Hash, salsa::Update)]
pub struct FuncHeader {
    /// Used for debugging; may be synthetic
    /// in the case of anonymous functions.
    pub name: CompactString,
    /// Type used to store the captured variables
    /// for the function. A managed reference
    /// to the captures is the first argument
    /// to the entry block of the function.
    pub captures_type: TypeKind,
    /// Parameters expected by the function, not including the captures.
    pub param_types: Vec<TypeKind>,
    pub return_type: TypeKind,
}

#[derive(Debug, Clone, PartialEq, Hash, salsa::Update)]
pub struct FuncData<'db> {
    pub header: FuncHeader,
    /// Set of values used by the function. Values can be assigned
    /// multiple times until after the SSA lowering pass is applied.
    pub vals: PrimaryMap<Val, ValData>,

    /// Basic blocks in the function instruction stream.
    pub basic_blocks: PrimaryMap<BasicBlock, BasicBlockData<'db>>,
    /// Basic block where execution of this function starts.
    pub entry_block: BasicBlock,

    /// Pool of `Local` references used for lists
    /// of locals in `instrs`.
    pub val_lists: ListPool<Val>,
}

impl<'db> FuncData<'db> {
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
    pub typ: TypeKind,
    /// Optional name, for debugging and testing.
    pub name: Option<CompactString>,
}

entity_ref_16bit! {
    pub struct BasicBlock;
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, salsa::Update)]
pub struct BasicBlockData<'db> {
    /// Optional name, for debugging and testing.
    pub name: Option<CompactString>,
    pub instrs: Vec<InstrData<'db>>,
    /// Only used after SSA transformation; empty before then, except for
    /// the entry block, where the capture pointer followed by the function arguments are assigned
    /// here.
    pub params: EntityList<Val>,
}
