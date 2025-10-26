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
    traits: PrimaryMap<TraitRef, Option<Trait<'db>>>,
    trait_impls: Vec<TraitImpl<'db>>,
    /// A function header can be known before
    /// the function body. This allows resolving
    /// recursive or mutually recursive functions.
    func_headers: SecondaryMap<FuncRef, Option<FuncHeader<'db>>>,
}

impl<'db> ContextBuilder<'db> {
    pub fn new(_db: &'db dyn Database) -> Self {
        Self {
            adts: Default::default(),
            funcs: Default::default(),
            func_headers: Default::default(),
            trait_impls: Vec::new(),
            traits: Default::default(),
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

    pub fn bind_func_header(&mut self, func_ref: FuncRef, header: FuncHeader<'db>) {
        self.func_headers[func_ref] = Some(header);
    }

    pub fn bind_func(&mut self, func_ref: FuncRef, func: Func<'db>) {
        assert!(self.funcs[func_ref].is_none(), "func bound twice");
        self.funcs[func_ref] = Some(func);
    }

    pub fn resolve_func(&self, r: FuncRef) -> Func<'db> {
        self.funcs[r].expect("attempted to resolve unbound func")
    }

    pub fn resolve_func_header(&self, db: &'db dyn Database, r: FuncRef) -> &FuncHeader<'db> {
        self.funcs[r]
            .as_ref()
            .map(|f| &f.data(db).header)
            .unwrap_or_else(|| {
                self.func_headers[r].as_ref().expect(
                    "attempted to resolve header of a func whose header is not yet resolved",
                )
            })
    }

    pub fn alloc_trait(&mut self) -> TraitRef {
        self.traits.push(None)
    }

    pub fn bind_trait(&mut self, ref_: TraitRef, trait_: Trait<'db>) {
        self.traits[ref_] = Some(trait_);
    }

    pub fn resolve_trait(&self, ref_: TraitRef) -> Trait<'db> {
        self.traits[ref_].expect("attempted to resolve unbound trait")
    }

    pub fn add_trait_impl(&mut self, trait_impl: TraitImpl<'db>) {
        self.trait_impls.push(trait_impl);
    }

    pub fn finish(self) -> ContextData<'db> {
        let mut adts = PrimaryMap::new();
        let mut funcs = PrimaryMap::new();
        let mut traits = PrimaryMap::new();
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
        for (trait_ref, trait_) in self.traits {
            assert_eq!(
                traits.push(trait_.expect("trait not bound before finalization")),
                trait_ref
            );
        }

        ContextData {
            adts,
            funcs,
            traits,
            trait_impls: self.trait_impls,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, salsa::Update)]
pub struct ContextData<'db> {
    pub adts: PrimaryMap<AlgebraicTypeRef, AlgebraicType<'db>>,
    pub funcs: PrimaryMap<FuncRef, Func<'db>>,
    pub traits: PrimaryMap<TraitRef, Trait<'db>>,
    pub trait_impls: Vec<TraitImpl<'db>>,
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

    pub fn data<'db>(
        &self,
        db: &'db dyn Database,
        cx: Context<'db>,
    ) -> &'db AlgebraicTypeData<'db> {
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
    ) -> &'cx FuncHeader<'db> {
        cx.resolve_func_header(db, *self)
    }

    pub fn data<'db>(&self, db: &'db dyn Database, cx: Context<'db>) -> &'db FuncData<'db> {
        self.resolve(db, cx).data(db)
    }
}

entity_ref! {
    /// ID of a trait within the same mir `Context`.
    /// Enables circular references among traits.
    pub struct TraitRef;
}

impl TraitRef {
    pub fn resolve<'db>(&self, db: &'db dyn Database, cx: Context<'db>) -> Trait<'db> {
        /// Wrapping this in a salsa::tracked
        /// function allows salsa to avoid
        /// recalculating a query when the returned
        /// Trait doesn't change, even if the Context
        /// was partially updated.
        #[salsa::tracked]
        fn resolve_helper<'db>(
            db: &'db dyn Database,
            cx: Context<'db>,
            trait_ref: TraitRef,
        ) -> Trait<'db> {
            cx.data(db).traits[trait_ref]
        }

        resolve_helper(db, cx, *self)
    }
}

#[salsa::tracked(debug)]
pub struct Trait<'db> {
    #[returns(ref)]
    #[tracked]
    pub data: TraitData<'db>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct TraitData<'db> {
    pub name: CompactString,
    pub type_params: PrimaryMap<TypeParam, TypeParamData<'db>>,
    pub assoc_funcs: PrimaryMap<AssocFunc, AssocFuncData<'db>>,
}

entity_ref_16bit! {
    pub struct AssocFunc;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct AssocFuncData<'db> {
    pub name: CompactString,
    pub param_types: Vec<Type<'db>>,
    pub return_type: Type<'db>,
}

/// A type that can have generic parameters.
#[salsa::tracked(debug)]
pub struct AlgebraicType<'db> {
    #[returns(ref)]
    pub name: CompactString,
    #[tracked]
    #[returns(ref)]
    pub type_params: PrimaryMap<TypeParam, TypeParamData<'db>>,
    #[tracked]
    #[returns(ref)]
    pub data: AlgebraicTypeData<'db>,
}

entity_ref_16bit! {
    pub struct TypeParam;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct TypeParamData<'db> {
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
}

#[salsa::interned(debug)]
pub struct TraitInstance<'db> {
    pub trait_: TraitRef,
    #[returns(ref)]
    pub type_args: SecondaryMap<TypeParam, Option<TypeKind<'db>>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub enum AlgebraicTypeData<'db> {
    Struct(StructTypeData<'db>),
}

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

#[salsa::tracked(debug)]
pub struct TraitImpl<'db> {
    #[returns(ref)]
    #[tracked]
    pub data: TraitImplData<'db>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct TraitImplData<'db> {
    pub type_params: PrimaryMap<TypeParam, TypeParamData<'db>>,
    /// Note: can refer to a type parameter....
    pub impl_for_type: Type<'db>,
    pub trait_: TraitInstance<'db>,
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
    TypeParam(TypeParam),
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct AlgebraicTypeInstance<'db> {
    pub adt: AlgebraicTypeRef,
    pub type_args: SecondaryMap<TypeParam, Option<Type<'db>>>,
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

/// A closure object, consisting of a dynamic
/// function reference and a reference to an opaque
/// captures struct.
#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct FuncTypeData<'db> {
    pub param_types: Vec<Type<'db>>,
    pub return_type: Type<'db>,
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
pub struct StructTypeData<'db> {
    pub fields: PrimaryMap<Field, FieldData<'db>>,
}

entity_ref_16bit! {
    pub struct Field;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct FieldData<'db> {
    pub name: CompactString,
    pub typ: Type<'db>,
}

#[salsa::tracked(debug)]
pub struct Constant<'db> {
    #[returns(ref)]
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
    pub fn typ(&self) -> TypeKind<'static> {
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
pub struct FuncHeader<'db> {
    /// Used for debugging; may be synthetic
    /// in the case of anonymous functions.
    pub name: CompactString,
    /// Type used to store the captured variables
    /// for the function. A managed reference
    /// to the captures is the first argument
    /// to the entry block of the function.
    pub captures_type: Type<'db>,
    /// Parameters expected by the function, not including the captures.
    pub param_types: Vec<Type<'db>>,
    pub return_type: Type<'db>,
    pub type_params: PrimaryMap<TypeParam, TypeParamData<'db>>,
}

#[derive(Debug, Clone, PartialEq, Hash, salsa::Update)]
pub struct FuncData<'db> {
    pub header: FuncHeader<'db>,
    /// Set of values used by the function. Values can be assigned
    /// multiple times until after the SSA lowering pass is applied.
    pub vals: PrimaryMap<Val, ValData<'db>>,

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
pub struct ValData<'db> {
    /// Type of the local.
    pub typ: Type<'db>,
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

#[salsa::interned(debug)]
pub struct FuncInstance<'db> {
    pub func: MaybeAssocFunc<'db>,
    pub type_args: SecondaryMap<TypeParam, Option<Type<'db>>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub enum MaybeAssocFunc<'db> {
    Func(FuncRef),
    AssocFunc {
        trait_: TraitRef,
        typ: Type<'db>,
        assoc_func: AssocFunc,
    },
}
