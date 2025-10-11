use crate::instr::InstrData;
use compact_str::CompactString;
use cranelift_entity::{EntityList, EntitySet, ListPool, PrimaryMap, SecondaryMap};
use salsa::Database;
use std::{
    hash::{Hash, Hasher},
    mem,
};

#[salsa::tracked(debug)]
pub struct Type<'db> {
    #[returns(ref)]
    pub data: TypeData<'db>,
}

#[salsa::tracked(debug)]
struct TypeDataWrapper<'db> {
    data: TypeData<'db>,
}

/// Helper that ensures equal types are assigned equal Type<'db> identifiers.
/// Essentially a manual implementation of interning, since salsa interned
/// structs don't seem to support references to other salsa structs.
pub fn memoized_type<'db>(db: &'db dyn Database, data: TypeData<'db>) -> Type<'db> {
    #[salsa::tracked]
    fn memoized_type_helper<'db>(db: &'db dyn Database, data: TypeDataWrapper<'db>) -> Type<'db> {
        Type::new(db, data.data(db))
    }

    memoized_type_helper(db, TypeDataWrapper::new(db, data))
}

#[salsa::tracked]
pub fn int_type<'db>(db: &'db dyn Database) -> Type<'db> {
    memoized_type(db, TypeData::Prim(PrimType::Int))
}

#[salsa::tracked]
pub fn real_type<'db>(db: &'db dyn Database) -> Type<'db> {
    memoized_type(db, TypeData::Prim(PrimType::Real))
}

pub fn byte_type<'db>(db: &'db dyn Database) -> Type<'db> {
    memoized_type(db, TypeData::Prim(PrimType::Byte))
}

pub fn bool_type<'db>(db: &'db dyn Database) -> Type<'db> {
    memoized_type(db, TypeData::Prim(PrimType::Bool))
}

pub fn str_type<'db>(db: &'db dyn Database) -> Type<'db> {
    memoized_type(db, TypeData::Prim(PrimType::Str))
}

pub fn unit_type<'db>(db: &'db dyn Database) -> Type<'db> {
    memoized_type(db, TypeData::Prim(PrimType::Unit))
}

pub fn list_type<'db>(db: &'db dyn Database, element_type: Type<'db>) -> Type<'db> {
    memoized_type(db, TypeData::List(element_type))
}

pub fn mref_type<'db>(db: &'db dyn Database, pointee_type: Type<'db>) -> Type<'db> {
    memoized_type(db, TypeData::MRef(pointee_type))
}

pub fn eref_type<'db>(db: &'db dyn Database, pointee_type: Type<'db>) -> Type<'db> {
    memoized_type(db, TypeData::ERef(pointee_type))
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub enum TypeData<'db> {
    Prim(PrimType),
    /// Reference to an object managed by the garbage collector.
    /// It has indefinite lifetime.
    MRef(Type<'db>),
    /// Ephemeral reference to one of:
    /// 1. An object managed by the garbage collector.
    /// 2. A field of a struct anywhere in memory.
    /// 3. A local that has been promoted to a reference.
    ///
    /// Its lifetime is constrained. ERefs cannot be stored
    /// in struct fields or globals.
    ERef(Type<'db>),
    Func(FuncTypeData<'db>),
    Struct(StructTypeData<'db>),
    /// Dynamically resized array.
    List(Type<'db>),
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
    pub name: CompactString,
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
    pub fn typ(&self) -> TypeData<'static> {
        match self {
            ConstantData::Int(_) => TypeData::Prim(PrimType::Int),
            ConstantData::Real(_) => TypeData::Prim(PrimType::Real),
            ConstantData::Bool(_) => TypeData::Prim(PrimType::Bool),
            ConstantData::Str(_) => TypeData::Prim(PrimType::Str),
        }
    }
}

/*
/// ID of a module import; a reference
/// to another module.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ImportedModule(u32);
entity_impl!(ImportedModule);

#[derive(Debug, Clone)]
pub struct ImportedModuleData {
    pub type_imports: PrimaryMap<ImportedType, ImportedTypeData>,
}

/// ID assigned to each unique imported type from a module.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ImportedType(u32);
entity_impl!(ImportedType);

#[derive(Debug, Clone)]
pub struct ImportedTypeData {
    /// Name of the type to import.
    pub name: CompactString,
}
 */

#[salsa::tracked(debug)]
pub struct Func<'db> {
    #[returns(ref)]
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
    pub captures_type: Type<'db>,
    /// Set of values used by the function. Values can be assigned
    /// multiple times until after the SSA lowering pass is applied.
    pub vals: PrimaryMap<Val, ValData<'db>>,
    /// Parameters expected by the function, not including the captures.
    pub param_types: Vec<Type<'db>>,
    pub return_type: Type<'db>,
    /// Basic blocks in the function instruction stream.
    pub basic_blocks: PrimaryMap<BasicBlock, BasicBlockData<'db>>,
    /// Basic block where execution of this function starts.
    pub entry_block: BasicBlock,

    /// Pool of `Local` references used for lists
    /// of locals in `instrs`.
    pub val_lists: ListPool<Val>,
}

impl FuncData<'_> {
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
}

impl<'db> ValData<'db> {
    pub fn new(typ: Type<'db>) -> Self {
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

#[cfg(test)]
mod tests {
    use super::*;
    use zyon_core::Db;

    #[test]
    fn types_are_memoized() {
        let db = Db::default();
        let t0 = int_type(&db);
        let t1 = int_type(&db);
        assert_eq!(t0, t1);
    }
}
