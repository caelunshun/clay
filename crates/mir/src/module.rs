use crate::instr::InstrData;
use compact_str::CompactString;
use cranelift_entity::{EntityList, EntitySet, ListPool, PrimaryMap, SecondaryMap};
use hashbrown::HashSet;

#[derive(Debug, Clone, Default)]
pub struct ModuleData {
    pub types: PrimaryMap<Type, TypeData>,
    pub funcs: PrimaryMap<Func, FuncData>,
    pub constants: PrimaryMap<Constant, ConstantData>,
    // pub imported_modules: PrimaryMap<ImportedModule, ImportedModuleData>,
}

impl ModuleData {
    pub fn constant(&mut self, c: ConstantData) -> Constant {
        if let Some((id, _)) = self.constants.iter().find(|(_, val)| **val == c) {
            id
        } else {
            self.constants.push(c)
        }
    }

    pub fn typ(&mut self, t: TypeData) -> Type {
        if let Some((id, _)) = self.types.iter().find(|(_, val)| *val == &t) {
            id
        } else {
            self.types.push(t)
        }
    }
}

entity_ref_16bit! {
    /// ID of a type used in a module.
    pub struct Type;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeData {
    Prim(PrimType),
    /// Reference to an object managed by the garbage collector.
    /// It has indefinite lifetime.
    MRef(Type),
    /// Manages reference to another type,
    /// with lazily initialized value.
    /// It is a fat pointer that includes a function
    /// object used to initialize.
    LazyMRef(Type),
    /// Ephemeral reference to one of:
    /// 1. An object managed by the garbage collector.
    /// 2. A field of a struct anywhere in memory.
    /// 3. A local that has been promoted to a reference.
    /// Its lifetime is constrained. ERefs cannot be stored
    /// in struct fields or globals.
    ERef(Type),
    Func(FuncTypeData),
    Struct(StructTypeData),
    /// Dynamically resized array.
    List(Type),
}

/// A closure object, consisting of a dynamic
/// function reference and a reference to an opaque
/// captures struct.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncTypeData {
    pub param_types: Vec<Type>,
    pub return_type: Type,
}

/// Type built in to the engine.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructTypeData {
    pub name: CompactString,
    pub fields: PrimaryMap<Field, FieldData>,
}

entity_ref_16bit! {
    pub struct Field;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldData {
    pub name: CompactString,
    pub typ: Type,
}

entity_ref! {
    /// ID of a constant value in a module.
    pub struct Constant;
}

#[derive(Clone, Debug, PartialEq)]
pub enum ConstantData {
    Int(i64),
    Real(f64),
    Bool(bool),
    Str(CompactString),
}

impl ConstantData {
    pub fn typ(&self) -> TypeData {
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

entity_ref! {
    /// Function ID within a module.
    pub struct Func;
}

#[derive(Debug, Clone)]
pub struct FuncData {
    /// Used for debugging; may be synthetic
    /// in the case of anonymous functions.
    pub name: CompactString,
    /// Type used to store the captured variables
    /// for the function. A managed reference
    /// to the captures is the first argument
    /// to the entry block of the function.
    pub captures_type: Type,
    /// Set of values used by the function. Values can be assigned
    /// multiple times until after the SSA lowering pass is applied.
    pub vals: PrimaryMap<Val, ValData>,
    /// Parameters expected by the function, not including the captures.
    pub param_types: Vec<Type>,
    pub return_type: Type,
    /// Basic blocks in the function instruction stream.
    pub basic_blocks: PrimaryMap<BasicBlock, BasicBlockData>,
    /// Basic block where execution of this function starts.
    pub entry_block: BasicBlock,

    /// Pool of `Local` references used for lists
    /// of locals in `instrs`.
    pub val_lists: ListPool<Val>,
}

impl FuncData {
    /// Creates a `FuncData` with unit captures type.
    pub fn new_no_captures(return_type: Type, module: &mut ModuleData) -> Self {
        Self::with_captures_type(
            return_type,
            module.typ(TypeData::Prim(PrimType::Unit)),
            module,
        )
    }

    /// Visits all basic blocks in an order such that
    /// a block B is not visited until after all blocks that
    /// appear in any *path* (not a walk) from the entry block to B (exclusive)
    /// are visited.
    pub fn visit_basic_blocks_topological(&self, mut visit: impl FnMut(BasicBlock)) {
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

    pub fn with_captures_type(
        captures_type: Type,
        return_type: Type,
        module: &mut ModuleData,
    ) -> Self {
        let locals = PrimaryMap::<Val, ValData>::new();

        let mut basic_blocks = PrimaryMap::<BasicBlock, BasicBlockData>::new();
        let entry_block = basic_blocks.push(BasicBlockData::default());

        Self {
            name: "".into(),
            captures_type,
            vals: locals,
            param_types: Vec::new(),

            return_type,
            basic_blocks,
            entry_block,
            val_lists: ListPool::new(),
        }
    }
}

entity_ref_16bit! {
    pub struct Val;
}

#[derive(Debug, Clone)]
pub struct ValData {
    /// Type of the local.
    pub typ: Type,
}

impl ValData {
    pub fn new(typ: Type) -> Self {
        Self { typ }
    }
}

entity_ref_16bit! {
    pub struct BasicBlock;
}

#[derive(Debug, Clone, Default)]
pub struct BasicBlockData {
    pub instrs: Vec<InstrData>,
    /// Only used after SSA transformation; empty before then, except for
    /// the entry block, where the capture pointer followed by the function arguments are assigned
    /// here.
    pub params: EntityList<Val>,
}
