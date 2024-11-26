use crate::instr::InstrData;
use compact_str::CompactString;
use cranelift_entity::{ListPool, PrimaryMap, SecondaryMap};

#[derive(Debug, Clone)]
pub struct ModuleData {
    pub types: PrimaryMap<Type, TypeData>,
    pub funcs: PrimaryMap<Func, FuncData>,
    // pub imported_modules: PrimaryMap<ImportedModule, ImportedModuleData>,
}

entity_ref_16bit! {
    /// ID of a type used in a module.
    pub struct Type;
}

#[derive(Debug, Clone)]
pub enum TypeData {
    Primitive(PrimitiveType),
    /// Managed reference to another type.
    Reference(Type),
    Func(FuncTypeData),
    Lazy(LazyTypeData),
    Struct(StructTypeData),
}

/// Special lazily-initialized type used during module
/// initialization to allow forward references and
/// recursion.
///
/// The initializer function is part of the type; thus
/// each lazy variable gets a different type.
///
/// Value is initialized by the associated initializer
/// function on first use.
#[derive(Debug, Clone)]
pub struct LazyTypeData {
    /// Underlying type of the variable.
    pub inner_type: Type,
    /// Function used to initialize the value.
    pub initializer_func: Func,
}

/// A closure object, consisting of a dynamic
/// function reference and a reference to an opaque
/// captures struct.
#[derive(Debug, Clone)]
pub struct FuncTypeData {
    pub param_types: Vec<Type>,
    pub return_type: Type,
}

/// Type built in to the language.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum PrimitiveType {
    /// 64-bit signed integer.
    Int,
    /// 64-bit float.
    Real,
    /// Boolean.
    Bool,
    /// The empty type, having only one value.
    Unit,
}

#[derive(Debug, Clone)]
pub struct StructTypeData {
    pub name: CompactString,
    pub fields: PrimaryMap<Field, FieldData>,
}

entity_ref_16bit! {
    pub struct Field;
}

#[derive(Debug, Clone)]
pub struct FieldData {
    pub name: CompactString,
    pub typ: Type,
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
    pub struct Func;
}

#[derive(Debug, Clone)]
pub struct FuncData {
    /// Used for debugging; may be synthetic
    /// in the case of anonymous functions.
    pub name: CompactString,
    /// Type used to store the captured variables
    /// for the function.
    pub captures_type: Type,
    /// Local into which the captures are placed
    /// by the interpreter
    /// when the function is called.
    pub captures_local: Local,
    /// Set of locals allocated by the function.
    /// These are analogous to "registers" in a VM.
    pub locals: PrimaryMap<Local, LocalData>,
    /// Names of locals for debugging, potentially synthetic
    /// when no corresponding identifier exists in the source code.
    /// These are stored in a separate map as they are accessed
    /// much less frequently than the `LocalData` itself, and they
    /// could otherwise pollute the cache in the interpreter loop.
    pub local_names: SecondaryMap<Local, CompactString>,
    /// Parameters expected by the function.
    pub params: PrimaryMap<FuncParam, FuncParamData>,
    /// Names of the function parameters for debugging;
    /// see `local_names` for why this is a separate map.
    pub param_names: SecondaryMap<FuncParam, CompactString>,
    /// Flat representation of the instructions to be executed
    /// when the function is called.
    pub instrs: PrimaryMap<Instr, InstrData>,

    /// Pool of `Local` references used for lists
    /// of locals in `instrs`.
    pub local_pool: ListPool<Local>,
}

impl FuncData {
    /// Gets the type expected for the given parameter.
    pub fn param_type(&self, param: FuncParam) -> &Type {
        &self.locals[self.params[param].bind_to_local].typ
    }
}

entity_ref_16bit! {
    pub struct Local;
}

#[derive(Debug, Clone)]
pub struct LocalData {
    /// Type of the local.
    pub typ: Type,
}

entity_ref_16bit! {
    pub struct Instr;
}

entity_ref! {
    pub struct FuncParam;
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct FuncParamData {
    /// Local to which this parameter is bound
    /// at call time.
    ///
    /// The type of the parameter equals the type
    /// of the local.
    pub bind_to_local: Local,
}
