use crate::instr::InstrData;
use compact_str::CompactString;
use cranelift_entity::{ListPool, PrimaryMap, SecondaryMap};

#[derive(Debug, Clone, Default)]
pub struct ModuleData {
    pub types: PrimaryMap<LocalType, TypeData>,
    pub funcs: PrimaryMap<LocalFunc, FuncData>,
    pub constants: PrimaryMap<Constant, ConstantData>,
    // pub imported_modules: PrimaryMap<ImportedModule, ImportedModuleData>,
}

impl ModuleData {
    pub fn constant(&mut self, c: ConstantData) -> Constant {
        self.constants.push(c)
    }
}

entity_ref_16bit! {
    /// ID of a type used in a module.
    pub struct LocalType;
}

#[derive(Debug, Clone)]
pub enum TypeData {
    Primitive(PrimitiveType),
    /// Managed reference to another type.
    Reference(LocalType),
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LazyTypeData {
    /// Underlying type of the variable.
    pub inner_type: LocalType,
    /// Function used to initialize the value.
    pub initializer_func: LocalFunc,
}

/// A closure object, consisting of a dynamic
/// function reference and a reference to an opaque
/// captures struct.
#[derive(Debug, Clone)]
pub struct FuncTypeData {
    pub param_types: Vec<LocalType>,
    pub return_type: LocalType,
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
    pub typ: LocalType,
}

entity_ref! {
    /// ID of a constant value in a module.
    pub struct Constant;
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum ConstantData {
    Int(i64),
    Real(f64),
    Bool(bool),
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
    pub struct LocalFunc;
}

#[derive(Debug, Clone, Default)]
pub struct FuncData {
    /// Used for debugging; may be synthetic
    /// in the case of anonymous functions.
    pub name: CompactString,
    /// Type used to store the captured variables
    /// for the function. At runtime, the value in `captures_local`
    /// at the start of the function will have type `Reference(captures_type)`.
    pub captures_type: LocalType,
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
    pub fn param_type(&self, param: FuncParam) -> &LocalType {
        &self.locals[self.params[param].bind_to_local].typ
    }

    pub fn local(&mut self, typ: LocalType) -> Local {
        self.locals.push(LocalData::new(typ))
    }

    pub fn instr(&mut self, instr: InstrData) -> Instr {
        self.instrs.push(instr)
    }
}

entity_ref_16bit! {
    pub struct Local;
}

#[derive(Debug, Clone)]
pub struct LocalData {
    /// Type of the local.
    pub typ: LocalType,
}

impl LocalData {
    pub fn new(typ: LocalType) -> Self {
        Self { typ }
    }
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
