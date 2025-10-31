use crate::{intrinsic::IntrinsicCall, strand::GBasicBlockId};

/// Contains machine code for a strand,
/// along with metadata for relocations, GC
/// stack maps, etc.
#[derive(Debug, Clone)]
pub struct CompiledStrand {
    code: Vec<u8>,
    metadata: CompiledStrandMetadata,
}

impl CompiledStrand {
    pub fn new(code: impl Into<Vec<u8>>, metadata: CompiledStrandMetadata) -> Self {
        Self {
            code: code.into(),
            metadata,
        }
    }

    pub fn code(&self) -> &[u8] {
        &self.code
    }

    pub fn metadata(&self) -> &CompiledStrandMetadata {
        &self.metadata
    }
}

#[derive(Debug, Clone)]
pub struct CompiledStrandMetadata {
    relocations: Vec<Relocation>,
}

impl CompiledStrandMetadata {
    pub fn new(relocations: Vec<Relocation>) -> Self {
        Self { relocations }
    }

    pub fn relocations(&self) -> &[Relocation] {
        &self.relocations
    }
}

/// Specifies a portion of the compiled machine code
/// that needs to be modified at runtime to point to the address
/// of some function or global value.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Relocation {
    kind: RelocationKind,
    offset_in_code: usize,
    symbol: Symbol,
}

/// Specifies how the code needs to be updated for a relocation.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum RelocationKind {
    /// The 4-byte (little-endian) value at the given
    /// offset in the code buffer should be replaced
    /// with the absolute address of the symbol.
    Abs4,
    /// The 8-byte (little-endian) value at the givne
    /// offset in the code buffer should be replaced
    /// with the absolute address of the symbol.
    Abs8,
}

/// Specifies what entity's address to use for a relocation.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Symbol {
    /// Intrinsic host call, used to implement internal runtime features.
    Intrinsic(IntrinsicCall),
    /// Address of the GOT entry storing the address
    /// of the compiled strand whose entry is the given
    /// basic block.
    StrandForBlock(GBasicBlockId),
}
