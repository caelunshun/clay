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
    // TODO
}
