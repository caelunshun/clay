use fir_mir::ir::{BasicBlockId, FuncId};

/// A strand of basic blocks: the unit of compilation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Strand(Vec<GBasicBlockId>);

impl Strand {
    pub fn new(blocks: impl IntoIterator<Item = GBasicBlockId>) -> Self {
        let mut blocks = blocks.into_iter().collect::<Vec<_>>();
        blocks.sort_unstable();
        blocks.dedup();
        Self(blocks)
    }

    pub fn blocks(&self) -> impl Iterator<Item = GBasicBlockId> {
        self.0.iter().copied()
    }
}

/// An MIR basic block ID and the function it's associated with.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GBasicBlockId {
    pub func: FuncId,
    pub bb: BasicBlockId,
}
