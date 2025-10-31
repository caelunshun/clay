use fir_core::IndexSet;
use fir_mir::ir::{BasicBlockId, FuncId};
use salsa::Database;

/// A strand of basic blocks: the unit of compilation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Strand {
    blocks: IndexSet<GBasicBlockId>,
    entry_block: GBasicBlockId,
}

impl Strand {
    pub fn new(
        blocks: impl IntoIterator<Item = GBasicBlockId>,
        entry_block: GBasicBlockId,
    ) -> Self {
        let blocks = blocks.into_iter().collect::<IndexSet<_>>();
        assert!(
            blocks.contains(&entry_block),
            "entry block must be part of the strand"
        );

        Self {
            blocks,
            entry_block,
        }
    }

    pub fn blocks(&self) -> impl Iterator<Item = GBasicBlockId> {
        self.blocks.iter().copied()
    }

    pub fn contains_block(&self, block: GBasicBlockId) -> bool {
        self.blocks.contains(&block)
    }

    pub fn entry_block(&self) -> GBasicBlockId {
        self.entry_block
    }
}

/// "Global" basic block. An MIR basic block ID and the function it's associated with.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GBasicBlockId {
    pub func: FuncId,
    pub bb: BasicBlockId,
}

impl GBasicBlockId {
    pub fn new(func: FuncId, bb: BasicBlockId) -> Self {
        Self { func, bb }
    }

    pub fn resolve<'db>(
        &self,
        db: &'db dyn Database,
        cx: mir::Context<'db>,
    ) -> &'db mir::BasicBlock<'db> {
        &self.func.resolve(db, cx).data(db).basic_blocks[self.bb]
    }
}
