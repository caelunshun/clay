use fir_mir::ir::{BasicBlockId, FuncId};
use mir::TypeArgs;
use salsa::Database;
use std::collections::BTreeSet;

#[salsa::interned]
pub struct InternedStrand<'db> {
    pub data: Strand<'db>,
}

/// A strand of basic blocks: the unit of compilation.
///
/// A strand has a single entry block, and a set of jump targets
/// that are considered exits.,
/// The strand then contains all reachable blocks between the entry
/// and the exits.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Strand<'db> {
    entry: GBasicBlockId,
    /// Function type arguments in the entry function.
    entry_type_args: TypeArgs<'db>,
    exits: BTreeSet<Exit>,
}

impl<'db> Strand<'db> {
    pub fn new(
        entry: GBasicBlockId,
        entry_type_args: TypeArgs<'db>,
        exits: impl IntoIterator<Item = Exit>,
    ) -> Self {
        Self {
            entry,
            entry_type_args,
            exits: exits.into_iter().collect(),
        }
    }

    pub fn entry(&self) -> GBasicBlockId {
        self.entry
    }

    pub fn entry_type_args(&self) -> &TypeArgs<'db> {
        &self.entry_type_args
    }

    pub fn entry_func(&self) -> FuncId {
        self.entry.func
    }

    pub fn exits(&self) -> impl Iterator<Item = Exit> {
        self.exits.iter().copied()
    }

    pub fn is_exit(&self, exit: Exit) -> bool {
        self.exits.contains(&exit)
    }
}

/// An exit of a strand.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Exit {
    /// The block the exit instruction is in.
    pub block: GBasicBlockId,
    /// The target block being jumped to or called.
    /// For instructions with multiple targets (e.g. branch),
    /// this allows representing strands that exit only
    /// for a subset of the targets.
    pub target: GBasicBlockId,
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
