use fir_mir::ir::{BasicBlockId, FuncId};
use mir::{FuncInstance, TypeArgs};
use salsa::Database;

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
    entry: GBasicBlockId<'db>,
    /// Function type arguments in the entry function.
    entry_type_args: TypeArgs<'db>,
    exits: Vec<Exit<'db>>,
}

impl<'db> Strand<'db> {
    pub fn new(
        entry: GBasicBlockId<'db>,
        entry_type_args: TypeArgs<'db>,
        exits: impl IntoIterator<Item = Exit<'db>>,
    ) -> Self {
        Self {
            entry,
            entry_type_args,
            exits: exits.into_iter().collect(),
        }
    }

    pub fn entry(&self) -> GBasicBlockId<'db> {
        self.entry
    }

    pub fn entry_type_args(&self) -> &TypeArgs<'db> {
        &self.entry_type_args
    }

    pub fn entry_func(&self) -> FuncInstance<'db> {
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
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Exit<'db> {
    /// The block the exit instruction is in.
    pub block: GBasicBlockId<'db>,
    /// The target block being jumped to or called.
    /// For instructions with multiple targets (e.g. branch),
    /// this allows representing strands that exit only
    /// for a subset of the targets.
    pub target: GBasicBlockId<'db>,
}

/// "Global" basic block. An MIR basic block ID and the function it's associated with.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct GBasicBlockId<'db> {
    pub func: FuncInstance<'db>,
    pub bb: BasicBlockId,
}

impl<'db> GBasicBlockId<'db> {
    pub fn new(func: FuncInstance<'db>, bb: BasicBlockId) -> Self {
        Self { func, bb }
    }

    pub fn resolve(
        &self,
        db: &'db dyn Database,
        cx: mir::Context<'db>,
    ) -> &'db mir::BasicBlock<'db> {
        &self.func.id(db).resolve(db, cx).data(db).basic_blocks[self.bb]
    }
}
