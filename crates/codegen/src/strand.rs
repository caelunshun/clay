use fir_mir::ir::{BasicBlockId, FuncId};
use salsa::Database;
use std::collections::BTreeSet;

/// A strand of basic blocks: the unit of compilation.
///
/// This consists of a tree of "strand atoms", each of which
/// is a tuple (function, bbs) corresponding to one or more
/// basic blocks in the same function.
///
/// The children of a strand atom represent calls to effectively-inlined
/// functions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Strand {
    /// Boxed to ensure `StrandAtomId` remains stable.
    root_atom: Box<StrandAtom>,
}

impl Strand {
    pub fn new(root_atom: StrandAtom) -> Self {
        Self {
            root_atom: Box::new(root_atom),
        }
    }

    pub fn root_atom(&self) -> &StrandAtom {
        &self.root_atom
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StrandAtom {
    func: FuncId,
    entry: BasicBlockId,
    bbs: BTreeSet<BasicBlockId>,
    children: Vec<StrandAtom>,
}

impl StrandAtom {
    pub fn new(
        func: FuncId,
        entry: BasicBlockId,
        bbs: impl IntoIterator<Item = BasicBlockId>,
    ) -> Self {
        let bbs: BTreeSet<_> = bbs.into_iter().collect();
        assert!(bbs.contains(&entry), "entry block must be in the atom");
        Self {
            func,
            entry,
            bbs,
            children: Vec::new(),
        }
    }

    pub fn push_child(&mut self, child: StrandAtom) {
        self.children.push(child);
    }

    pub fn func(&self) -> FuncId {
        self.func
    }

    pub fn entry(&self) -> BasicBlockId {
        self.entry
    }

    pub fn bbs(&self) -> impl Iterator<Item = BasicBlockId> {
        self.bbs.iter().copied()
    }

    pub fn bbs_as_global(&self) -> impl Iterator<Item = GBasicBlockId> {
        self.bbs().map(|bb| GBasicBlockId {
            func: self.func,
            bb,
        })
    }

    pub fn contains_bb(&self, bb: BasicBlockId) -> bool {
        self.bbs.contains(&bb)
    }

    pub fn children(&self) -> impl Iterator<Item = &StrandAtom> {
        self.children.iter()
    }

    pub fn id(&self) -> StrandAtomId {
        StrandAtomId(self as *const _)
    }
}

/// Identifies a `StrandAtom` within a strand.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct StrandAtomId(*const StrandAtom);

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
