use index_vec::{IndexVec, define_index_type};

define_index_type! {
    pub struct MirBlockIdx = u32;
}

#[derive(Debug, Clone)]
pub struct MirBody {
    pub blocks: IndexVec<MirBlockIdx, MirBlock>,
}

#[derive(Debug, Clone)]
pub struct MirBlock {
    pub stmt: Vec<MirStmt>,
    pub terminator: MirTerminator,
}

#[derive(Debug, Clone)]
pub struct MirStmt {}

#[derive(Debug, Clone)]
pub enum MirStmtKind {}

#[derive(Debug, Clone)]
pub enum MirTerminator {
    Goto(MirBlockIdx),
    Switch(),
    Unreachable,
}
