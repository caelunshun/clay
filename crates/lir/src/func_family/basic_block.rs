use crate::func_family::terminator::Terminator;
use clay_core::ghost_heap::GhostHeap;

#[derive(Debug)]
pub struct BasicBlock {
    pub terminator: Terminator,
}
