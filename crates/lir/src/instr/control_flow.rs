use crate::{
    func_family::{basic_block::BasicBlock, val::ValPtr},
    instr,
};
use clay_core::ghost_heap::GhostPtr;

instr! {
    pub struct Jump {
        pub block: GhostPtr<'g, BasicBlock<'g>>,
        pub args: GhostPtr<'g, [ValPtr<'g>]>,
    }
}

instr! {
    pub struct Branch {
        pub cond: ValPtr<'g>,
        pub true_block: GhostPtr<'g, BasicBlock<'g>>,
        pub true_args: GhostPtr<'g, [ValPtr<'g>]>,
        pub false_block: GhostPtr<'g, BasicBlock<'g>>,
        pub false_args: GhostPtr<'g, [ValPtr<'g>]>,
    }
}
