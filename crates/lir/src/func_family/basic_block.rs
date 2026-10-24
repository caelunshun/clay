use crate::instr::InstrPtr;
use clay_core::ghost_heap::GhostPointee;

pub struct BasicBlock<'g> {
    pub first_instr: InstrPtr<'g>,
    pub last_instr: InstrPtr<'g>,
}

unsafe impl<'g> GhostPointee<'g> for BasicBlock<'g> {
    type ForLt<'new_g> = BasicBlock<'new_g>;
}
