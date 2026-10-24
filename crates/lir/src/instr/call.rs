use crate::{func_family::val::ValPtr, instr, subst_func::SubstFunc};
use clay_core::ghost_heap::GhostPtr;

instr! {
    pub struct Call {
        pub func: SubstFunc,
        pub args: GhostPtr<'g, [ValPtr<'g>]>,
    }
}
