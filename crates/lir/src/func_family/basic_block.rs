use crate::func_family::{instr::Instr, terminator::Terminator};

#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub instrs: Vec<Instr>,
    pub terminator: Terminator,
}
