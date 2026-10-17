use crate::{arena::Ptr, func_family::basic_block::BasicBlock};

#[derive(Debug, Clone)]
pub enum Terminator {
    Jump(Ptr<BasicBlock>),
}
