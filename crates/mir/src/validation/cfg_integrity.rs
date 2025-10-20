use crate::{module::FuncData, validation::ValidationError};

/// Verifies that basic blocks all end in terminators,
/// and terminators only appear as the last instruction
/// in a basic block. Additionally, the entry block
/// cannot appear as a jump target.
pub fn verify_cfg_integrity(func: &FuncData) -> Result<(), ValidationError> {
    for (_, basic_block) in &func.basic_blocks {
        if basic_block.instrs.is_empty() {
            return Err(ValidationError::new("basic block cannot be empty"));
        }
        for instr in &basic_block.instrs[..basic_block.instrs.len() - 1] {
            if instr.is_block_terminator() {
                return Err(ValidationError::new(
                    "terminators can only appear as the last instruction in a basic block",
                ));
            }
        }
        let last_instr = basic_block.instrs.last().unwrap();
        if !last_instr.is_block_terminator() {
            return Err(ValidationError::new(
                "that last instruction in a basic block must be a terminator",
            ));
        }
        let mut error = None;
        last_instr.visit_successors(|dst| {
            if dst == func.entry_block {
                error = Some(ValidationError::new(
                    "entry block cannot appear as a jump target",
                ));
            }
        });
        if let Some(error) = error {
            return Err(error);
        }
    }

    Ok(())
}
