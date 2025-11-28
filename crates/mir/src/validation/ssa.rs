use crate::{ValId, ir::FuncData, validation::ValidationError};
use cranelift_entity::EntitySet;

/// Verifies that the function has been correctly
/// transformed to SSA form.
pub fn verify_ssa(func: &FuncData) -> Result<(), ValidationError> {
    for (block, block_data) in &func.basic_blocks {
        let mut written_vals = EntitySet::<ValId>::new();
        written_vals.extend(block_data.params.as_slice(&func.val_lists).iter().copied());
        for (_, instr) in &block_data.instrs {
            let mut error = None;
            instr.visit_src_operands(&func.val_lists, |val| {
                   if !written_vals.contains(val) {
                       error = Some(ValidationError::new(format!("SSA violation: value {val:?} is not in scope in block {block:?} when used at instruction {instr:?}")));
                   }
                });
            instr.visit_dst_operands(&func.val_lists, |val| {
                    if written_vals.contains(val) {
                        error = Some(ValidationError::new(format!("SSA violation: value {val:?} is written a second time in block {block:?} instr {instr:?}")));
                    }
                    written_vals.insert(val);
                });
            if let Some(error) = error {
                return Err(error);
            }
        }
    }

    Ok(())
}
