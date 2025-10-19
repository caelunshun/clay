use crate::{
    Val,
    module::{BasicBlock, FuncData},
    validation::ValidationError,
};
use cranelift_entity::{EntitySet, SecondaryMap};

/// Verifies that all values are initialized as the
/// destination operand of an instruction before they are used.
///
/// Specifically, if a value is used as a source operand in a block B_1,
/// then it must appear as a destination operand in all paths from the
/// entry block to B_1.
pub fn verify_value_initialization(func: &FuncData) -> Result<(), ValidationError> {
    let mut values_written_by_blocks = SecondaryMap::<BasicBlock, EntitySet<Val>>::new();
    for (block, block_data) in &func.basic_blocks {
        for &param in block_data.params.as_slice(&func.val_lists) {
            values_written_by_blocks[block].insert(param);
        }

        for &instr in &block_data.instrs {
            instr.visit_dst_operands(&func.val_lists, |val| {
                values_written_by_blocks[block].insert(val);
            });
        }
    }

    let paths = func.compute_paths_from_entry();
    for (block, block_data) in &func.basic_blocks {
        let mut written_this_block = EntitySet::new();
        for &param in block_data.params.as_slice(&func.val_lists) {
            written_this_block.insert(param);
        }

        for &instr in &block_data.instrs {
            let mut error = None;
            instr.visit_src_operands(&func.val_lists, |val| {
                    if !written_this_block.contains(val) && paths[block]
                        .iter()
                        .any(|path| {
                            !path.iter().any(|pred| values_written_by_blocks[pred].contains(val))
                        }){
                        error = Some(ValidationError::new(format!("value {val:?} is used as a source operand in block {block:?} instruction {instr:?}, but it is not initialized on every CFG path")));
                    }
                });
            if let Some(error) = error {
                return Err(error);
            }

            instr.visit_dst_operands(&func.val_lists, |val| {
                written_this_block.insert(val);
            });
        }
    }
    Ok(())
}
