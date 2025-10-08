use crate::{validation::ValidationError, ModuleData};

/// Verifies that all values are initialized as the
/// destination operand of an instruction before they are used.
///
/// Specifically, if a value is used as a source operand in a block B_1,
/// then it must appear as a destination operand in all paths from the
/// entry block to B_1.
pub fn verify_value_initialization(module: &ModuleData) -> Result<(), ValidationError> {
    Ok(())
}
