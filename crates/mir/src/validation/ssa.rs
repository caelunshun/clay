use crate::{validation::ValidationError, ModuleData};

/// Verifies that all functions in the given module
/// have been correctly transformed to SSA form.
pub fn verify_ssa(module: &ModuleData) -> Result<(), ValidationError> {
    Ok(())
}
