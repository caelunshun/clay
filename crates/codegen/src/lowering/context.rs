use crate::{
    backend,
    lowering::{BbInstance, compound_val::Compound},
    strand::GBasicBlockId,
};
use bumpalo::Bump;
use cranelift_entity::SecondaryMap;
use fir_core::HashMap;

/// Contains cached allocations for reusing across multiple lowerings.
#[derive(Default)]
pub struct LoweringCx {
    pub(super) bump: Bump,
}

impl LoweringCx {
    pub(super) fn reset(&mut self) {
        self.bump.reset();
    }
}
