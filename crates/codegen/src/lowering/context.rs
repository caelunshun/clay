use crate::{backend, lowering::BbInstance, strand::GBasicBlockId};
use bumpalo::Bump;
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
