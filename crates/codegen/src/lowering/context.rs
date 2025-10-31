use crate::{backend, strand::GBasicBlockId};
use bumpalo::Bump;
use fir_core::HashMap;

/// Contains cached allocations for reusing across multiple lowerings.
#[derive(Default)]
pub struct LoweringCx {
    pub(super) bump: Bump,
    pub(super) bb_mapping: HashMap<GBasicBlockId, backend::BasicBlockId>,
}

impl LoweringCx {
    pub(super) fn reset(&mut self) {
        self.bump.reset();
        self.bb_mapping.clear();
    }
}
