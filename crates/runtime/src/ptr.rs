use bytemuck::{Pod, Zeroable};
use std::ptr::NonNull;

/// Wrapper for a managed reference to an opaque
/// value.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct MRef(*mut u8);

impl MRef {
    /// # Safety
    /// The pointer must be managed by the garbage collector,
    /// and have been correctly allocated.
    pub unsafe fn new(ptr: NonNull<u8>) -> Self {
        Self(ptr.as_ptr())
    }

    pub fn as_ptr(&self) -> *mut u8 {
        self.0
    }
}

unsafe impl Send for MRef {}
unsafe impl Sync for MRef {}

// RIP pointer provenance (TODO)
unsafe impl Zeroable for MRef {}
unsafe impl Pod for MRef {}
