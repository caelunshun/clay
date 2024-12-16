use crate::{engine::Instance, ptr::MRef, type_registry::Type, Error};

/// A memory management implementation for the Zyon runtime.
///
/// Garbage collectors handle both allocation and deallocation
/// of memory.
pub trait GarbageCollector: Send + Sync {
    /// Allocate managed memory for an object of the given type.
    fn allocate(
        &self,
        instance: &Instance,
        typ: Type,
        stack_walker: &mut dyn StackWalker,
    ) -> Result<MRef, Error>;

    /// GC safepoint: potentially check if another thread has started
    /// a GC cycle, and participate if needed.
    fn safepoint(&self, instance: &Instance, stack_walker: &mut dyn StackWalker);

    /// Registers the current thread as active in Zyon code;
    /// this will cause GC cycles to wait for `safepoint` to be
    /// called on this thread before proceeding.
    ///
    /// A call to this function should always be followed by a call to `safepoint`
    /// before beginning Zyon execution.
    fn mark_thread_active(&self);
    /// Deregisters the current thread as active in Zyon code.
    fn mark_thread_inactive(&self);
}

/// Passed to the garbage collector to traverse
/// all managed references stored on the local stack.
pub trait StackWalker: Send {
    fn next(&mut self) -> Option<MRef>;
}

impl<T> StackWalker for T
where
    T: Iterator<Item = MRef> + Send,
{
    fn next(&mut self) -> Option<MRef> {
        <Self as Iterator>::next(self)
    }
}
