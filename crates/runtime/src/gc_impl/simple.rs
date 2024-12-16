use crate::{
    engine::Instance,
    gc::{GarbageCollector, StackWalker},
    ptr::MRef,
    type_registry::Type,
    Error,
};
use crossbeam_utils::CachePadded;
use parking_lot::{Condvar, Mutex};
use std::{
    alloc::Layout,
    iter, ptr,
    ptr::NonNull,
    sync::{
        atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicUsize, Ordering},
        Barrier,
    },
};
use thread_local::ThreadLocal;

/// Simple garbage collector relying on `malloc` to do allocations,
/// doing a full stop-the-world mark-and-sweep on every GC cycle, and not
/// performing any sort of compaction.
///
/// We add a header to each object consisting of 8 bytes, which are
/// used to tag the object type and for marking during the GC cycle.
pub struct SimpleGarbageCollector {
    /// We rely on `ThreadLocal` not dropping values when threads are destroyed
    /// and continuing to yield these values from `iter`; this is the current behavior
    /// and should not change without a major version break for `thread_local`.
    thread_states: ThreadLocal<CachePadded<ThreadState>>,
    /// Shared memory usage value; note that to reduce contention,
    /// each thread also stores a local counter which must be
    /// added to this value.
    memory_usage: AtomicUsize,
    approx_max_memory: usize,
    cycle_active: AtomicBool,
    /// Contains `true` when the current cycle has finished.
    cycle_completion_mutex: Mutex<bool>,
    cycle_completion_condvar: Condvar,
}

/// State kept local to a thread to reduce contention.
struct ThreadState {
    /// Whether the thread has live references on its stack.
    active: AtomicBool,

    /// List of live objects allocated on this thread (or dead
    /// threads that previously had the same thread index in `thread_local`).
    ///
    /// Used for sweeping.
    live_objects: Mutex<Vec<MRef>>,
    /// Approx. contribution to memory usage of recent allocations on this thread,
    /// i.e. allocations not counted in the shared counter value.
    ///
    /// Note: should only be updated by the owning thread.
    recent_memory_usage: AtomicUsize,
    /// Used to periodically add up global memory usage statistics
    /// and run a GC cycle if needed.
    ///
    /// Note: should only be updated by the owning thread.
    ticks: AtomicU64,
    /// Used to wait for the thread to reach a safepoint
    /// before proceeding with marking. Synchronization
    /// always happens between two threads: this thread
    /// and the thread that initiated the cycle.
    participation_barrier: Barrier,

    /// Pointer to the `StackWalker` for this thread during
    /// a GC cycle. Contents only defined if `safepoint_barrier` was successfully
    /// waited on, and the current cycle has not yet finished.
    stack_walker: Mutex<Option<NonNull<dyn StackWalker>>>,
}

// Soundness: ThreadState does not get auto-impl due to NonNull<dyn StackWalker>;
// however, StackWalker is Send and is behind a mutex, so we can correctly
// implement both Send and Sync.
unsafe impl Send for ThreadState {}
unsafe impl Sync for ThreadState {}

impl Default for ThreadState {
    fn default() -> Self {
        Self {
            active: AtomicBool::new(false),
            live_objects: Mutex::new(Vec::new()),
            recent_memory_usage: AtomicUsize::new(0),
            ticks: AtomicU64::new(0),
            participation_barrier: Barrier::new(2),
            stack_walker: Mutex::new(None),
        }
    }
}

impl SimpleGarbageCollector {
    pub fn new(approx_max_memory: usize) -> Self {
        Self {
            thread_states: ThreadLocal::new(),
            memory_usage: AtomicUsize::new(0),
            approx_max_memory,
            cycle_active: AtomicBool::new(false),
            cycle_completion_mutex: Mutex::new(false),
            cycle_completion_condvar: Condvar::new(),
        }
    }

    #[cold]
    fn do_cycle(&self, stack_walker: &mut dyn StackWalker, instance: &Instance) {
        if self
            .cycle_active
            .compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed)
            .is_err()
        {
            // Another thread already started the cycle; participate and wait for it to finish.
            self.wait_for_cycle_finish(stack_walker);
            return;
        }

        // We need to wait until all active threads are at a safepoint
        // and waiting in `wait_for_cycle_finish`, such that we
        // can access their StackWalkers.
        let this_thread_state = self.thread_states.get_or(Default::default);

        self.memory_usage.fetch_add(
            this_thread_state
                .recent_memory_usage
                .load(Ordering::Relaxed),
            Ordering::Relaxed,
        );
        this_thread_state
            .recent_memory_usage
            .store(0, Ordering::Relaxed);

        let _span = tracing::debug_span!("GC cycle",);
        tracing::debug!(
            memory_usage = self.memory_usage.load(Ordering::Relaxed),
            "starting GC cycle"
        );

        let mut stack_walkers = vec![stack_walker];
        for thread_state in self.thread_states.iter() {
            if ptr::eq(thread_state, this_thread_state) {
                continue;
            }

            if thread_state.active.load(Ordering::Relaxed) {
                continue; // TODO race condition with mark_thread_active - could observe false, skip, then thread becomes active but not observed
            }

            thread_state.participation_barrier.wait();
            // Thread is now inside wait_for_cycle_finish
            // and will remain parked there until we notify
            // cycle_completion_condvar.
            unsafe {
                stack_walkers.push(thread_state.stack_walker.lock().unwrap().as_mut());
            }
        }

        tracing::trace!("threads synchronized, running mark-and-sweep");

        self.mark(&mut stack_walkers, instance);
        self.sweep(instance);

        tracing::debug!(
            memory_usage = self.memory_usage.load(Ordering::Relaxed),
            "collected"
        );

        *self.cycle_completion_mutex.lock() = true;
        self.cycle_completion_condvar.notify_all();

        // Ordering matters here; we need to ensure that in wait_for_cycle_finish,
        // if `cycle_completion_mutex` is observed (which would be a false negative
        // indicator of completion), then the thread will still observe
        // completion by finding `cycle_active == false`.
        self.cycle_active.store(false, Ordering::Release);
        *self.cycle_completion_mutex.lock() = false;
    }

    fn mark(&self, stack_walkers: &mut [&mut dyn StackWalker], instance: &Instance) {
        let mut roots = Vec::new();
        for stack_walker in stack_walkers {
            while let Some(live_ref) = stack_walker.next() {
                if live_ref.as_ptr().is_null() {
                    continue;
                }
                unsafe {
                    if ObjectHeader::of(live_ref).mark() {
                        roots.push(live_ref);
                    }
                }
            }
        }

        while let Some(live_ref) = roots.pop() {
            unsafe {
                let header = ObjectHeader::of(live_ref);
                instance.engine.type_registry.traverse_references(
                    live_ref.as_ptr(),
                    header.typ,
                    |pointer| {
                        if pointer.as_ptr().is_null() {
                            return;
                        }

                        let pointee_header = ObjectHeader::of(pointer);
                        if pointee_header.mark() {
                            roots.push(pointer);
                        }
                    },
                );
            }
        }
    }

    fn sweep(&self, instance: &Instance) {
        for thread_state in self.thread_states.iter() {
            thread_state.live_objects.lock().retain(|&r| {
                let header = unsafe { ObjectHeader::of(r) };
                if header.is_marked() {
                    header.unmark();
                    true
                } else {
                    // Object is no longer reachable
                    unsafe {
                        self.dealloc(r, instance);
                    }
                    false
                }
            });
        }
    }

    unsafe fn dealloc(&self, r: MRef, instance: &Instance) {
        // `r` points to the _value_ part of the object,
        // which is not the start of the allocation due to
        // the object header. We need to subtract the value offset
        // to get the original pointer returned from the allocator.
        let header = ObjectHeader::of(r);
        let layout = ObjectLayout::new(instance.engine.type_registry.layouts[header.typ].unwrap());

        let allocated_ptr = r.as_ptr().offset(-(layout.value_offset as isize));
        std::alloc::dealloc(allocated_ptr, layout.overall);

        self.memory_usage
            .fetch_sub(layout.overall.size(), Ordering::Relaxed);
    }

    #[cold]
    fn wait_for_cycle_finish(&self, stack_walker: &mut dyn StackWalker) {
        // Lifetime extension. Soundness: the GC synchronization logic ensures
        // that the stack walker is only accessed by the initiating
        // thread while this function is active (i.e. cycle_completion_condvar
        // has not yet been notified)
        let stack_walker = unsafe {
            std::mem::transmute::<&'_ mut dyn StackWalker, &'static mut dyn StackWalker>(
                stack_walker,
            )
        };

        let thread_state = self.thread_states.get_or(Default::default);
        *thread_state.stack_walker.lock() =
            Some(NonNull::new(stack_walker as *mut dyn StackWalker).unwrap());
        thread_state.participation_barrier.wait();

        self.memory_usage.fetch_add(
            thread_state.recent_memory_usage.load(Ordering::Relaxed),
            Ordering::Relaxed,
        );
        thread_state.recent_memory_usage.store(0, Ordering::Relaxed);

        let mut guard = self.cycle_completion_mutex.lock();
        if *guard {
            return;
        }
        if !self.cycle_active.load(Ordering::Acquire) {
            return;
        }
        self.cycle_completion_condvar.wait(&mut guard);
    }
}

impl GarbageCollector for SimpleGarbageCollector {
    fn allocate(
        &self,
        instance: &Instance,
        typ: Type,
        stack_walker: &mut dyn StackWalker,
    ) -> Result<MRef, Error> {
        let type_layout = instance.engine.type_registry.layouts[typ].unwrap();
        let object_layout = ObjectLayout::new(type_layout);

        if type_layout.size() == 0 {
            // No need to allocate for a zero-sized type.
            unsafe {
                return Ok(MRef::new(ptr::null_mut()));
            }
        }

        let thread_state = self.thread_states.get_or(Default::default);

        if object_layout.overall.size()
            + self.memory_usage.load(Ordering::Relaxed)
            + thread_state.recent_memory_usage.load(Ordering::Relaxed)
            > self.approx_max_memory
        {
            self.do_cycle(stack_walker, instance);
            if object_layout.overall.size()
                + self.memory_usage.load(Ordering::Relaxed)
                + thread_state.recent_memory_usage.load(Ordering::Relaxed)
                > self.approx_max_memory
            {
                return Err(Error::OutOfMemory);
            }
        }

        // Soundness: since `object_layout` always includes the
        // footer, it is never of zero size.
        let ptr = unsafe {
            std::alloc::alloc_zeroed(object_layout.overall).add(object_layout.value_offset)
        };
        if ptr.is_null() {
            return Err(Error::OutOfSystemMemory);
        }

        // Soundness: the pointer is managed by this garbage collector.
        let mref = unsafe { MRef::new(ptr) };

        unsafe {
            ObjectHeader::init(mref, typ);
        }

        thread_state.live_objects.lock().push(mref);

        // Manual load=>add=>store avoids using atomic read-modify-update instructions;
        // this improves performance
        // but obviously breaks when multiple threads mutate the counter at once (but
        // only this thread should update these values).
        thread_state.recent_memory_usage.store(
            thread_state.recent_memory_usage.load(Ordering::Relaxed) + object_layout.overall.size(),
            Ordering::Relaxed,
        );
        let tick = thread_state.ticks.load(Ordering::Relaxed);
        thread_state.ticks.store(tick + 1, Ordering::Relaxed);

        if tick % 256 == 0 || object_layout.overall.size() >= 1024 {
            self.memory_usage.fetch_add(
                thread_state.recent_memory_usage.load(Ordering::Relaxed),
                Ordering::Relaxed,
            );
            thread_state.recent_memory_usage.store(0, Ordering::Relaxed);
            if self.memory_usage.load(Ordering::Relaxed) >= self.approx_max_memory {
                self.do_cycle(stack_walker, instance);
            }
        }

        Ok(mref)
    }

    fn safepoint(&self, _instance: &Instance, stack_walker: &mut dyn StackWalker) {
        if self.cycle_active.load(Ordering::Relaxed) {
            self.wait_for_cycle_finish(stack_walker);
        }
    }

    fn mark_thread_active(&self) {
        self.thread_states
            .get_or(Default::default)
            .active
            .store(true, Ordering::Relaxed); // TODO bug
        if self.cycle_active.load(Ordering::Relaxed) {
            // We don't have any live references on the stack,
            // but we do need to wait for the GC cycle to complete;
            // otherwise `wait_for_cycle_finish` could deadlock due to not
            // being notified
            todo!()
        }
    }

    fn mark_thread_inactive(&self) {
        self.thread_states
            .get_or(Default::default)
            .active
            .store(false, Ordering::Relaxed);
        if self.cycle_active.load(Ordering::Relaxed) {
            // since thread is now inactive, we have no live references on the stack; pass an empty StackWalker
            self.wait_for_cycle_finish(&mut iter::empty());
        }
    }
}

#[repr(C)]
struct ObjectHeader {
    typ: Type,
    mark: AtomicU32,
}

impl ObjectHeader {
    pub fn new(typ: Type) -> Self {
        Self {
            typ,
            mark: AtomicU32::new(0),
        }
    }

    /// Tries to mark the object; returns `false`
    /// if the object was already marked.
    pub fn mark(&self) -> bool {
        self.mark
            .compare_exchange(0, 1, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok()
    }

    pub fn unmark(&self) {
        self.mark.store(0, Ordering::Relaxed);
    }

    pub fn is_marked(&self) -> bool {
        self.mark.load(Ordering::Relaxed) == 1
    }

    pub unsafe fn of(r: MRef) -> &'static Self {
        unsafe {
            let ptr = r.as_ptr().offset(-(size_of::<Self>() as isize));
            &*ptr.cast()
        }
    }

    pub unsafe fn init(r: MRef, typ: Type) {
        unsafe {
            let ptr = r
                .as_ptr()
                .offset(-(size_of::<Self>() as isize))
                .cast::<Self>();
            ptr.write(ObjectHeader::new(typ));
        }
    }
}

struct ObjectLayout {
    overall: Layout,
    value_offset: usize,
}

impl ObjectLayout {
    pub fn new(value_layout: Layout) -> Self {
        let header = Layout::new::<ObjectHeader>();
        let (overall, value_offset) = header.extend(value_layout).unwrap();
        Self {
            overall,
            value_offset,
        }
    }
}
