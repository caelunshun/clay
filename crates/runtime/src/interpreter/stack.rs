use bytemuck::{Pod, Zeroable};
use core::slice;
use std::{
    any::type_name,
    cell::{Cell, RefCell, UnsafeCell},
    mem::MaybeUninit,
    ptr,
};

#[derive(Debug, Default)]
pub struct Stack {
    /// Storage for locals.
    ///
    /// Stored as `Aligned16` to ensure alignment to 16 bytes.
    ///
    /// We should never return a reference to the data
    /// slice from a public method.
    data: UnsafeCell<Vec<MaybeUninit<Aligned16>>>,
    /// Start of the current stack frame as a _byte_
    /// index into `data`.
    current_frame: Cell<usize>,
    previous_frames: RefCell<Vec<usize>>,
}

unsafe impl Send for Stack {}

#[derive(Copy, Clone, Debug, Pod, Zeroable)]
#[repr(C, align(16))]
struct Aligned16(u128);

impl Stack {
    pub const MAX_ALIGN: usize = align_of::<Aligned16>();

    pub fn new() -> Self {
        Self::default()
    }

    pub fn clear(&self) {
        self.current_frame.set(0);
        self.previous_frames.borrow_mut().clear();
        unsafe {
            (*self.data.get()).clear();
        }
    }

    /// Begins a new stack frame for the given function.
    pub fn push_frame(&self, func_stack_size: usize) {
        self.previous_frames
            .borrow_mut()
            .push(self.current_frame.get());

        unsafe {
            self.current_frame.set(self.data().len());
        }

        let num_words = func_stack_size.div_ceil(Self::MAX_ALIGN);

        unsafe {
            let data = &mut *self.data.get();

            data.extend((0..num_words).map(|_| MaybeUninit::zeroed()));
        }
    }

    /// Pops the current stack frame.
    pub fn pop_frame(&self) {
        let frame_end = self.current_frame.get();
        self.current_frame.set(
            self.previous_frames
                .borrow_mut()
                .pop()
                .expect("no stack frame to pop"),
        );
        unsafe {
            let data = &mut *self.data.get();
            data.truncate(frame_end / size_of::<Aligned16>());
        }
    }

    /// Load a value from the stack at the given offset
    /// from the current frame base.
    ///
    /// # Safety
    /// `offset` and `offset + size_of::<T>` must be in bounds,
    /// and the value stored in the stack must be a valid instance
    /// of `T`. Additionally, `offset + size_of::<T>` must be aligned
    /// to `align_of::<T>`.
    #[inline]
    pub unsafe fn load<T: Copy>(&self, offset: u32) -> T {
        self.load_absolute(self.current_frame.get() + usize::try_from(offset).unwrap())
    }

    /// # Safety
    /// `offset` and `offset + size_of::<T>` must be in bounds.
    /// Additionally, `offset + size_of::<T>` must be aligned
    /// to `align_of::<T>`.
    #[inline]
    pub unsafe fn store<T: Copy>(&self, offset: u32, value: T) {
        self.store_absolute(
            self.current_frame.get() + usize::try_from(offset).unwrap(),
            value,
        );
    }

    #[inline]
    pub unsafe fn load_absolute<T: Copy>(&self, offset: usize) -> T {
        const {
            assert!(align_of::<T>() <= Self::MAX_ALIGN, "alignment too large",);
        }

        debug_assert!(offset <= self.data().len());
        debug_assert!(offset + size_of::<T>() <= self.data().len());
        debug_assert!(offset % align_of::<T>() == 0);

        let ptr = self.data().as_ptr().add(offset);
        ptr.cast::<T>().read()
    }

    #[inline]
    pub unsafe fn store_absolute<T: Copy>(&self, offset: usize, value: T) {
        const {
            assert!(align_of::<T>() <= Self::MAX_ALIGN, "alignment too large",);
        }

        debug_assert!(
            offset <= self.data().len(),
            "{offset} > {}",
            self.data().len()
        );
        debug_assert!(
            offset + size_of::<T>() <= self.data().len(),
            "{} > {} (type {})",
            offset + size_of::<T>(),
            self.data().len(),
            type_name::<T>()
        );
        debug_assert!(offset % align_of::<T>() == 0);

        let ptr = self.data_mut().as_mut_ptr().add(offset);
        ptr.cast::<T>().write(value);
    }

    /// Gets the offset in the stack of the given frame,
    /// where frame 0 is the current frame.
    pub fn frame_offset(&self, i: usize) -> Option<usize> {
        if i == 0 {
            Some(self.current_frame.get())
        } else {
            let frames = self.previous_frames.borrow();
            let i = i - 1;
            if i < frames.len() {
                Some(frames[frames.len() - i - 1])
            } else {
                None
            }
        }
    }

    /// Copies a value from one offset in the stack to another.
    ///
    /// # Safety
    /// The offsets must be in bounds and the sizes must be in bounds.
    pub unsafe fn copy(&self, src_offset: u32, dst_offset: u32, size: u32) {
        let src_offset = self.current_frame.get() + usize::try_from(src_offset).unwrap();
        let dst_offset = self.current_frame.get() + usize::try_from(dst_offset).unwrap();

        self.copy_absolute(src_offset, dst_offset, size)
    }

    /// Copies a value from the current stack frame into the previous stack frame.
    ///
    /// `src_offset` is relative to the current frame base,
    /// while `dst_offset` is relative to the parent frame base.
    ///
    /// # Safety
    /// The offsets must be in bounds and the sizes must be in bounds.
    pub unsafe fn copy_to_caller(&self, src_offset: u32, dst_offset: u32, size: u32) {
        let caller_offset = self.previous_frames.borrow().last().copied().unwrap();
        let src_offset = self.current_frame.get() + usize::try_from(src_offset).unwrap();
        let dst_offset = caller_offset + usize::try_from(dst_offset).unwrap();

        self.copy_absolute(src_offset, dst_offset, size);
    }

    /// Copies a value from the previous stack frame into the current stack frame.
    ///
    /// `src_offset` is relative to the parent frame base,
    /// while `dst_offset` is relative to the current frame base.
    ///
    /// # Safety
    /// The offsets must be in bounds and the sizes must be in bounds.
    pub unsafe fn copy_from_caller(&self, src_offset: u32, dst_offset: u32, size: u32) {
        let caller_offset = self.previous_frames.borrow().last().copied().unwrap();
        let src_offset = caller_offset + usize::try_from(src_offset).unwrap();
        let dst_offset = self.current_frame.get() + usize::try_from(dst_offset).unwrap();

        self.copy_absolute(src_offset, dst_offset, size);
    }

    unsafe fn copy_absolute(&self, src_offset: usize, dst_offset: usize, size: u32) {
        debug_assert!(
            src_offset < self.data().len()
                && src_offset + usize::try_from(size).unwrap() < self.data().len()
        );
        debug_assert!(
            dst_offset < self.data().len()
                && dst_offset + usize::try_from(size).unwrap() < self.data().len()
        );
        let data = self.data_mut();
        ptr::copy(
            data.as_ptr().add(src_offset),
            data.as_mut_ptr().add(dst_offset),
            size as usize,
        );
    }

    pub unsafe fn get_pointer_absolute(&self, offset: usize) -> *const u8 {
        self.data().as_ptr().add(offset).cast()
    }

    /// Gets the data as bytes.
    ///
    /// # Safety
    /// Calling operations that may cause `self.data`
    /// to reallocate invalidates the returned reference.
    #[inline]
    unsafe fn data(&self) -> &[MaybeUninit<u8>] {
        let vec = &*self.data.get();
        slice::from_raw_parts(vec.as_ptr().cast(), vec.len() * size_of::<Aligned16>())
    }

    /// Gets the data as bytes.
    ///
    /// # Safety
    /// No access to `self.data` is allowed while the returned
    /// reference is live.
    #[inline]
    #[allow(clippy::mut_from_ref)] // private method
    unsafe fn data_mut(&self) -> &mut [MaybeUninit<u8>] {
        let vec = &mut *self.data.get();
        slice::from_raw_parts_mut(vec.as_mut_ptr().cast(), vec.len() * size_of::<Aligned16>())
    }
}
