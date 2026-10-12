use std::{marker::PhantomData, slice};

#[derive(Default)]
pub struct VecOfPtrScratch {
    buffer: Vec<*mut ()>,
}

unsafe impl Send for VecOfPtrScratch {}
unsafe impl Sync for VecOfPtrScratch {}

impl VecOfPtrScratch {
    pub fn builder<'i, T: SizedPointer>(&'i mut self) -> VecOfPtrScratchBuilder<'i, T> {
        self.buffer.clear();

        VecOfPtrScratchBuilder {
            _ty: PhantomData,
            buffer: &mut self.buffer,
        }
    }

    pub fn build<T: SizedPointer>(&mut self, iter: impl IntoIterator<Item = T>) -> &mut [T] {
        let mut builder = self.builder();
        builder.extend(iter);
        builder.finish()
    }
}

pub struct VecOfPtrScratchBuilder<'a, T: SizedPointer> {
    _ty: PhantomData<Vec<T>>,
    buffer: &'a mut Vec<*mut ()>,
}

impl<'a, T: SizedPointer> VecOfPtrScratchBuilder<'a, T> {
    pub fn finish(self) -> &'a mut [T] {
        let buffer = self.buffer.as_mut_slice() as *mut [*mut ()];

        unsafe { slice::from_raw_parts_mut(buffer.cast::<()>().cast::<T>(), buffer.len()) }
    }
}

impl<'a, T: SizedPointer> Extend<T> for VecOfPtrScratchBuilder<'a, T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.buffer.extend(iter.into_iter().map(|v| v.as_ptr()));
    }
}

pub unsafe trait SizedPointer {
    fn as_ptr(self) -> *mut ();
}

unsafe impl<'a, T> SizedPointer for &'a T {
    fn as_ptr(self) -> *mut () {
        (self as *const T).cast::<()>().cast_mut()
    }
}

unsafe impl<'a, T> SizedPointer for &'a mut T {
    fn as_ptr(self) -> *mut () {
        (self as *mut T).cast()
    }
}
