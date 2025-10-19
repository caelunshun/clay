use std::{cell::Cell, ptr};

pub struct StackConsumer<'a, T> {
    target: &'a mut Vec<T>,
    remaining: Cell<*mut [T]>,
    truncate_to: Cell<usize>,
}

impl<'a, T> StackConsumer<'a, T> {
    pub fn new(target: &'a mut Vec<T>) -> Self {
        // N.B. We cannot access the vector beyond the call to `as_mut_ptr()` so our length read has
        // to happen before.
        let full_len = target.len();
        let remaining = ptr::slice_from_raw_parts_mut(target.as_mut_ptr(), full_len);

        Self {
            target,
            remaining: Cell::new(remaining),
            truncate_to: Cell::new(remaining.len()),
        }
    }
}

impl<T> StackConsumer<'_, T> {
    #[expect(clippy::mut_from_ref)]
    pub fn peek_many(&self, cnt: usize) -> Option<&mut [T]> {
        let remaining = self.remaining.get();

        let new_remaining = remaining.len().checked_sub(cnt)?;

        let cut = unsafe {
            &mut *ptr::slice_from_raw_parts_mut(remaining.cast::<T>().add(new_remaining), cnt)
        };

        self.remaining.set(ptr::slice_from_raw_parts_mut(
            remaining.cast::<T>(),
            new_remaining,
        ));

        Some(cut)
    }

    #[must_use]
    pub fn peek_array<const N: usize>(&self) -> Option<&mut [T; N]> {
        self.peek_many(N).map(|v| v.try_into().unwrap())
    }

    #[must_use]
    pub fn peek(&self) -> Option<&mut T> {
        let [v] = self.peek_array()?;
        Some(v)
    }

    #[must_use]
    pub fn peek_nth(&self, at: usize) -> Option<&mut T> {
        self.peek_many(at + 1).map(|v| &mut v[at])
    }

    pub fn pop_many(&self, cnt: usize) -> Option<&mut [T]> {
        debug_assert!(self.truncate_to.get() == self.remaining.get().len());

        let v = self.peek_many(cnt)?;
        self.truncate_to.set(self.remaining.get().len());
        Some(v)
    }

    #[must_use]
    pub fn pop_array<const N: usize>(&self) -> Option<&mut [T; N]> {
        self.pop_many(N).map(|v| v.try_into().unwrap())
    }

    #[must_use]
    pub fn pop(&self) -> Option<&mut T> {
        let [v] = self.pop_array()?;
        Some(v)
    }
}

impl<T> Drop for StackConsumer<'_, T> {
    fn drop(&mut self) {
        self.target.truncate(self.truncate_to.get());
    }
}
