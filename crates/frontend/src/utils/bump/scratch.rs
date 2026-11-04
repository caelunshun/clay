use bumpalo::Bump;
use std::{
    cell::{Ref, RefCell},
    mem::ManuallyDrop,
    ops::Deref,
};

#[derive(Default)]
pub struct ScratchBump {
    bump: RefCell<Bump>,
}

impl ScratchBump {
    pub fn acquire_guard(&self) -> ScratchBumpGuard<'_> {
        ScratchBumpGuard {
            scratch: self,
            guard: ManuallyDrop::new(self.bump.borrow()),
        }
    }

    pub fn acquire<R>(&self, f: impl FnOnce(&Bump) -> R) -> R {
        f(&self.acquire_guard())
    }
}

pub struct ScratchBumpGuard<'s> {
    scratch: &'s ScratchBump,
    guard: ManuallyDrop<Ref<'s, Bump>>,
}

impl Deref for ScratchBumpGuard<'_> {
    type Target = Bump;

    fn deref(&self) -> &Self::Target {
        &self.guard
    }
}

impl Drop for ScratchBumpGuard<'_> {
    fn drop(&mut self) {
        unsafe {
            ManuallyDrop::drop(&mut self.guard);
        }

        if let Ok(mut bump) = self.scratch.bump.try_borrow_mut() {
            bump.reset();
        }
    }
}
