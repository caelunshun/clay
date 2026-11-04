use bumpalo::Bump;
use std::cell::RefCell;

#[derive(Default)]
pub struct ScratchBump {
    bump: RefCell<Bump>,
}

impl ScratchBump {
    pub fn acquire<R>(&self, f: impl FnOnce(&Bump) -> R) -> R {
        // N.B. we create the cleanup guard before the immutable borrow guard to ensure the borrow
        // expires before cleanup.
        let _guard = scopeguard::guard((), |()| {
            if let Ok(mut bump) = self.bump.try_borrow_mut() {
                bump.reset();
            }
        });

        f(&self.bump.borrow())
    }
}
