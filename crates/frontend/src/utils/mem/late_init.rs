use std::{
    cell::{Cell, UnsafeCell},
    fmt,
    mem::MaybeUninit,
    ops::Deref,
};

pub struct LateInit<T> {
    is_init: Cell<bool>,
    cell: UnsafeCell<MaybeUninit<T>>,
}

impl<T: fmt::Debug> fmt::Debug for LateInit<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(value) = Self::get(self) {
            value.fmt(f)
        } else {
            f.write_str("<uninit>")
        }
    }
}

impl<T: Clone> Clone for LateInit<T> {
    fn clone(&self) -> Self {
        if let Some(value) = Self::get(self) {
            Self::new(value.clone())
        } else {
            Self::uninit()
        }
    }
}

impl<T> From<T> for LateInit<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T> LateInit<T> {
    pub const fn new(value: T) -> Self {
        Self {
            is_init: Cell::new(true),
            cell: UnsafeCell::new(MaybeUninit::new(value)),
        }
    }

    pub const fn uninit() -> Self {
        Self {
            is_init: Cell::new(false),
            cell: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    pub fn init(me: &Self, value: T) -> &T {
        // Ensure that the cell is only initialized once.
        if me.is_init.get() {
            panic!("cannot initialize `LateInit` more than once");
        }

        // Initialize the cell.
        unsafe { *me.cell.get() = MaybeUninit::new(value) };

        // Mark the cell as initialized.
        me.is_init.set(true);

        unsafe { (*me.cell.get()).assume_init_ref() }
    }

    pub fn get(me: &Self) -> Option<&T> {
        me.is_init
            .get()
            .then(|| unsafe { (*me.cell.get()).assume_init_ref() })
    }
}

impl<T> Deref for LateInit<T> {
    type Target = T;

    #[track_caller]
    fn deref(&self) -> &Self::Target {
        Self::get(self).expect("cell not initialized")
    }
}

impl<T> Drop for LateInit<T> {
    fn drop(&mut self) {
        if self.is_init.get() {
            unsafe { self.cell.get_mut().assume_init_drop() }
        }
    }
}
