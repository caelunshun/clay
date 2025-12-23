use derive_where::derive_where;
use polonius_the_crab::{polonius, polonius_return};
use std::{
    cell::{Ref, RefCell},
    fmt,
    rc::Rc,
};

#[derive_where(Clone)]
pub struct StealRc<T>(Rc<RefCell<Option<T>>>);

impl<T: fmt::Debug> fmt::Debug for StealRc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(value) = self.try_get() {
            value.fmt(f)
        } else {
            f.write_str("<stolen>")
        }
    }
}

impl<T: Default> Default for StealRc<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T> StealRc<T> {
    pub fn new(value: T) -> Self {
        Self(Rc::new(RefCell::new(Some(value))))
    }

    pub fn try_get(&self) -> Option<Ref<'_, T>> {
        Ref::filter_map(self.0.borrow(), |v| v.as_ref()).ok()
    }

    #[track_caller]
    pub fn get(&self) -> Ref<'_, T> {
        self.try_get().expect("already stolen")
    }

    pub fn try_unique(&mut self) -> Option<&mut T> {
        let mut this = &mut *self;

        polonius!(|this| -> Option<&'polonius mut T> {
            if let Some(unique) = Rc::get_mut(&mut this.0) {
                polonius_return!(unique.get_mut().as_mut());
            }
        });

        let stolen = this.0.borrow_mut().take()?;

        this.0 = Rc::new(RefCell::new(Some(stolen)));

        Some(
            Rc::get_mut(&mut this.0)
                .unwrap()
                .get_mut()
                .as_mut()
                .unwrap(),
        )
    }

    #[track_caller]
    pub fn unique(&mut self) -> &mut T {
        self.try_unique().expect("already stolen")
    }

    #[must_use]
    pub fn try_steal(self) -> Option<T> {
        match Rc::try_unwrap(self.0) {
            Ok(unique) => unique.into_inner(),
            Err(shared) => shared.borrow_mut().take(),
        }
    }

    #[track_caller]
    pub fn steal(self) -> T {
        self.try_steal().expect("already stolen")
    }
}
