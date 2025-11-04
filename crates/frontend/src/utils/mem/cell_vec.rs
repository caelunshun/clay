use derive_where::derive_where;
use std::{cell::RefCell, fmt, rc::Rc};

#[derive_where(Default)]
pub struct CellVec<T> {
    rc: RefCell<Rc<Vec<T>>>,
}

impl<T: fmt::Debug> fmt::Debug for CellVec<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.read().fmt(f)
    }
}

impl<T> Clone for CellVec<T> {
    fn clone(&self) -> Self {
        Self {
            rc: self.rc.clone(),
        }
    }
}

impl<T> CellVec<T> {
    pub fn new(vec: Vec<T>) -> Self {
        Self {
            rc: RefCell::new(Rc::new(vec)),
        }
    }

    pub fn read(&self) -> Rc<Vec<T>> {
        self.rc.borrow().clone()
    }

    pub fn mutate<R>(&self, f: impl FnOnce(&mut Vec<T>) -> R) -> R
    where
        T: Clone,
    {
        let mut guard = self.rc.borrow_mut();
        f(Rc::make_mut(&mut *guard))
    }
}
