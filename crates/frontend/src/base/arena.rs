use crate::{
    base::Session,
    utils::bump::{DropBumpListInterner, DropBumpPtr, DropBumpValueInterner},
};
use clay_core::FastHashMap;
use derive_where::derive_where;
use hashbrown::hash_map;
use late_struct::{LateField, LateInstance};
use std::{
    any::{Any, TypeId},
    cell::RefCell,
    fmt, hash,
    ptr::NonNull,
};

// === Obj === //

#[derive_where(Copy, Clone, Hash, Eq, PartialEq)]
pub struct Obj<T: ?Sized + 'static> {
    raw: DropBumpPtr<T>,
}

impl<T> fmt::Debug for Obj<T>
where
    T: ?Sized + 'static + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        thread_local! {
            static REENTRANT_FMT: RefCell<FastHashMap<(TypeId, NonNull<()>), u32>> =
                RefCell::new(FastHashMap::default());
        }

        let key = (TypeId::of::<T>(), self.raw.ptr().cast());

        let (reentrant_depth, was_non_reentrant) = REENTRANT_FMT.with_borrow_mut(|map| {
            let len = map.len();

            match map.entry(key) {
                hash_map::Entry::Occupied(entry) => (*entry.get(), false),
                hash_map::Entry::Vacant(entry) => (*entry.insert(len as u32), true),
            }
        });

        write!(f, "{reentrant_depth}")?;

        if was_non_reentrant {
            let _guard = scopeguard::guard((), |()| {
                REENTRANT_FMT.with_borrow_mut(|v| v.remove(&key));
            });

            f.write_str(": ")?;
            self.r(&Session::fetch()).fmt(f)
        } else {
            Ok(())
        }
    }
}

impl<T: 'static> Obj<T> {
    pub fn new(value: T, s: &Session) -> Self
    where
        T: Sized,
    {
        Self {
            raw: DropBumpPtr::new(value, &s.drop_bump),
        }
    }
}

impl<T: 'static> Obj<[T]> {
    pub fn new_empty(s: &Session) -> Self {
        Self {
            raw: DropBumpPtr::new_list_empty(&s.drop_bump),
        }
    }

    pub fn new_iter(values: impl IntoIterator<Item = T>, s: &Session) -> Self {
        Self {
            raw: DropBumpPtr::new_iter(values, &s.drop_bump, &s.scratch_bump),
        }
    }

    pub fn new_iter_with(len: usize, f: impl FnMut(usize) -> T, s: &Session) -> Self {
        Self {
            raw: DropBumpPtr::new_iter_with(len, f, &s.drop_bump),
        }
    }

    pub fn new_slice_clone(values: &[T], s: &Session) -> Self
    where
        T: Clone,
    {
        Self {
            raw: DropBumpPtr::new_slice_clone(values, &s.drop_bump),
        }
    }

    pub fn new_slice_copy(values: &[T], s: &Session) -> Self
    where
        T: Copy,
    {
        Self {
            raw: DropBumpPtr::new_slice_copy(values, &s.drop_bump),
        }
    }
}

impl<T: ?Sized + 'static> Obj<T> {
    pub fn wrap(raw: DropBumpPtr<T>) -> Self {
        Self { raw }
    }

    pub fn raw(self) -> DropBumpPtr<T> {
        self.raw
    }

    pub fn map<V: ?Sized>(self, f: impl FnOnce(&T) -> &V, s: &Session) -> Obj<V> {
        Obj {
            raw: self.raw.map(f, &s.drop_bump),
        }
    }

    pub fn r(self, s: &Session) -> &T {
        self.raw.r(&s.drop_bump)
    }
}

// === Intern === //

#[derive(Default)]
pub struct SessionInterners {
    raw: LateInstance<Self>,
}

late_struct::late_struct!(
    SessionInterners => dyn Any
);

pub trait ValueInternable:
    'static
    + Sized
    + Eq
    + hash::Hash
    + Clone
    + LateField<SessionInterners, Value = DropBumpValueInterner<Self>>
{
    fn intern(self, s: &Session) -> Intern<Self> {
        Intern::new(self, s)
    }
}

pub trait ListInternable:
    'static
    + Sized
    + Eq
    + hash::Hash
    + Clone
    + LateField<SessionInterners, Value = DropBumpListInterner<Self>>
{
}

pub trait IterInternExt: Sized + IntoIterator<Item: ListInternable> {
    fn intern(self, s: &Session) -> Intern<[Self::Item]>;
}

impl<I: IntoIterator<Item: ListInternable>> IterInternExt for I {
    fn intern(self, s: &Session) -> Intern<[Self::Item]> {
        Intern::new_iter(self, s)
    }
}

#[derive_where(Copy, Clone, Hash, Eq, PartialEq)]
#[repr(transparent)]
pub struct Intern<T: ?Sized + 'static> {
    inner: Obj<T>,
}

impl<T: ?Sized + 'static + fmt::Debug> fmt::Debug for Intern<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<T: ValueInternable> Intern<T> {
    pub fn new(value: T, s: &Session) -> Self {
        let obj = s.interners.raw.get::<T>().intern(value, &s.drop_bump);
        Self::wrap_unchecked(Obj::wrap(obj))
    }
}

impl<T: ListInternable> Intern<[T]> {
    pub fn new_empty(s: &Session) -> Self {
        Self::wrap_unchecked(Obj::new_empty(s))
    }

    pub fn new_iter(values: impl IntoIterator<Item = T>, s: &Session) -> Self {
        let obj = s
            .interners
            .raw
            .get::<T>()
            .intern_iter(values, &s.drop_bump, &s.scratch_bump);

        Self::wrap_unchecked(Obj::wrap(obj))
    }

    pub fn new_slice_clone(values: &[T], s: &Session) -> Self {
        let obj = s
            .interners
            .raw
            .get::<T>()
            .intern_slice_clone(values, &s.drop_bump);

        Self::wrap_unchecked(Obj::wrap(obj))
    }

    pub fn new_slice_copy(values: &[T], s: &Session) -> Self
    where
        T: Copy,
    {
        let obj = s
            .interners
            .raw
            .get::<T>()
            .intern_slice_copy(values, &s.drop_bump);

        Self::wrap_unchecked(Obj::wrap(obj))
    }

    pub fn extend(self, s: &Session, values: impl IntoIterator<Item = T>) -> Self {
        Self::new_iter(self.r(s).iter().cloned().chain(values), s)
    }

    pub fn truncate_to_len_clone(self, s: &Session, len: usize) -> Self {
        Self::new_slice_clone(&self.r(s)[..len], s)
    }

    pub fn truncate_to_len_copy(self, s: &Session, len: usize) -> Self
    where
        T: Copy,
    {
        Self::new_slice_copy(&self.r(s)[..len], s)
    }

    pub fn map<V: ListInternable>(self, s: &Session, f: impl FnMut(T) -> V) -> Intern<[V]> {
        Intern::new_iter(self.r(s).iter().cloned().map(f), s)
    }
}

impl<T: ?Sized + 'static> Intern<T> {
    pub fn wrap_unchecked(inner: Obj<T>) -> Self {
        Self { inner }
    }

    pub fn unwrap(self) -> Obj<T> {
        self.inner
    }

    pub fn r(self, s: &Session) -> &T {
        self.inner.r(s)
    }
}

#[doc(hidden)]
pub mod internable_internals {
    pub use super::{ListInternable, SessionInterners, ValueInternable};
    pub use crate::utils::bump::{DropBumpListInterner, DropBumpValueInterner};
    pub use late_struct::late_field;
}

#[macro_export]
macro_rules! value_internable {
    ($($ty:ty),*$(,)?) => {$(
        $crate::base::internable_internals::late_field! {
            $ty [$crate::base::internable_internals::SessionInterners] =>
                $crate::base::internable_internals::DropBumpValueInterner<Self>
        }

        impl $crate::base::internable_internals::ValueInternable for $ty {}
    )*};
}

pub use value_internable;

#[macro_export]
macro_rules! list_internable {
    ($($ty:ty),*$(,)?) => {$(
        $crate::base::internable_internals::late_field! {
            $ty [$crate::base::internable_internals::SessionInterners] =>
                $crate::base::internable_internals::DropBumpListInterner<Self>
        }

        impl $crate::base::internable_internals::ListInternable for $ty {}
    )*};
}

pub use list_internable;
