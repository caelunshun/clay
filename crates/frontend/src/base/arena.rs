use crate::{
    base::{HasSession, Session},
    utils::hash::{FxBuildHasher, FxHashMap, FxHashSet, hash_map},
};
use bumpalo::Bump;
use derive_where::derive_where;
use std::{
    any::{Any, TypeId},
    cell::{Cell, RefCell, UnsafeCell},
    fmt,
    hash::{self, BuildHasher as _, BuildHasherDefault},
    mem::MaybeUninit,
    num::NonZeroU64,
    ops::Deref,
    ptr::NonNull,
    sync::atomic::{AtomicU64, Ordering::*},
};

// === GpArena === //

pub struct GpArena {
    generation: NonZeroU64,
    bump: bumpalo::Bump,
    drop_queue: RefCell<GpArenaDropQueue>,
}

struct GpArenaDropQueue {
    singles: Vec<NonNull<dyn Any>>,
    lists: Vec<GpList>,
}

#[derive(Copy, Clone)]
struct GpList {
    base: NonNull<()>,
    len: usize,
    drop: unsafe fn(NonNull<()>, usize),
}

impl fmt::Debug for GpArena {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("GpArena").finish_non_exhaustive()
    }
}

impl Default for GpArena {
    fn default() -> Self {
        static ID_GEN: AtomicU64 = AtomicU64::new(1);

        Self {
            generation: NonZeroU64::new(ID_GEN.fetch_add(1, Relaxed)).unwrap(),
            bump: Bump::new(),
            drop_queue: RefCell::new(GpArenaDropQueue {
                singles: Vec::new(),
                lists: Vec::new(),
            }),
        }
    }
}

impl Drop for GpArena {
    fn drop(&mut self) {
        let inner = self.drop_queue.get_mut();

        for &single in &inner.singles {
            unsafe { single.drop_in_place() };
        }

        for &GpList { base, len, drop } in &inner.lists {
            unsafe { drop(base, len) };
        }
    }
}

#[derive_where(Copy, Clone, Hash, Eq, PartialEq)]
pub struct Obj<T: ?Sized + 'static> {
    generation: NonZeroU64,
    ptr: NonNull<T>,
}

impl<T> fmt::Debug for Obj<T>
where
    T: ?Sized + 'static + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        thread_local! {
            static REENTRANT_FMT: RefCell<FxHashSet<(TypeId, NonNull<()>)>> =
                const { RefCell::new(FxHashSet::with_hasher(BuildHasherDefault::new())) };
        }

        let key = (TypeId::of::<T>(), self.ptr.cast());

        write!(f, "{:?}", self.ptr.as_ptr().cast::<()>())?;

        if REENTRANT_FMT.with_borrow_mut(|v| v.insert(key)) {
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
        let this = &s.gp_arena;
        let ptr = NonNull::from(this.bump.alloc(value));

        this.drop_queue.borrow_mut().singles.push(ptr);

        Self {
            generation: this.generation,
            ptr,
        }
    }
}

impl<T: 'static> Obj<[T]> {
    pub fn new_slice(value: &[T], s: &Session) -> Self
    where
        T: Clone,
    {
        let this = &s.gp_arena;
        let ptr = NonNull::from(this.bump.alloc_slice_clone(value));

        this.drop_queue.borrow_mut().lists.push(GpList {
            base: ptr.cast(),
            len: ptr.len(),
            drop: |ptr, len| unsafe {
                NonNull::slice_from_raw_parts(ptr.cast::<T>(), len).drop_in_place();
            },
        });

        Self {
            generation: this.generation,
            ptr,
        }
    }

    pub fn new_iter(
        value: impl IntoIterator<Item = T, IntoIter: ExactSizeIterator>,
        s: &Session,
    ) -> Self {
        let this = &s.gp_arena;

        let ptr = NonNull::from(this.bump.alloc_slice_fill_iter(value));

        this.drop_queue.borrow_mut().lists.push(GpList {
            base: ptr.cast(),
            len: ptr.len(),
            drop: |ptr, len| unsafe {
                NonNull::slice_from_raw_parts(ptr.cast::<T>(), len).drop_in_place();
            },
        });

        Self {
            generation: this.generation,
            ptr,
        }
    }
}

impl<T: ?Sized + 'static> Obj<T> {
    pub fn map<V: ?Sized>(self, f: impl FnOnce(&T) -> &V, s: &Session) -> Obj<V> {
        Obj {
            generation: self.generation,
            ptr: NonNull::from(f(self.r(s))),
        }
    }

    pub fn r(self, s: &Session) -> &T {
        assert_eq!(s.gp_arena.generation, self.generation);
        unsafe { self.ptr.as_ref() }
    }
}

// === Intern === //

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

// === Interner === //

pub trait HasInterner<T: 'static + hash::Hash + Eq>: HasSession {
    fn interner(&self) -> &Interner<T>;

    fn intern(&self, value: T) -> Intern<T> {
        self.interner().intern(value, self.session())
    }
}

#[derive_where(Default)]
pub struct Interner<T: 'static> {
    interns: RefCell<FxHashMap<(Intern<T>, u64), ()>>,
}

impl<T: 'static> fmt::Debug for Interner<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Interner").finish_non_exhaustive()
    }
}

impl<T> Interner<T>
where
    T: 'static + hash::Hash + Eq,
{
    pub fn intern(&self, value: T, s: &Session) -> Intern<T> {
        let mut interns = self.interns.borrow_mut();
        let hash = FxBuildHasher::default().hash_one(&value);

        match interns
            .raw_entry_mut()
            .from_hash(hash, |(other, other_hash)| {
                hash == *other_hash && &value == other.r(s)
            }) {
            hash_map::RawEntryMut::Occupied(entry) => entry.key().0,
            hash_map::RawEntryMut::Vacant(entry) => {
                let value = Intern::wrap_unchecked(Obj::new(value, s));
                entry.insert_with_hasher(hash, (value, hash), (), |(_, hash)| *hash);
                value
            }
        }
    }
}

// === ListInterner === //

pub trait HasListInterner<T: 'static + hash::Hash + Eq + Clone>: HasSession {
    fn interner(&self) -> &ListInterner<T>;

    fn intern_list(&self, values: &[T]) -> Intern<[T]>
    where
        T: Clone,
    {
        self.interner().intern_list(values, self.session())
    }
}

#[derive_where(Default)]
pub struct ListInterner<T: 'static> {
    #[expect(clippy::type_complexity)]
    interns: RefCell<FxHashMap<(Intern<[T]>, u64), ()>>,
}

impl<T: 'static> fmt::Debug for ListInterner<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ListInterner").finish_non_exhaustive()
    }
}

impl<T> ListInterner<T>
where
    T: 'static + hash::Hash + Eq,
{
    pub fn intern_list(&self, values: &[T], s: &Session) -> Intern<[T]>
    where
        T: Clone,
    {
        let mut interns = self.interns.borrow_mut();
        let hash = FxBuildHasher::default().hash_one(values);

        match interns
            .raw_entry_mut()
            .from_hash(hash, |(other, other_hash)| {
                hash == *other_hash && values == other.r(s)
            }) {
            hash_map::RawEntryMut::Occupied(entry) => entry.key().0,
            hash_map::RawEntryMut::Vacant(entry) => {
                let values = Intern::wrap_unchecked(Obj::new_slice(values, s));
                entry.insert_with_hasher(hash, (values, hash), (), |(_, hash)| *hash);
                values
            }
        }
    }
}

// === LateInit === //

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
