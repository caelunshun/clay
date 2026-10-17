use bumpalo::Bump;
use derive_where::derive_where;
use std::{
    marker::PhantomData,
    num::{NonZero, NonZeroU64},
    ptr::{self, NonNull},
    sync::atomic::{AtomicU64, Ordering::*},
};

pub struct GhostArena<'m> {
    _ty: PhantomData<&'m ()>,
    bump: Bump,
    uid: NonZeroU64,
    head: Option<NonNull<GhostHeader>>,
}

#[derive(Copy, Clone)]
struct GhostHeader {
    value: NonNull<GhostHeader>,
}

impl GhostHeader {
    fn mark_needs_drop(&mut self) {
        self.value = self
            .value
            .map_addr(|v| unsafe { NonZero::new_unchecked(v.get() | 0b01) });
    }

    fn mark_condemned(&mut self) {
        self.value = self
            .value
            .map_addr(|v| unsafe { NonZero::new_unchecked(v.get() | 0b10) });
    }

    fn set_next(&mut self, ptr: NonNull<GhostHeader>) {
        assert!(ptr.addr().get().is_multiple_of(4));

        self.value = ptr.map_addr(|v| unsafe {
            NonZero::new_unchecked(v.get() | (self.value.addr().get() & 0b11))
        });
    }

    fn needs_drop(self) -> bool {
        self.value.addr().get() & 0b01 != 0
    }

    fn is_condemned(self) -> bool {
        self.value.addr().get() & 0b10 != 0
    }

    fn next(self) -> NonNull<GhostHeader> {
        self.value
            .map_addr(|v| unsafe { NonZero::new_unchecked(v.get() & !0b11) })
    }
}

#[repr(C)]
struct GhostValueWithDrop<T> {
    drop_fn: unsafe fn(NonNull<GhostValueWithDrop<()>>),
    inner: GhostValueWithoutDrop<T>,
}

#[repr(C)]
struct GhostValueWithoutDrop<T> {
    header: GhostHeader,
    value: T,
}

impl Default for GhostArena<'_> {
    fn default() -> Self {
        static UID_GEN: AtomicU64 = AtomicU64::new(1);

        Self {
            _ty: PhantomData,
            bump: Default::default(),
            uid: NonZeroU64::new(UID_GEN.fetch_add(1, Relaxed)).unwrap(),
            head: None,
        }
    }
}

impl<'m> GhostArena<'m> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn use_mut<F, R>(&mut self, f: F) -> R
    where
        F: for<'g> FnOnce(&mut GhostArenaAcquired<'g, 'm>) -> R,
    {
        f(unsafe { &mut *(self as *mut GhostArena as *mut GhostArenaAcquired<'_, 'm>) })
    }

    pub fn use_ref<F, R>(&self, f: F) -> R
    where
        F: for<'g> FnOnce(&GhostArenaAcquired<'g, 'm>) -> R,
    {
        f(unsafe { &*(self as *const GhostArena as *const GhostArenaAcquired<'_, 'm>) })
    }
}

#[repr(transparent)]
pub struct GhostArenaAcquired<'g, 'm> {
    _marker: PhantomData<fn(&'g ()) -> &'g ()>,
    arena: GhostArena<'m>,
}

#[derive_where(Copy, Clone)]
pub struct GhostPtr<'g, T: ?Sized + GhostPointee<'g>> {
    _marker: PhantomData<fn(&'g ()) -> &'g ()>,
    ptr: NonNull<T>,
}

impl<'g, T: ?Sized + GhostPointee<'g>> GhostPtr<'g, T> {
    pub fn new<'m>(value: T, ar: &mut GhostArenaAcquired<'g, 'm>) -> Self
    where
        T: Sized + 'm,
    {
        Self {
            _marker: PhantomData,
            ptr: NonNull::from(ar.arena.bump.alloc(value)),
        }
    }

    pub fn r<'a>(self, ar: &'a GhostArenaAcquired<'g, '_>) -> &'a T {
        _ = ar;
        unsafe { self.ptr.as_ref() }
    }

    pub fn m<'a>(mut self, ar: &'a mut GhostArenaAcquired<'g, '_>) -> &'a mut T {
        _ = ar;
        unsafe { self.ptr.as_mut() }
    }

    pub fn free(self, ar: &mut GhostArenaAcquired<'g, '_>) {
        todo!()
    }

    pub fn liberate(self, ar: &GhostArenaAcquired<'g, '_>) -> LiberatedGhostPtr<T::ForLt<'static>> {
        LiberatedGhostPtr {
            uid: ar.arena.uid,
            ptr: recast_ptr(self.ptr),
        }
    }
}

pub unsafe trait GhostPointee<'g> {
    type ForLt<'new_g>: ?Sized
        + for<'possible_g> GhostPointee<'new_g, ForLt<'possible_g> = Self::ForLt<'possible_g>>;
}

fn recast_ptr<'a, 'b, T>(ptr: NonNull<T>) -> NonNull<T::ForLt<'b>>
where
    T: ?Sized + GhostPointee<'a>,
{
    unsafe { ptr::read(&ptr as *const NonNull<T> as *const NonNull<_>) }
}

#[derive_where(Copy, Clone)]
pub struct LiberatedGhostPtr<T: ?Sized + GhostPointee<'static>> {
    uid: NonZeroU64,
    ptr: NonNull<T>,
}

impl<T: ?Sized + GhostPointee<'static>> LiberatedGhostPtr<T> {
    pub fn rejoin<'g>(self, ar: &GhostArenaAcquired<'g, '_>) -> GhostPtr<'g, T::ForLt<'g>> {
        assert_eq!(self.uid, ar.arena.uid);

        GhostPtr {
            _marker: PhantomData,
            ptr: recast_ptr(self.ptr),
        }
    }
}
