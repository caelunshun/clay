use bumpalo::Bump;
use derive_where::derive_where;
use std::{
    marker::PhantomData,
    num::NonZeroU64,
    ptr::{self, NonNull},
    sync::atomic::{AtomicU64, Ordering::*},
};

#[derive(Debug)]
pub struct GhostHeap<'m> {
    _ty: PhantomData<fn(&'m ())>,
    bump: Bump,
    uid: NonZeroU64,
}

unsafe impl Send for GhostHeap<'_> {}
unsafe impl Sync for GhostHeap<'_> {}

impl Default for GhostHeap<'_> {
    fn default() -> Self {
        static UID_GEN: AtomicU64 = AtomicU64::new(1);

        Self {
            _ty: PhantomData,
            bump: Default::default(),
            uid: NonZeroU64::new(UID_GEN.fetch_add(1, Relaxed)).unwrap(),
        }
    }
}

impl<'m> GhostHeap<'m> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn acquire_mut<R>(
        &mut self,
        f: impl for<'g> FnOnce(&mut GhostArenaAcquired<'g, 'm>) -> R,
    ) -> R {
        f(unsafe { &mut *(self as *mut GhostHeap as *mut GhostArenaAcquired<'_, 'm>) })
    }

    pub fn acquire_ref<R>(&self, f: impl for<'g> FnOnce(&GhostArenaAcquired<'g, 'm>) -> R) -> R {
        f(unsafe { &*(self as *const GhostHeap as *const GhostArenaAcquired<'_, 'm>) })
    }
}

#[repr(transparent)]
pub struct GhostArenaAcquired<'g, 'm> {
    _marker: PhantomData<fn(&'g ()) -> &'g ()>,
    arena: GhostHeap<'m>,
}

#[derive_where(Copy, Clone)]
pub struct GhostPtr<'g, T: ?Sized + GhostPointee<'g>> {
    _marker: PhantomData<fn(&'g ()) -> &'g ()>,
    ptr: NonNull<T>,
}

unsafe impl<'g, T: ?Sized + GhostPointee<'g>> Send for GhostPtr<'g, T> {}
unsafe impl<'g, T: ?Sized + GhostPointee<'g>> Sync for GhostPtr<'g, T> {}

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

    pub fn liberate(self, ar: &GhostArenaAcquired<'g, '_>) -> DynGhostPtr<T::ForLt<'static>> {
        DynGhostPtr {
            uid: ar.arena.uid,
            ptr: recast_ptr(self.ptr),
        }
    }
}

pub unsafe trait GhostPointee<'g>: Send + Sync {
    type ForLt<'new_g>: ?Sized
        + for<'possible_g> GhostPointee<'new_g, ForLt<'possible_g> = Self::ForLt<'possible_g>>;
}

unsafe impl<'g, T> GhostPointee<'g> for [T]
where
    T: GhostPointee<'g> + Sized,
    for<'new_g> T::ForLt<'new_g>: Sized,
{
    type ForLt<'new_g> = [T::ForLt<'new_g>];
}

unsafe impl<'g, T> GhostPointee<'g> for GhostPtr<'g, T>
where
    T: GhostPointee<'g>,
    for<'new_g> T::ForLt<'new_g>: Sized,
{
    type ForLt<'new_g> = GhostPtr<'new_g, T::ForLt<'new_g>>;
}

fn recast_ptr<'a, 'b, T>(ptr: NonNull<T>) -> NonNull<T::ForLt<'b>>
where
    T: ?Sized + GhostPointee<'a>,
{
    unsafe { ptr::read(&ptr as *const NonNull<T> as *const NonNull<_>) }
}

#[derive_where(Copy, Clone)]
pub struct DynGhostPtr<T: ?Sized + GhostPointee<'static>> {
    uid: NonZeroU64,
    ptr: NonNull<T>,
}

unsafe impl<T: ?Sized + GhostPointee<'static>> Send for DynGhostPtr<T> {}
unsafe impl<T: ?Sized + GhostPointee<'static>> Sync for DynGhostPtr<T> {}

impl<T: ?Sized + GhostPointee<'static>> DynGhostPtr<T> {
    pub fn rejoin<'g>(self, ar: &GhostArenaAcquired<'g, '_>) -> GhostPtr<'g, T::ForLt<'g>> {
        assert_eq!(self.uid, ar.arena.uid);

        GhostPtr {
            _marker: PhantomData,
            ptr: recast_ptr(self.ptr),
        }
    }
}
