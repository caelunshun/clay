use bumpalo::Bump;
use std::{
    cell::Cell,
    mem::{self, MaybeUninit},
    ops::Deref,
    ptr::NonNull,
    rc::Rc,
};

pub struct BumpRc<T: ?Sized> {
    header: NonNull<ElemHeader>,
    pointee: NonNull<T>,
}

struct ElemHeader {
    strong: Cell<usize>,
    bump: MaybeUninit<Rc<Bump>>,
    dtor: unsafe fn(NonNull<ElemHeader>),
}

#[repr(C)]
struct Elem<T> {
    header: ElemHeader,
    value: MaybeUninit<T>,
}

impl<T> BumpRc<T> {
    pub fn new(bump: Rc<Bump>, value: T) -> Self {
        let mut header = NonNull::from(bump.alloc(Elem {
            header: ElemHeader {
                strong: Cell::new(1),
                bump: MaybeUninit::uninit(),
                dtor: |ptr| unsafe {
                    // All projections are dead—we can get a mutable reference.
                    let ptr = ptr.cast::<Elem<T>>().as_mut();

                    // Drop the value in place.
                    MaybeUninit::assume_init_drop(&mut ptr.value);

                    // Take ownership of the `bump` and drop that to avoid deallocating the
                    // underlying bump while `ptr` is still live.
                    drop(MaybeUninit::assume_init_read(&ptr.header.bump));
                },
            },
            value: MaybeUninit::new(value),
        }));

        // Do all mutations before taking out immutable projections.
        unsafe { header.as_mut().header.bump = MaybeUninit::new(bump) };

        let pointee = NonNull::from(unsafe { header.as_ref().value.assume_init_ref() });

        Self {
            header: header.cast(),
            pointee,
        }
    }

    pub fn bump(me: &Self) -> &Rc<Bump> {
        unsafe { me.header.as_ref().bump.assume_init_ref() }
    }

    pub fn map<V: ?Sized>(me: Self, f: impl FnOnce(&T) -> &V) -> BumpRc<V> {
        let pointee = NonNull::from(f(&me));

        let mapped = BumpRc {
            header: me.header,
            pointee,
        };

        mem::forget(me);

        mapped
    }
}

impl<T: ?Sized> Deref for BumpRc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { self.pointee.as_ref() }
    }
}

impl<T: ?Sized> Clone for BumpRc<T> {
    fn clone(&self) -> Self {
        let header = unsafe { self.header.as_ref() };
        header.strong.set(
            header
                .strong
                .get()
                .checked_add(1)
                .expect("ref-count overflow"),
        );

        Self {
            header: self.header,
            pointee: self.pointee,
        }
    }
}

impl<T: ?Sized> Drop for BumpRc<T> {
    fn drop(&mut self) {
        let header = unsafe { self.header.as_ref() };
        header.strong.set(header.strong.get() - 1);

        if header.strong.get() > 0 {
            return;
        }

        let dtor = header.dtor;

        unsafe { dtor(self.header) };
    }
}
