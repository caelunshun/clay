use derive_where::derive_where;
use std::{convert::Infallible, fmt, mem, ops::Deref, ptr::NonNull, rc::Rc};

pub fn try_map_rc_same_addr<I: ?Sized, O: ?Sized, E>(
    rc: Rc<I>,
    map: impl for<'a> FnOnce(&'a I) -> Result<&'a O, E>,
) -> Result<Rc<O>, (Rc<I>, E)> {
    let orig = Rc::into_raw(rc);
    let mapped = match map(unsafe { &*orig }) {
        Ok(mapped) => mapped,
        Err(err) => return Err((unsafe { Rc::from_raw(orig) }, err)),
    };

    // Ensure that the layout of the dropped pointee remains the same.
    assert_eq!(orig as *const (), mapped as *const _ as *const ());
    assert_eq!(
        mem::size_of_val(unsafe { &*orig }),
        mem::size_of_val(mapped)
    );

    Ok(unsafe {
        // Safety:
        //
        // a) The `map` function used to construct this `MappedRc` guarantees statically that the
        //    output reference can live as long as a reference to the pointee lives.
        //
        // b) Although `Rc` may be dropping a different type to the one it originally contained,
        //    the pointer and size of the dropped object remains the same, ensuring that the
        //    deallocation call will still be valid.
        //
        Rc::from_raw(mapped)
    })
}

#[derive_where(Clone)]
pub struct MappedRc<O: ?Sized, T: ?Sized> {
    original: Rc<O>,
    mapped: NonNull<T>,
}

impl<O: ?Sized, T: ?Sized> MappedRc<O, T> {
    pub unsafe fn new_unchecked(original: Rc<O>, mapped: NonNull<T>) -> Self {
        Self { original, mapped }
    }

    pub fn try_new<E>(
        original: Rc<O>,
        map: impl for<'a> FnOnce(&'a O) -> Result<&'a T, E>,
    ) -> Result<Self, (Rc<O>, E)> {
        let mapped = match map(&*original) {
            Ok(mapped) => mapped,
            Err(err) => return Err((original, err)),
        };
        let mapped = NonNull::from(mapped);

        Ok(Self { original, mapped })
    }

    pub fn new(original: Rc<O>, map: impl for<'a> FnOnce(&'a O) -> &'a T) -> Self {
        let Ok(res) = Self::try_new(original, |v| Result::<_, Infallible>::Ok(map(v)));
        res
    }

    pub fn original(me: &Self) -> &Rc<O> {
        &me.original
    }

    pub fn into_original(me: Self) -> Rc<O> {
        me.original
    }

    pub fn try_map_original<O2: ?Sized, E>(
        me: Self,
        map: impl for<'a> FnOnce(&'a O) -> Result<&'a O2, E>,
    ) -> Result<MappedRc<O2, T>, (MappedRc<O, T>, E)> {
        match try_map_rc_same_addr(me.original, map) {
            Ok(original) => Ok(MappedRc {
                original,
                mapped: me.mapped,
            }),
            Err((original, err)) => Err((
                MappedRc {
                    original,
                    mapped: me.mapped,
                },
                err,
            )),
        }
    }

    pub fn map_original<O2: ?Sized>(
        me: Self,
        map: impl for<'a> FnOnce(&'a O) -> &'a O2,
    ) -> MappedRc<O2, T> {
        let Ok(res) = Self::try_map_original(me, |v| Result::<_, Infallible>::Ok(map(v)));
        res
    }

    pub fn try_map<T2: ?Sized, E>(
        me: Self,
        map: impl for<'a> FnOnce(&'a T) -> Result<&'a T2, E>,
    ) -> Result<MappedRc<O, T2>, (MappedRc<O, T>, E)> {
        match map(&*me) {
            Ok(mapped) => {
                let mapped = NonNull::from(mapped);

                Ok(MappedRc {
                    original: me.original,
                    mapped,
                })
            }
            Err(err) => Err((me, err)),
        }
    }

    pub fn map<T2: ?Sized>(me: Self, map: impl for<'a> FnOnce(&'a T) -> &'a T2) -> MappedRc<O, T2> {
        let Ok(res) = Self::try_map(me, |v| Result::<_, Infallible>::Ok(map(v)));
        res
    }
}

impl<O: ?Sized, T: ?Sized> Deref for MappedRc<O, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe {
            // Safety: the `map` function used to construct this `MappedRc` guarantees statically
            // that the output reference can live as long as a reference to the pointee lives.
            self.mapped.as_ref()
        }
    }
}

impl<O: ?Sized, T: ?Sized> AsRef<T> for MappedRc<O, T> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<O: ?Sized, T: ?Sized + fmt::Debug> fmt::Debug for MappedRc<O, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<O: ?Sized, T: ?Sized + fmt::Display> fmt::Display for MappedRc<O, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}
