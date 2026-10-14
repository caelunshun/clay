use crate::{adt_family::AdtTyFamily, arena::Arena};

/// Holds all IR structures for a program.
pub struct Soup {
    pub adt_ty_families: Arena<AdtTyFamily>,
}

macro_rules! impl_has_arena {
    ($($field:ident: $ty:ty),* $(,)?) => {
        $(
            impl $crate::arena::HasArena<$ty> for Soup {
                fn arena(&self) -> &Arena<$ty> {
                    &self.$field
                }
            }

            impl $crate::arena::HasArenaMut<$ty> for Soup {
                fn arena_mut(&mut self) -> &mut Arena<$ty> {
                    &mut self.$field
                }
            }
        )*
    }
}

impl_has_arena!(
    adt_ty_families: AdtTyFamily,
);
