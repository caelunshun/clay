use crate::{
    adt_family::AdtTyFamily, arena::Arena, brick::Brick, func_family::FuncFamily,
    trait_family::TraitFamily, trait_impl_family::TraitImplFamily, ty_param::TyParam,
};

/// Holds all IR structures for a program.
pub struct Soup {
    pub adt_ty_families: Arena<AdtTyFamily>,
    pub func_families: Arena<FuncFamily>,
    pub trait_families: Arena<TraitFamily>,
    pub trait_impl_families: Arena<TraitImplFamily>,
    pub ty_params: Arena<TyParam>,
    pub bricks: Arena<Brick>,
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
    func_families: FuncFamily,
    trait_families: TraitFamily,
    trait_impl_families: TraitImplFamily,
    ty_params: TyParam,
    bricks: Brick,
);
