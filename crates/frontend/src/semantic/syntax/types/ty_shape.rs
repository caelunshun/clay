use crate::{
    base::{
        arena::{Intern, Obj},
        syntax::Symbol,
    },
    semantic::syntax::{AdtItem, Mutability, SimpleTyKind, TraitItem},
};

pub type TyShapeList = Intern<[TyShape]>;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum TyShape {
    Hole,
    Solid(SolidTyShape),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct SolidTyShape {
    pub kind: SolidTyShapeKind,
    pub children: TyShapeList,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum SolidTyShapeKind {
    /// A top-level impl-cache type indicating the implementation of a trait.
    ///
    /// The type's children are organized into two parts:
    ///
    /// - The first child is the target type.
    /// - The remaining `trait_def.regular_generic_count` child types (minus the number of region
    ///   generics) represent the trait arguments.
    ///
    TraitImpl(Obj<TraitItem>),

    /// A top-level impl-cache type indicating the implementation of a specific method in an inherent
    /// `impl` block. This type has exactly one child type indicating the *receiver target*.
    InherentMethodImpl(Symbol),

    /// A top-level impl-cache type indicating the implementation of a specific associated function
    /// in an inherent `impl` block. This type has exactly one child type indicating the *self
    /// type*.
    InherentFunctionImpl(Symbol),

    Simple(SimpleTyKind),
    Reference(Mutability),
    Adt(Obj<AdtItem>),
    Trait,
    Tuple(u32),

    /// No need to specialize in an efficient manner because `impl`s naming these types are not
    /// possible.
    FnDef,
}
