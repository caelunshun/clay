use crate::{
    Func,
    ir::{AlgebraicType, AlgebraicTypeKind, FuncData, FuncHeader, Trait, TraitImpl},
};
use cranelift_entity::PrimaryMap;
use salsa::Database;

pub mod builder;

pub use builder::ContextBuilder;

pub trait ContextLike<'db> {
    fn resolve_adt(&self, db: &'db dyn Database, adt: AlgebraicTypeId) -> AlgebraicType<'db>;
    fn resolve_func(&self, db: &'db dyn Database, func: FuncId) -> Func<'db>;
    fn resolve_trait(&self, db: &'db dyn Database, trait_: TraitId) -> Trait<'db>;
}

impl<'a, 'db, C> ContextLike<'db> for &'a C
where
    C: ContextLike<'db>,
{
    fn resolve_adt(&self, db: &'db dyn Database, adt: AlgebraicTypeId) -> AlgebraicType<'db> {
        C::resolve_adt(self, db, adt)
    }

    fn resolve_func(&self, db: &'db dyn Database, func: FuncId) -> Func<'db> {
        C::resolve_func(self, db, func)
    }

    fn resolve_trait(&self, db: &'db dyn Database, trait_: TraitId) -> Trait<'db> {
        C::resolve_trait(self, db, trait_)
    }
}

impl<'a, 'db, C> ContextLike<'db> for &'a mut C
where
    C: ContextLike<'db>,
{
    fn resolve_adt(&self, db: &'db dyn Database, adt: AlgebraicTypeId) -> AlgebraicType<'db> {
        C::resolve_adt(self, db, adt)
    }

    fn resolve_func(&self, db: &'db dyn Database, func: FuncId) -> Func<'db> {
        C::resolve_func(self, db, func)
    }

    fn resolve_trait(&self, db: &'db dyn Database, trait_: TraitId) -> Trait<'db> {
        C::resolve_trait(self, db, trait_)
    }
}

/// An mir context is a collection of functions and types
/// that can refer to each other.
#[salsa::tracked]
pub struct Context<'db> {
    #[returns(ref)]
    #[tracked]
    pub data: ContextData<'db>,
}

impl<'db> ContextLike<'db> for Context<'db> {
    fn resolve_adt(&self, db: &'db dyn Database, adt: AlgebraicTypeId) -> AlgebraicType<'db> {
        /// Wrapping this in a salsa::tracked
        /// function allows salsa to avoid
        /// recalculating a query when the returned
        /// value doesn't change, even if others
        /// did change.
        #[salsa::tracked]
        fn resolve_helper<'db>(
            db: &'db dyn Database,
            cx: Context<'db>,
            adt: AlgebraicTypeId,
        ) -> AlgebraicType<'db> {
            cx.data(db).adts[adt]
        }
        resolve_helper(db, *self, adt)
    }

    fn resolve_func(&self, db: &'db dyn Database, func: FuncId) -> Func<'db> {
        #[salsa::tracked]
        fn resolve_helper<'db>(db: &'db dyn Database, cx: Context<'db>, func: FuncId) -> Func<'db> {
            cx.data(db).funcs[func]
        }
        resolve_helper(db, *self, func)
    }

    fn resolve_trait(&self, db: &'db dyn Database, trait_: TraitId) -> Trait<'db> {
        #[salsa::tracked]
        fn resolve_helper<'db>(
            db: &'db dyn Database,
            cx: Context<'db>,
            trait_: TraitId,
        ) -> Trait<'db> {
            cx.data(db).traits[trait_]
        }
        resolve_helper(db, *self, trait_)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, salsa::Update)]
pub struct ContextData<'db> {
    pub adts: PrimaryMap<AlgebraicTypeId, AlgebraicType<'db>>,
    pub funcs: PrimaryMap<FuncId, Func<'db>>,
    pub traits: PrimaryMap<TraitId, Trait<'db>>,
    pub trait_impls: Vec<TraitImpl<'db>>,
}

entity_ref! {
    /// ID of a type within the same mir `Context`.
    /// Enables circular references (e.g. struct with
    /// a reference to itself, as seen in a linked list)
    pub struct TypeRef;
}

entity_ref! {
    pub struct AlgebraicTypeId;
}

impl AlgebraicTypeId {
    pub fn resolve<'db>(
        &self,
        db: &'db dyn Database,
        cx: impl ContextLike<'db>,
    ) -> AlgebraicType<'db> {
        cx.resolve_adt(db, *self)
    }

    pub fn kind<'db>(
        &self,
        db: &'db dyn Database,
        cx: impl ContextLike<'db>,
    ) -> &'db AlgebraicTypeKind<'db> {
        self.resolve(db, cx).kind(db)
    }
}

entity_ref! {
    /// ID of a function within the same mir `Context`.
    /// Enables circular references (e.g. recursion or mutual
    /// recursion).
    pub struct FuncId;
}

impl FuncId {
    pub fn resolve<'db>(&self, db: &'db dyn Database, cx: impl ContextLike<'db>) -> Func<'db> {
        cx.resolve_func(db, *self)
    }

    pub fn resolve_header<'cx, 'db>(
        &self,
        db: &'db dyn Database,
        cx: &'cx ContextBuilder<'db>,
    ) -> &'cx FuncHeader<'db> {
        cx.resolve_func_header(db, *self)
    }

    pub fn data<'db>(
        &self,
        db: &'db dyn Database,
        cx: impl ContextLike<'db>,
    ) -> &'db FuncData<'db> {
        self.resolve(db, cx).data(db)
    }
}

entity_ref! {
    /// ID of a trait within the same mir `Context`.
    /// Enables circular references among traits.
    pub struct TraitId;
}

impl TraitId {
    pub fn resolve<'db>(&self, db: &'db dyn Database, cx: impl ContextLike<'db>) -> Trait<'db> {
        cx.resolve_trait(db, *self)
    }
}
