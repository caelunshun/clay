use crate::{
    Func,
    ir::{AlgebraicType, AlgebraicTypeData, FuncData, FuncHeader, Trait, TraitImpl},
};
use cranelift_entity::{PrimaryMap, SecondaryMap};
use salsa::Database;

/// An mir context is a collection of functions and types
/// that can refer to each other.
#[salsa::tracked]
pub struct Context<'db> {
    #[returns(ref)]
    #[tracked]
    pub data: ContextData<'db>,
}

/// Builder for `ContextData` that allows
/// lazy initialization of each type and function.
#[derive(Debug, Clone)]
pub struct ContextBuilder<'db> {
    adts: PrimaryMap<AlgebraicTypeId, Option<AlgebraicType<'db>>>,
    funcs: PrimaryMap<FuncId, Option<Func<'db>>>,
    traits: PrimaryMap<TraitId, Option<Trait<'db>>>,
    trait_impls: Vec<TraitImpl<'db>>,
    /// A function header can be known before
    /// the function body. This allows resolving
    /// recursive or mutually recursive functions.
    func_headers: SecondaryMap<FuncId, Option<FuncHeader<'db>>>,
}

impl<'db> ContextBuilder<'db> {
    pub fn new(_db: &'db dyn Database) -> Self {
        Self {
            adts: Default::default(),
            funcs: Default::default(),
            func_headers: Default::default(),
            trait_impls: Vec::new(),
            traits: Default::default(),
        }
    }

    /// Creates a `AlgebraicTypeRef` without binding the corresponding
    /// type data. It must be bound before finalization
    /// or a panic will occur.
    pub fn alloc_adt(&mut self) -> AlgebraicTypeId {
        self.adts.push(None)
    }

    /// Binds the value of an ADT.
    pub fn bind_adt(
        &mut self,
        _db: &'db dyn Database,
        type_ref: AlgebraicTypeId,
        typ: AlgebraicType<'db>,
    ) {
        assert!(self.adts[type_ref].is_none(), "type bound twice");
        self.adts[type_ref] = Some(typ);
    }

    pub fn resolve_adt(&self, r: AlgebraicTypeId) -> AlgebraicType<'db> {
        self.adts[r].expect("attempted to resolve unbound ADT")
    }

    pub fn alloc_func(&mut self) -> FuncId {
        self.funcs.push(None)
    }

    pub fn bind_func_header(&mut self, func_ref: FuncId, header: FuncHeader<'db>) {
        self.func_headers[func_ref] = Some(header);
    }

    pub fn bind_func(&mut self, func_ref: FuncId, func: Func<'db>) {
        assert!(self.funcs[func_ref].is_none(), "func bound twice");
        self.funcs[func_ref] = Some(func);
    }

    pub fn resolve_func(&self, r: FuncId) -> Func<'db> {
        self.funcs[r].expect("attempted to resolve unbound func")
    }

    pub fn resolve_func_header(&self, db: &'db dyn Database, r: FuncId) -> &FuncHeader<'db> {
        self.funcs[r]
            .as_ref()
            .map(|f| &f.data(db).header)
            .unwrap_or_else(|| {
                self.func_headers[r].as_ref().expect(
                    "attempted to resolve header of a func whose header is not yet resolved",
                )
            })
    }

    pub fn alloc_trait(&mut self) -> TraitId {
        self.traits.push(None)
    }

    pub fn bind_trait(&mut self, ref_: TraitId, trait_: Trait<'db>) {
        self.traits[ref_] = Some(trait_);
    }

    pub fn resolve_trait(&self, ref_: TraitId) -> Trait<'db> {
        self.traits[ref_].expect("attempted to resolve unbound trait")
    }

    pub fn add_trait_impl(&mut self, trait_impl: TraitImpl<'db>) {
        self.trait_impls.push(trait_impl);
    }

    pub fn finish(self) -> ContextData<'db> {
        let mut adts = PrimaryMap::new();
        let mut funcs = PrimaryMap::new();
        let mut traits = PrimaryMap::new();
        for (type_ref, typ) in self.adts {
            assert_eq!(
                adts.push(typ.expect("type not bound before finalization")),
                type_ref
            );
        }
        for (func_ref, func) in self.funcs {
            assert_eq!(
                funcs.push(func.expect("func not bound before finalization")),
                func_ref
            );
        }
        for (trait_ref, trait_) in self.traits {
            assert_eq!(
                traits.push(trait_.expect("trait not bound before finalization")),
                trait_ref
            );
        }

        ContextData {
            adts,
            funcs,
            traits,
            trait_impls: self.trait_impls,
        }
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
    pub fn resolve<'db>(&self, db: &'db dyn Database, cx: Context<'db>) -> AlgebraicType<'db> {
        /// Wrapping this in a salsa::tracked
        /// function allows salsa to avoid
        /// recalculating a query when the returned
        /// Type doesn't change, even if the Context
        /// was partially updated.
        #[salsa::tracked]
        fn resolve_helper<'db>(
            db: &'db dyn Database,
            cx: Context<'db>,
            type_ref: AlgebraicTypeId,
        ) -> AlgebraicType<'db> {
            cx.data(db).adts[type_ref]
        }

        resolve_helper(db, cx, *self)
    }

    pub fn resolve_in_builder<'db>(&self, cx: &ContextBuilder<'db>) -> AlgebraicType<'db> {
        cx.resolve_adt(*self)
    }

    pub fn data<'db>(
        &self,
        db: &'db dyn Database,
        cx: Context<'db>,
    ) -> &'db AlgebraicTypeData<'db> {
        self.resolve(db, cx).data(db)
    }
}

entity_ref! {
    /// ID of a function within the same mir `Context`.
    /// Enables circular references (e.g. recursion or mutual
    /// recursion).
    pub struct FuncId;
}

impl FuncId {
    pub fn resolve<'db>(&self, db: &'db dyn Database, cx: Context<'db>) -> Func<'db> {
        /// Wrapping this in a salsa::tracked
        /// function allows salsa to avoid
        /// recalculating a query when the returned
        /// Func doesn't change, even if the Context
        /// was partially updated.
        #[salsa::tracked]
        fn resolve_helper<'db>(
            db: &'db dyn Database,
            cx: Context<'db>,
            func_ref: FuncId,
        ) -> Func<'db> {
            cx.data(db).funcs[func_ref]
        }

        resolve_helper(db, cx, *self)
    }

    pub fn resolve_in_builder<'db>(&self, cx: &ContextBuilder<'db>) -> Func<'db> {
        cx.resolve_func(*self)
    }

    pub fn resolve_header<'cx, 'db>(
        &self,
        db: &'db dyn Database,
        cx: &'cx ContextBuilder<'db>,
    ) -> &'cx FuncHeader<'db> {
        cx.resolve_func_header(db, *self)
    }

    pub fn data<'db>(&self, db: &'db dyn Database, cx: Context<'db>) -> &'db FuncData<'db> {
        self.resolve(db, cx).data(db)
    }
}

entity_ref! {
    /// ID of a trait within the same mir `Context`.
    /// Enables circular references among traits.
    pub struct TraitId;
}

impl TraitId {
    pub fn resolve<'db>(&self, db: &'db dyn Database, cx: Context<'db>) -> Trait<'db> {
        /// Wrapping this in a salsa::tracked
        /// function allows salsa to avoid
        /// recalculating a query when the returned
        /// Trait doesn't change, even if the Context
        /// was partially updated.
        #[salsa::tracked]
        fn resolve_helper<'db>(
            db: &'db dyn Database,
            cx: Context<'db>,
            trait_ref: TraitId,
        ) -> Trait<'db> {
            cx.data(db).traits[trait_ref]
        }

        resolve_helper(db, cx, *self)
    }
}
