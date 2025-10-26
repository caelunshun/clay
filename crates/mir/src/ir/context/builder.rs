use crate::{
    Func,
    ir::{
        AlgebraicType, AlgebraicTypeId, ContextData, ContextLike, FuncHeader, FuncId, Trait,
        TraitId, TraitImpl, TraitImplId,
    },
};
use cranelift_entity::{PrimaryMap, SecondaryMap};
use fir_core::IndexMap;
use salsa::Database;
use std::borrow::Cow;

/// Builder for `ContextData` that allows
/// lazy initialization of each type and function.
#[derive(Debug, Clone)]
pub struct ContextBuilder<'db> {
    adts: PrimaryMap<AlgebraicTypeId, Option<AlgebraicType<'db>>>,
    funcs: PrimaryMap<FuncId, Option<Func<'db>>>,
    traits: PrimaryMap<TraitId, Option<Trait<'db>>>,
    trait_impls: PrimaryMap<TraitImplId, TraitImpl<'db>>,
    trait_impls_by_trait: IndexMap<TraitId, Vec<TraitImpl<'db>>>,
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
            trait_impls: Default::default(),
            traits: Default::default(),
            trait_impls_by_trait: Default::default(),
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

    pub fn alloc_trait(&mut self) -> TraitId {
        self.traits.push(None)
    }

    pub fn bind_trait(&mut self, ref_: TraitId, trait_: Trait<'db>) {
        self.traits[ref_] = Some(trait_);
    }

    pub fn add_trait_impl(
        &mut self,
        db: &'db dyn Database,
        trait_impl: TraitImpl<'db>,
    ) -> TraitImplId {
        self.trait_impls_by_trait
            .entry(trait_impl.data(db).trait_.trait_(db))
            .or_default()
            .push(trait_impl);
        self.trait_impls.push(trait_impl)
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
            trait_impls_by_trait: self.trait_impls_by_trait,
        }
    }
}

impl<'db> ContextLike<'db> for ContextBuilder<'db> {
    fn resolve_adt(&self, _db: &'db dyn Database, adt: AlgebraicTypeId) -> AlgebraicType<'db> {
        self.adts[adt].expect("attempted to resolve unbound ADT")
    }

    fn resolve_func(&self, _db: &'db dyn Database, func: FuncId) -> Func<'db> {
        self.funcs[func].expect("attempted to resolve unbound func")
    }

    fn resolve_trait(&self, _db: &'db dyn Database, ref_: TraitId) -> Trait<'db> {
        self.traits[ref_].expect("attempted to resolve unbound trait")
    }

    fn trait_impls_for_trait<'a>(
        &'a self,
        _db: &'db dyn Database,
        trait_: TraitId,
    ) -> Cow<'a, [TraitImpl<'db>]> {
        Cow::Borrowed(
            self.trait_impls_by_trait
                .get(&trait_)
                .map(Vec::as_slice)
                .unwrap_or_default(),
        )
    }

    fn resolve_func_header(&self, db: &'db dyn Database, func: FuncId) -> &FuncHeader<'db> {
        self.funcs[func]
            .as_ref()
            .map(|f: &Func<'_>| &f.data(db).header)
            .unwrap_or_else(|| {
                self.func_headers[func].as_ref().expect(
                    "attempted to resolve header of a func whose header is not yet resolved",
                )
            })
    }

    fn resolve_trait_impl(
        &self,
        _db: &'db dyn Database,
        trait_impl: TraitImplId,
    ) -> TraitImpl<'db> {
        self.trait_impls[trait_impl]
    }
}
