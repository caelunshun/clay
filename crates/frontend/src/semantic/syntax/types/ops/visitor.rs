use crate::{
    base::Session,
    semantic::syntax::{
        AdtInstance, FnInstance, FnInstanceInner, FnOwner, HrtbBinder, HrtbDebruijnDef,
        HrtbDebruijnDefList, HrtbProjection, Re, TraitClause, TraitClauseList, TraitInstance,
        TraitParam, TraitParamList, TraitSpec, Ty, TyKind, TyList, TyOrRe, TyOrReList, UniversalTy,
        UniversalTyProj, UniversalTyProjInner,
    },
};
use std::{convert::Infallible, ops::ControlFlow};

// === Core traits === //

pub trait TyVisitable: Sized {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>;

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>;
}

pub trait TyVisitor<'sess> {
    type Break;

    fn session(&self) -> &'sess Session;

    // === Clauses === //

    fn visit_clause_list(&mut self, clauses: TraitClauseList) -> ControlFlow<Self::Break> {
        self.walk_fallible(clauses)
    }

    fn visit_clause(&mut self, clause: TraitClause) -> ControlFlow<Self::Break> {
        self.walk_fallible(clause)
    }

    fn visit_param_list(&mut self, params: TraitParamList) -> ControlFlow<Self::Break> {
        self.walk_fallible(params)
    }

    fn visit_param(&mut self, param: TraitParam) -> ControlFlow<Self::Break> {
        self.walk_fallible(param)
    }

    // === Instances === //

    fn visit_trait_spec(&mut self, spec: TraitSpec) -> ControlFlow<Self::Break> {
        self.walk_fallible(spec)
    }

    fn visit_trait_instance(&mut self, instance: TraitInstance) -> ControlFlow<Self::Break> {
        self.walk_fallible(instance)
    }

    fn visit_adt_instance(&mut self, instance: AdtInstance) -> ControlFlow<Self::Break> {
        self.walk_fallible(instance)
    }

    fn visit_hrtb_projection(&mut self, projection: HrtbProjection) -> ControlFlow<Self::Break> {
        self.walk_fallible(projection)
    }

    fn visit_fn_instance(&mut self, instance: FnInstance) -> ControlFlow<Self::Break> {
        self.walk_fallible(instance)
    }

    fn visit_fn_owner(&mut self, owner: FnOwner) -> ControlFlow<Self::Break> {
        self.walk_fallible(owner)
    }

    // === Types === //

    fn visit_ty_or_re(&mut self, ty_or_re: TyOrRe) -> ControlFlow<Self::Break> {
        self.walk_fallible(ty_or_re)
    }

    fn visit_ty_or_re_list(&mut self, list: TyOrReList) -> ControlFlow<Self::Break> {
        self.walk_fallible(list)
    }

    fn visit_ty_list(&mut self, list: TyList) -> ControlFlow<Self::Break> {
        self.walk_fallible(list)
    }

    fn visit_re(&mut self, re: Re) -> ControlFlow<Self::Break> {
        self.walk_fallible(re)
    }

    fn visit_ty(&mut self, ty: Ty) -> ControlFlow<Self::Break> {
        self.walk_fallible(ty)
    }

    // === Universals === //

    fn visit_universal(&mut self, ty: UniversalTy) -> ControlFlow<Self::Break> {
        self.walk_fallible(ty)
    }

    fn visit_universal_projection(
        &mut self,
        projection: UniversalTyProj,
    ) -> ControlFlow<Self::Break> {
        self.walk_fallible(projection)
    }

    // === Binders === //

    fn visit_hrtb_binder(&mut self, binder: HrtbBinder) -> ControlFlow<Self::Break> {
        self.walk_fallible(binder)
    }

    fn visit_hrtb_debruijn_def_list(
        &mut self,
        defs: HrtbDebruijnDefList,
    ) -> ControlFlow<Self::Break> {
        self.walk_fallible(defs)
    }

    fn visit_hrtb_debruijn_def(&mut self, defs: HrtbDebruijnDef) -> ControlFlow<Self::Break> {
        self.walk_fallible(defs)
    }
}

// === Extensions === //

pub trait TyVisitorExt<'sess>: TyVisitor<'sess> {
    fn visit_fallible<T: TyVisitable>(&mut self, value: T) -> ControlFlow<Self::Break> {
        T::visit_raw(value, self)
    }

    fn walk_fallible<T: TyVisitable>(&mut self, value: T) -> ControlFlow<Self::Break> {
        T::walk_raw(value, self)
    }
}

impl<'sess, T: ?Sized + TyVisitor<'sess>> TyVisitorExt<'sess> for T {}

pub trait TyVisitorInfallibleExt<'sess>: TyVisitor<'sess, Break = Infallible> {
    fn visit<T: TyVisitable>(&mut self, value: T) {
        ControlFlow::Continue(()) = self.visit_fallible(value)
    }

    fn walk<T: TyVisitable>(&mut self, value: T) {
        ControlFlow::Continue(()) = self.walk_fallible(value)
    }
}

impl<'sess, T: ?Sized + TyVisitor<'sess, Break = Infallible>> TyVisitorInfallibleExt<'sess> for T {}

// === Clauses === //

impl TyVisitable for TraitClauseList {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_clause_list(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        let s = visitor.session();

        for &clause in me.r(s) {
            visitor.visit_fallible(clause)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for TraitClause {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_clause(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        match me {
            TraitClause::Outlives(_dir, ty_or_re) => {
                visitor.visit_fallible(ty_or_re)?;
            }
            TraitClause::Trait(spec) => {
                visitor.visit_fallible(spec)?;
            }
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for TraitParamList {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_param_list(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        let s = visitor.session();

        for &param in me.r(s) {
            visitor.visit_fallible(param)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for TraitParam {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_param(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        match me {
            TraitParam::Equals(ty_or_re) => {
                visitor.visit_fallible(ty_or_re)?;
            }
            TraitParam::Unspecified(clauses) => {
                visitor.visit_fallible(clauses)?;
            }
        }

        ControlFlow::Continue(())
    }
}

// === Instances === //

impl TyVisitable for TraitSpec {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_trait_spec(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        let TraitSpec { def: _, params } = me;
        visitor.visit_fallible(params)?;

        ControlFlow::Continue(())
    }
}

impl TyVisitable for TraitInstance {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_trait_instance(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        let TraitInstance { def: _, params } = me;
        visitor.visit_fallible(params)?;

        ControlFlow::Continue(())
    }
}

impl TyVisitable for AdtInstance {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_adt_instance(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        let AdtInstance { def: _, params } = me;
        visitor.visit_fallible(params)?;

        ControlFlow::Continue(())
    }
}

impl TyVisitable for HrtbProjection {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_hrtb_projection(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        let HrtbProjection {
            target,
            spec,
            assoc_idx: _,
        } = me;

        visitor.visit_fallible(target)?;
        visitor.visit_fallible(spec)?;

        ControlFlow::Continue(())
    }
}

impl TyVisitable for FnInstance {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_fn_instance(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        let s = visitor.session();
        let FnInstanceInner { owner, early_args } = *me.r(s);

        visitor.visit_fallible(owner)?;

        if let Some(early_args) = early_args {
            visitor.visit_fallible(early_args)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for FnOwner {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_fn_owner(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        match me {
            FnOwner::Item(_) | FnOwner::AdtCtor(_) => {
                // (dead end)
            }
            FnOwner::Trait {
                instance,
                self_ty,
                method_idx: _,
            } => {
                visitor.visit_fallible(instance)?;
                visitor.visit_fallible(self_ty)?;
            }
            FnOwner::Inherent {
                self_ty,
                block: _,
                method_idx: _,
            } => {
                visitor.visit_fallible(self_ty)?;
            }
        }

        ControlFlow::Continue(())
    }
}

// === Types === //

impl TyVisitable for TyOrRe {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_ty_or_re(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        match me {
            TyOrRe::Re(re) => visitor.visit_fallible(re),
            TyOrRe::Ty(ty) => visitor.visit_fallible(ty),
        }
    }
}

impl TyVisitable for TyOrReList {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_ty_or_re_list(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        let s = visitor.session();

        for &ty_or_re in me.r(s) {
            visitor.visit_fallible(ty_or_re)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for TyList {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_ty_list(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        let s = visitor.session();

        for &ty in me.r(s) {
            visitor.visit_fallible(ty)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for Re {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_re(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        match me {
            Re::Gc | Re::Error(_) | Re::HrtbVar(_) | Re::InferVar(_) | Re::UniversalVar(_) => {
                _ = visitor;
                // (dead end)
            }
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for Ty {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_ty(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        let s = visitor.session();

        match *me.r(s) {
            TyKind::Simple(_) | TyKind::Error(_) | TyKind::HrtbVar(_) | TyKind::InferVar(_) => {
                // (dead end)
            }
            TyKind::Universal(universal) => {
                visitor.visit_fallible(universal)?;
            }
            TyKind::Reference(re, _muta, pointee) => {
                visitor.visit_fallible(re)?;
                visitor.visit_fallible(pointee)?;
            }
            TyKind::FnDef(instance) => {
                visitor.visit_fallible(instance)?;
            }
            TyKind::Adt(instance) => {
                visitor.visit_fallible(instance)?;
            }
            TyKind::HrtbProjection(projection) => {
                visitor.visit_fallible(projection)?;
            }
            TyKind::Trait(re, _muta, clause_list) => {
                visitor.visit_fallible(re)?;
                visitor.visit_fallible(clause_list)?;
            }
            TyKind::Tuple(tys) => {
                visitor.visit_fallible(tys)?;
            }
        }

        ControlFlow::Continue(())
    }
}

// === Universals === //

impl TyVisitable for UniversalTy {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_universal(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        match me {
            UniversalTy::Root(_var) => {
                // (dead_end)
            }
            UniversalTy::Projection(projection) => {
                visitor.visit_fallible(projection)?;
            }
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for UniversalTyProj {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_universal_projection(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        let s = visitor.session();
        let UniversalTyProjInner {
            target,
            as_spec,
            assoc_idx: _,
            cache_idx: _,
        } = *me.r(s);

        visitor.visit_fallible(target)?;
        visitor.visit_fallible(as_spec)?;

        ControlFlow::Continue(())
    }
}

// === Binders === //

impl TyVisitable for HrtbBinder {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_hrtb_binder(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        let HrtbBinder { defs: kind, inner } = me;

        visitor.visit_fallible(kind)?;
        visitor.visit_fallible(inner)?;

        ControlFlow::Continue(())
    }
}

impl TyVisitable for HrtbDebruijnDefList {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_hrtb_debruijn_def_list(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        let s = visitor.session();

        for &elem in me.r(s) {
            visitor.visit_fallible(elem)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for HrtbDebruijnDef {
    fn visit_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        visitor.visit_hrtb_debruijn_def(me)
    }

    fn walk_raw<'sess, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'sess>,
    {
        let HrtbDebruijnDef {
            span: _,
            name: _,
            kind: _,
            clauses,
        } = me;

        visitor.visit_fallible(clauses)?;

        ControlFlow::Continue(())
    }
}
