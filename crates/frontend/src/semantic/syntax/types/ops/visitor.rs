use crate::{
    base::Session,
    semantic::syntax::{
        AdtInstance, FnInstance, FnInstanceInner, FnOwner, FnOwnerAdtCtor, FnOwnerInherent,
        FnOwnerTrait, HrtbBinder, HrtbDebruijnDef, HrtbDebruijnDefList, HrtbProjection, Re,
        TraitClause, TraitClauseList, TraitInstance, TraitParam, TraitParamList, TraitSpec, Ty,
        TyCtxt, TyKind, TyList, TyOrRe, TyOrReList, UniversalTy, UniversalTyProj,
        UniversalTyProjInner, UniversalTyProjKind,
    },
};
use std::{convert::Infallible, ops::ControlFlow};

// === Core traits === //

pub trait TyVisitable: Sized {
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>;

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>;
}

pub trait TyVisitor<'tcx> {
    type Break;

    fn tcx(&self) -> &'tcx TyCtxt;

    fn session(&self) -> &'tcx Session {
        &self.tcx().session
    }

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

    fn visit_universal_projection_kind(
        &mut self,
        kind: UniversalTyProjKind,
    ) -> ControlFlow<Self::Break> {
        self.walk_fallible(kind)
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

pub trait TyVisitorExt<'tcx>: TyVisitor<'tcx> {
    fn visit_fallible<T: TyVisitable>(&mut self, value: T) -> ControlFlow<Self::Break> {
        T::visit_raw(value, self)
    }

    fn walk_fallible<T: TyVisitable>(&mut self, value: T) -> ControlFlow<Self::Break> {
        T::walk_raw(value, self)
    }
}

impl<'tcx, T: ?Sized + TyVisitor<'tcx>> TyVisitorExt<'tcx> for T {}

pub trait TyVisitorInfallibleExt<'tcx>: TyVisitor<'tcx, Break = Infallible> {
    fn visit<T: TyVisitable>(&mut self, value: T) {
        ControlFlow::Continue(()) = self.visit_fallible(value)
    }

    fn walk<T: TyVisitable>(&mut self, value: T) {
        ControlFlow::Continue(()) = self.walk_fallible(value)
    }
}

impl<'tcx, T: ?Sized + TyVisitor<'tcx, Break = Infallible>> TyVisitorInfallibleExt<'tcx> for T {}

// === Clauses === //

impl TyVisitable for TraitClauseList {
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_clause_list(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let s = visitor.session();

        for &clause in me.r(s) {
            visitor.visit_fallible(clause)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for TraitClause {
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_clause(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
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
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_param_list(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let s = visitor.session();

        for &param in me.r(s) {
            visitor.visit_fallible(param)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for TraitParam {
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_param(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
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
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_trait_spec(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let TraitSpec { def: _, params } = me;
        visitor.visit_fallible(params)?;

        ControlFlow::Continue(())
    }
}

impl TyVisitable for TraitInstance {
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_trait_instance(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let TraitInstance { def: _, params } = me;
        visitor.visit_fallible(params)?;

        ControlFlow::Continue(())
    }
}

impl TyVisitable for AdtInstance {
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_adt_instance(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let AdtInstance { def: _, params } = me;
        visitor.visit_fallible(params)?;

        ControlFlow::Continue(())
    }
}

impl TyVisitable for HrtbProjection {
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_hrtb_projection(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
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
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_fn_instance(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
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
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_fn_owner(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        match me {
            FnOwner::Item(_) | FnOwner::AdtCtor(FnOwnerAdtCtor { ctor: _ }) => {
                // (dead end)
            }
            FnOwner::Trait(FnOwnerTrait {
                instance,
                self_ty,
                method_idx: _,
            }) => {
                visitor.visit_fallible(instance)?;
                visitor.visit_fallible(self_ty)?;
            }
            FnOwner::Inherent(FnOwnerInherent {
                self_ty,
                block: _,
                method_idx: _,
            }) => {
                visitor.visit_fallible(self_ty)?;
            }
        }

        ControlFlow::Continue(())
    }
}

// === Types === //

impl TyVisitable for TyOrRe {
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_ty_or_re(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        match me {
            TyOrRe::Re(re) => visitor.visit_fallible(re),
            TyOrRe::Ty(ty) => visitor.visit_fallible(ty),
        }
    }
}

impl TyVisitable for TyOrReList {
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_ty_or_re_list(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let s = visitor.session();

        for &ty_or_re in me.r(s) {
            visitor.visit_fallible(ty_or_re)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for TyList {
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_ty_list(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let s = visitor.session();

        for &ty in me.r(s) {
            visitor.visit_fallible(ty)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for Re {
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_re(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        match me {
            Re::Gc
            | Re::Erased
            | Re::Error(_)
            | Re::HrtbVar(_)
            | Re::InferVar(_)
            | Re::UniversalVar(_) => {
                _ = visitor;
                // (dead end)
            }
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for Ty {
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_ty(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
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
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_universal(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
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
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_universal_projection(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let s = visitor.session();
        let UniversalTyProjInner {
            target,
            kind,
            idx: _,
        } = *me.r(s);

        visitor.visit_fallible(target)?;
        visitor.visit_fallible(kind)?;

        ControlFlow::Continue(())
    }
}

impl TyVisitable for UniversalTyProjKind {
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_universal_projection_kind(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        match me {
            UniversalTyProjKind::HrtbInvariant { id: _ } => {
                // (dead end)
            }
            UniversalTyProjKind::HrtbRelative {
                parent_clause_idx: _,
                parent_clause_hrtb_args,
                assoc_idx: _,
            } => {
                visitor.visit_fallible(parent_clause_hrtb_args)?;
            }
        }

        ControlFlow::Continue(())
    }
}

// === Binders === //

impl TyVisitable for HrtbBinder {
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_hrtb_binder(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let HrtbBinder { defs: kind, inner } = me;

        visitor.visit_fallible(kind)?;
        visitor.visit_fallible(inner)?;

        ControlFlow::Continue(())
    }
}

impl TyVisitable for HrtbDebruijnDefList {
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_hrtb_debruijn_def_list(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let s = visitor.session();

        for &elem in me.r(s) {
            visitor.visit_fallible(elem)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for HrtbDebruijnDef {
    fn visit_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_hrtb_debruijn_def(me)
    }

    fn walk_raw<'tcx, V>(me: Self, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
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
