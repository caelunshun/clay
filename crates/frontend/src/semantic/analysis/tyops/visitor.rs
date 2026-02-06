use crate::{
    base::{Session, analysis::Spanned},
    semantic::{
        analysis::{TyCtxt, TyFoldable},
        syntax::{
            AdtInstance, FnInstance, FnOwner, HrtbBinder, HrtbBinderKind, HrtbDebruijnDef,
            HrtbDebruijnDefList, Re, SpannedAdtInstance, SpannedAdtInstanceView, SpannedFnInstance,
            SpannedFnInstanceView, SpannedFnOwner, SpannedFnOwnerView, SpannedHrtbBinder,
            SpannedHrtbBinderKind, SpannedHrtbBinderKindView, SpannedHrtbBinderView,
            SpannedHrtbDebruijnDef, SpannedHrtbDebruijnDefList, SpannedHrtbDebruijnDefView,
            SpannedRe, SpannedTraitClause, SpannedTraitClauseList, SpannedTraitClauseView,
            SpannedTraitInstance, SpannedTraitInstanceView, SpannedTraitParam,
            SpannedTraitParamList, SpannedTraitParamView, SpannedTraitSpec, SpannedTraitSpecView,
            SpannedTy, SpannedTyList, SpannedTyOrRe, SpannedTyOrReList, SpannedTyOrReView,
            SpannedTyProjection, SpannedTyProjectionView, SpannedTyView, TraitClause,
            TraitClauseList, TraitInstance, TraitParam, TraitParamList, TraitSpec, Ty, TyList,
            TyOrRe, TyOrReList, TyProjection,
        },
    },
};
use std::{convert::Infallible, ops::ControlFlow};

// === Core traits === //

pub trait TyVisitable: Sized {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>;

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
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

    fn visit_clause_list(&mut self, clauses: SpannedTraitClauseList) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(clauses)
    }

    fn visit_clause(&mut self, clause: SpannedTraitClause) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(clause)
    }

    fn visit_param_list(&mut self, params: SpannedTraitParamList) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(params)
    }

    fn visit_param(&mut self, param: SpannedTraitParam) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(param)
    }

    // === Instances === //

    fn visit_trait_spec(&mut self, spec: SpannedTraitSpec) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(spec)
    }

    fn visit_trait_instance(&mut self, instance: SpannedTraitInstance) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(instance)
    }

    fn visit_adt_instance(&mut self, instance: SpannedAdtInstance) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(instance)
    }

    fn visit_fn_instance(&mut self, instance: SpannedFnInstance) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(instance)
    }

    fn visit_fn_owner(&mut self, owner: SpannedFnOwner) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(owner)
    }

    // === Types === //

    fn visit_ty_or_re(&mut self, ty_or_re: SpannedTyOrRe) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(ty_or_re)
    }

    fn visit_ty_or_re_list(&mut self, list: SpannedTyOrReList) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(list)
    }

    fn visit_ty_list(&mut self, list: SpannedTyList) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(list)
    }

    fn visit_re(&mut self, re: SpannedRe) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(re)
    }

    fn visit_ty(&mut self, ty: SpannedTy) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(ty)
    }

    fn visit_ty_projection(&mut self, projection: SpannedTyProjection) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(projection)
    }

    // === Binders === //

    fn visit_hrtb_binder<T: Copy + TyVisitable + TyFoldable>(
        &mut self,
        binder: SpannedHrtbBinder<T>,
    ) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(binder)
    }

    fn visit_hrtb_binder_kind(&mut self, kind: SpannedHrtbBinderKind) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(kind)
    }

    fn visit_hrtb_debruijn_def_list(
        &mut self,
        defs: SpannedHrtbDebruijnDefList,
    ) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(defs)
    }

    fn visit_hrtb_debruijn_def(
        &mut self,
        defs: SpannedHrtbDebruijnDef,
    ) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(defs)
    }
}

// === Extensions === //

pub trait TyVisitorExt<'tcx>: TyVisitor<'tcx> {
    fn visit_spanned_fallible<T: TyVisitable>(
        &mut self,
        value: Spanned<T>,
    ) -> ControlFlow<Self::Break> {
        T::visit_raw(value, self)
    }

    fn visit_fallible<T: TyVisitable>(&mut self, value: T) -> ControlFlow<Self::Break> {
        self.visit_spanned_fallible(Spanned::new_unspanned(value))
    }

    fn walk_spanned_fallible<T: TyVisitable>(
        &mut self,
        value: Spanned<T>,
    ) -> ControlFlow<Self::Break> {
        T::walk_raw(value, self)
    }

    fn walk_fallible<T: TyVisitable>(&mut self, value: T) -> ControlFlow<Self::Break> {
        self.walk_spanned_fallible(Spanned::new_unspanned(value))
    }
}

impl<'tcx, T: ?Sized + TyVisitor<'tcx>> TyVisitorExt<'tcx> for T {}

pub trait TyVisitorInfallibleExt<'tcx>: TyVisitor<'tcx, Break = Infallible> {
    fn visit_spanned<T: TyVisitable>(&mut self, value: Spanned<T>) {
        ControlFlow::Continue(()) = self.visit_spanned_fallible(value)
    }

    fn visit<T: TyVisitable>(&mut self, value: T) {
        ControlFlow::Continue(()) = self.visit_fallible(value)
    }

    fn walk_spanned<T: TyVisitable>(&mut self, value: Spanned<T>) {
        ControlFlow::Continue(()) = self.walk_spanned_fallible(value)
    }

    fn walk<T: TyVisitable>(&mut self, value: T) {
        ControlFlow::Continue(()) = self.walk_fallible(value)
    }
}

impl<'tcx, T: ?Sized + TyVisitor<'tcx, Break = Infallible>> TyVisitorInfallibleExt<'tcx> for T {}

// === Clauses === //

impl TyVisitable for TraitClauseList {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_clause_list(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        for clause in me.iter(visitor.tcx()) {
            visitor.visit_spanned_fallible(clause)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for TraitClause {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_clause(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        match me.view(visitor.tcx()) {
            SpannedTraitClauseView::Outlives(_dir, ty_or_re) => {
                visitor.visit_spanned_fallible(ty_or_re)?;
            }
            SpannedTraitClauseView::Trait(spec) => {
                visitor.visit_spanned_fallible(spec)?;
            }
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for TraitParamList {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_param_list(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        for param in me.iter(visitor.tcx()) {
            visitor.visit_spanned_fallible(param)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for TraitParam {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_param(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        match me.view(visitor.tcx()) {
            SpannedTraitParamView::Equals(ty_or_re) => {
                visitor.visit_spanned_fallible(ty_or_re)?;
            }
            SpannedTraitParamView::Unspecified(clauses) => {
                visitor.visit_spanned_fallible(clauses)?;
            }
        }

        ControlFlow::Continue(())
    }
}

// === Instances === //

impl TyVisitable for TraitSpec {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_trait_spec(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let SpannedTraitSpecView { def: _, params } = me.view(visitor.tcx());
        visitor.visit_spanned_fallible(params)?;

        ControlFlow::Continue(())
    }
}

impl TyVisitable for TraitInstance {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_trait_instance(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let SpannedTraitInstanceView { def: _, params } = me.view(visitor.tcx());
        visitor.visit_spanned_fallible(params)?;

        ControlFlow::Continue(())
    }
}

impl TyVisitable for AdtInstance {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_adt_instance(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let SpannedAdtInstanceView { def: _, params } = me.view(visitor.tcx());
        visitor.visit_spanned_fallible(params)?;

        ControlFlow::Continue(())
    }
}

impl TyVisitable for FnInstance {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_fn_instance(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let SpannedFnInstanceView { owner, early_args } = me.view(visitor.tcx());

        visitor.visit_spanned_fallible(owner)?;

        if let Some(early_args) = early_args {
            visitor.visit_spanned_fallible(early_args)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for FnOwner {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_fn_owner(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let tcx = visitor.tcx();

        match me.view(tcx) {
            SpannedFnOwnerView::Item(_) => {
                // (dead end)
            }
            SpannedFnOwnerView::Trait {
                instance,
                self_ty,
                method_idx: _,
            } => {
                visitor.visit_spanned_fallible(instance)?;
                visitor.visit_spanned_fallible(self_ty)?;
            }
            SpannedFnOwnerView::Inherent {
                self_ty,
                block: _,
                method_idx: _,
            } => {
                visitor.visit_spanned_fallible(self_ty)?;
            }
        }

        ControlFlow::Continue(())
    }
}

// === Types === //

impl TyVisitable for TyOrRe {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_ty_or_re(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        match me.view(visitor.tcx()) {
            SpannedTyOrReView::Re(re) => visitor.visit_spanned_fallible(re),
            SpannedTyOrReView::Ty(ty) => visitor.visit_spanned_fallible(ty),
        }
    }
}

impl TyVisitable for TyOrReList {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_ty_or_re_list(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        for ty_or_re in me.iter(visitor.tcx()) {
            visitor.visit_spanned_fallible(ty_or_re)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for TyList {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_ty_list(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        for ty in me.iter(visitor.tcx()) {
            visitor.visit_spanned_fallible(ty)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for Re {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_re(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        match me.value {
            Re::Gc
            | Re::SigInfer
            | Re::Erased
            | Re::Error(_)
            | Re::SigGeneric(_)
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
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_ty(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        match me.view(visitor.tcx()) {
            SpannedTyView::Simple(_)
            | SpannedTyView::SigInfer
            | SpannedTyView::Error(_)
            | SpannedTyView::SigThis
            | SpannedTyView::SigGeneric(_)
            | SpannedTyView::HrtbVar(_)
            | SpannedTyView::InferVar(_)
            | SpannedTyView::UniversalVar(_) => {
                // (dead end)
            }
            SpannedTyView::SigProject(project) => {
                visitor.visit_spanned_fallible(project)?;
            }
            SpannedTyView::Reference(re, _muta, pointee) => {
                visitor.visit_spanned_fallible(re)?;
                visitor.visit_spanned_fallible(pointee)?;
            }
            SpannedTyView::FnDef(instance) => {
                visitor.visit_spanned_fallible(instance)?;
            }
            SpannedTyView::Adt(instance) => {
                visitor.visit_spanned_fallible(instance)?;
            }
            SpannedTyView::Trait(re, _muta, clause_list) => {
                visitor.visit_spanned_fallible(re)?;
                visitor.visit_spanned_fallible(clause_list)?;
            }
            SpannedTyView::Tuple(tys) => {
                visitor.visit_spanned_fallible(tys)?;
            }
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for TyProjection {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_ty_projection(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let SpannedTyProjectionView {
            target,
            spec,
            assoc_span: _,
            assoc: _,
        } = me.view(visitor.tcx());

        visitor.visit_spanned_fallible(target)?;
        visitor.visit_spanned_fallible(spec)?;

        ControlFlow::Continue(())
    }
}

// === Binders === //

impl<T: TyVisitable + TyFoldable + Copy> TyVisitable for HrtbBinder<T> {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_hrtb_binder(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let SpannedHrtbBinderView { kind, inner } = me.view(visitor.tcx());

        visitor.visit_spanned_fallible(kind)?;
        visitor.visit_spanned_fallible(inner)?;

        ControlFlow::Continue(())
    }
}

impl TyVisitable for HrtbBinderKind {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_hrtb_binder_kind(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        match me.view(visitor.tcx()) {
            SpannedHrtbBinderKindView::Signature(_) => {
                // (terminal)
            }
            SpannedHrtbBinderKindView::Imported(clauses) => {
                visitor.visit_spanned_fallible(clauses)?;
            }
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for HrtbDebruijnDefList {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_hrtb_debruijn_def_list(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        for elem in me.iter(visitor.tcx()) {
            visitor.visit_spanned_fallible(elem)?;
        }

        ControlFlow::Continue(())
    }
}

impl TyVisitable for HrtbDebruijnDef {
    fn visit_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        visitor.visit_hrtb_debruijn_def(me)
    }

    fn walk_raw<'tcx, V>(me: Spanned<Self>, visitor: &mut V) -> ControlFlow<V::Break>
    where
        V: ?Sized + TyVisitor<'tcx>,
    {
        let SpannedHrtbDebruijnDefView {
            spawned_from: _,
            kind: _,
            clauses,
        } = me.view(visitor.tcx());

        visitor.visit_spanned_fallible(clauses)?;

        ControlFlow::Continue(())
    }
}
