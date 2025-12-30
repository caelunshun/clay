use crate::{
    base::{
        Session,
        analysis::Spanned,
        arena::{HasInterner, HasListInterner, Obj},
        syntax::Span,
    },
    semantic::{
        analysis::TyCtxt,
        syntax::{
            AdtInstance, InferReVar, InferTyVar, Re, RegionGeneric, SpannedAdtInstance,
            SpannedAdtInstanceView, SpannedRe, SpannedTraitClause, SpannedTraitClauseList,
            SpannedTraitClauseView, SpannedTraitInstance, SpannedTraitInstanceView,
            SpannedTraitParam, SpannedTraitParamList, SpannedTraitParamView, SpannedTraitSpec,
            SpannedTraitSpecView, SpannedTy, SpannedTyList, SpannedTyOrRe, SpannedTyOrReList,
            SpannedTyOrReView, SpannedTyView, TraitClause, TraitClauseList, TraitInstance,
            TraitParam, TraitParamList, TraitSpec, Ty, TyKind, TyList, TyOrRe, TyOrReList,
            TypeGeneric, UniversalReVar, UniversalTyVar,
        },
    },
};
use std::{convert::Infallible, ops::ControlFlow};

// === Visitor === //

// Core traits
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

    // === Terminators === //

    fn visit_sig_self_ty_use(&mut self, span: Option<Span>) -> ControlFlow<Self::Break> {
        _ = span;

        ControlFlow::Continue(())
    }

    fn visit_re_infer_var_use(
        &mut self,
        span: Option<Span>,
        var: InferReVar,
    ) -> ControlFlow<Self::Break> {
        _ = (span, var);

        ControlFlow::Continue(())
    }

    fn visit_re_universal_var_use(
        &mut self,
        span: Option<Span>,
        var: UniversalReVar,
    ) -> ControlFlow<Self::Break> {
        _ = (span, var);

        ControlFlow::Continue(())
    }

    fn visit_ty_infer_var_use(
        &mut self,
        span: Option<Span>,
        var: InferTyVar,
    ) -> ControlFlow<Self::Break> {
        _ = (span, var);

        ControlFlow::Continue(())
    }

    fn visit_ty_universal_var_use(
        &mut self,
        span: Option<Span>,
        var: UniversalTyVar,
    ) -> ControlFlow<Self::Break> {
        _ = (span, var);

        ControlFlow::Continue(())
    }

    fn visit_re_sig_generic_use(
        &mut self,
        span: Option<Span>,
        generic: Obj<RegionGeneric>,
    ) -> ControlFlow<Self::Break> {
        _ = (span, generic);

        ControlFlow::Continue(())
    }

    fn visit_ty_sig_generic_use(
        &mut self,
        span: Option<Span>,
        generic: Obj<TypeGeneric>,
    ) -> ControlFlow<Self::Break> {
        _ = (span, generic);

        ControlFlow::Continue(())
    }
}

// Extensions
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

// Clauses
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
            SpannedTraitClauseView::Outlives(re) => {
                visitor.visit_spanned_fallible(re)?;
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

// Instances
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

// Types
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
            Re::Gc | Re::SigExplicitInfer | Re::Erased | Re::Error(_) => {
                // (dead end)
            }
            Re::SigGeneric(generic) => {
                visitor.visit_re_sig_generic_use(me.own_span_if_specified(), generic)?;
            }
            Re::InferVar(var) => {
                visitor.visit_re_infer_var_use(me.own_span_if_specified(), var)?;
            }
            Re::UniversalVar(var) => {
                visitor.visit_re_universal_var_use(me.own_span_if_specified(), var)?;
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
            | SpannedTyView::SigExplicitInfer
            | SpannedTyView::FnDef(_, None)
            | SpannedTyView::Error(_) => {
                // (dead end)
            }
            SpannedTyView::SigThis => {
                visitor.visit_sig_self_ty_use(me.own_span_if_specified())?;
            }
            SpannedTyView::SigGeneric(generic) => {
                visitor.visit_ty_sig_generic_use(me.own_span_if_specified(), generic)?;
            }
            SpannedTyView::InferVar(var) => {
                visitor.visit_ty_infer_var_use(me.own_span_if_specified(), var)?;
            }
            SpannedTyView::UniversalVar(var) => {
                visitor.visit_ty_universal_var_use(me.own_span_if_specified(), var)?;
            }
            SpannedTyView::Reference(re, _muta, pointee) => {
                visitor.visit_spanned_fallible(re)?;
                visitor.visit_spanned_fallible(pointee)?;
            }
            SpannedTyView::FnDef(_def, Some(generics)) => {
                visitor.visit_spanned_fallible(generics)?;
            }
            SpannedTyView::Adt(instance) => {
                visitor.visit_spanned_fallible(instance)?;
            }
            SpannedTyView::Trait(clause_list) => {
                visitor.visit_spanned_fallible(clause_list)?;
            }
            SpannedTyView::Tuple(tys) => {
                visitor.visit_spanned_fallible(tys)?;
            }
        }

        ControlFlow::Continue(())
    }
}

// === Folder === //

pub trait TyFolder<'tcx> {
    type Error;

    fn tcx(&self) -> &'tcx TyCtxt;

    fn session(&self) -> &'tcx Session {
        &self.tcx().session
    }

    // === Clauses === //

    fn try_fold_clause_list(
        &mut self,
        clauses: TraitClauseList,
    ) -> Result<TraitClauseList, Self::Error> {
        self.super_clause_list(clauses)
    }

    fn try_fold_clause(&mut self, clause: TraitClause) -> Result<TraitClause, Self::Error> {
        self.super_clause(clause)
    }

    fn try_fold_param_list(
        &mut self,
        params: TraitParamList,
    ) -> Result<TraitParamList, Self::Error> {
        self.super_param_list(params)
    }

    fn try_fold_param(&mut self, param: TraitParam) -> Result<TraitParam, Self::Error> {
        self.super_param(param)
    }

    // === Instances === //

    fn try_fold_trait_spec(&mut self, spec: TraitSpec) -> Result<TraitSpec, Self::Error> {
        self.super_trait_spec(spec)
    }

    fn try_fold_trait_instance(
        &mut self,
        instance: TraitInstance,
    ) -> Result<TraitInstance, Self::Error> {
        self.super_trait_instance(instance)
    }

    fn try_fold_adt_instance(&mut self, instance: AdtInstance) -> Result<AdtInstance, Self::Error> {
        self.super_adt_instance(instance)
    }

    // === Types === //

    fn try_fold_ty_or_re(&mut self, ty_or_re: TyOrRe) -> Result<TyOrRe, Self::Error> {
        self.super_ty_or_re(ty_or_re)
    }

    fn try_fold_ty_or_re_list(&mut self, list: TyOrReList) -> Result<TyOrReList, Self::Error> {
        self.super_ty_or_re_list(list)
    }

    fn try_fold_ty_list(&mut self, list: TyList) -> Result<TyList, Self::Error> {
        self.super_ty_list(list)
    }

    fn try_fold_re(&mut self, re: Re) -> Result<Re, Self::Error> {
        self.super_re(re)
    }

    fn try_fold_ty(&mut self, ty: Ty) -> Result<Ty, Self::Error> {
        self.super_ty(ty)
    }

    fn try_fold_sig_self_ty_use(&mut self) -> Result<Ty, Self::Error> {
        self.super_sig_self_ty_use()
    }

    fn try_fold_re_infer_var_use(&mut self, var: InferReVar) -> Result<Re, Self::Error> {
        self.super_re_infer_var_use(var)
    }

    fn try_fold_re_universal_var_use(&mut self, var: UniversalReVar) -> Result<Re, Self::Error> {
        self.super_re_universal_var_use(var)
    }

    fn try_fold_ty_infer_var_use(&mut self, var: InferTyVar) -> Result<Ty, Self::Error> {
        self.super_ty_infer_var_use(var)
    }

    fn try_fold_ty_universal_var_use(&mut self, var: UniversalTyVar) -> Result<Ty, Self::Error> {
        self.super_ty_universal_var_use(var)
    }

    fn try_fold_re_sig_generic_use(
        &mut self,
        generic: Obj<RegionGeneric>,
    ) -> Result<Re, Self::Error> {
        self.super_re_sig_generic_use(generic)
    }

    fn try_fold_ty_sig_generic_use(
        &mut self,
        generic: Obj<TypeGeneric>,
    ) -> Result<Ty, Self::Error> {
        self.super_ty_sig_generic_use(generic)
    }
}

pub trait TyFolderSuper<'tcx>: TyFolder<'tcx> {
    // === Clauses === //

    fn super_clause_list(
        &mut self,
        clauses: TraitClauseList,
    ) -> Result<TraitClauseList, Self::Error> {
        let list = clauses.r(self.session());
        let mut out = Vec::with_capacity(list.len());

        for &ty in list {
            out.push(self.try_fold_clause(ty)?);
        }

        Ok(self.tcx().intern_list(&out))
    }

    fn super_clause(&mut self, clause: TraitClause) -> Result<TraitClause, Self::Error> {
        match clause {
            TraitClause::Outlives(re) => Ok(TraitClause::Outlives(self.try_fold_re(re)?)),
            TraitClause::Trait(spec) => Ok(TraitClause::Trait(self.try_fold_trait_spec(spec)?)),
        }
    }

    fn super_param_list(&mut self, params: TraitParamList) -> Result<TraitParamList, Self::Error> {
        let list = params.r(self.session());
        let mut out = Vec::with_capacity(list.len());

        for &ty in list {
            out.push(self.try_fold_param(ty)?);
        }

        Ok(self.tcx().intern_list(&out))
    }

    fn super_param(&mut self, param: TraitParam) -> Result<TraitParam, Self::Error> {
        match param {
            TraitParam::Equals(ty_or_re) => {
                Ok(TraitParam::Equals(self.try_fold_ty_or_re(ty_or_re)?))
            }
            TraitParam::Unspecified(clauses) => {
                Ok(TraitParam::Unspecified(self.try_fold_clause_list(clauses)?))
            }
        }
    }

    // === Instances === //

    fn super_trait_spec(&mut self, spec: TraitSpec) -> Result<TraitSpec, Self::Error> {
        Ok(TraitSpec {
            def: spec.def,
            params: self.try_fold_param_list(spec.params)?,
        })
    }

    fn super_trait_instance(
        &mut self,
        instance: TraitInstance,
    ) -> Result<TraitInstance, Self::Error> {
        Ok(TraitInstance {
            def: instance.def,
            params: self.try_fold_ty_or_re_list(instance.params)?,
        })
    }

    fn super_adt_instance(&mut self, instance: AdtInstance) -> Result<AdtInstance, Self::Error> {
        Ok(AdtInstance {
            def: instance.def,
            params: self.try_fold_ty_or_re_list(instance.params)?,
        })
    }

    // === Types === //

    fn super_ty_or_re(&mut self, ty_or_re: TyOrRe) -> Result<TyOrRe, Self::Error> {
        match ty_or_re {
            TyOrRe::Re(re) => Ok(TyOrRe::Re(self.try_fold_re(re)?)),
            TyOrRe::Ty(ty) => Ok(TyOrRe::Ty(self.try_fold_ty(ty)?)),
        }
    }

    fn super_ty_or_re_list(&mut self, list: TyOrReList) -> Result<TyOrReList, Self::Error> {
        let list = list.r(self.session());
        let mut out = Vec::with_capacity(list.len());

        for &ty in list {
            out.push(self.try_fold_ty_or_re(ty)?);
        }

        Ok(self.tcx().intern_list(&out))
    }

    fn super_ty_list(&mut self, list: TyList) -> Result<TyList, Self::Error> {
        let list = list.r(self.session());
        let mut out = Vec::with_capacity(list.len());

        for &ty in list {
            out.push(self.try_fold_ty(ty)?);
        }

        Ok(self.tcx().intern_list(&out))
    }

    fn super_re(&mut self, re: Re) -> Result<Re, Self::Error> {
        match re {
            Re::Gc | Re::SigExplicitInfer | Re::Erased | Re::Error(_) => Ok(re),
            Re::InferVar(var) => self.try_fold_re_infer_var_use(var),
            Re::UniversalVar(var) => self.try_fold_re_universal_var_use(var),
            Re::SigGeneric(generic) => self.try_fold_re_sig_generic_use(generic),
        }
    }

    fn super_ty(&mut self, ty: Ty) -> Result<Ty, Self::Error> {
        let tcx = self.tcx();

        match *ty.r(&tcx.session) {
            TyKind::Simple(_) | TyKind::SigExplicitInfer | TyKind::Error(_) => Ok(ty),
            TyKind::InferVar(var) => self.try_fold_ty_infer_var_use(var),
            TyKind::UniversalVar(var) => self.try_fold_ty_universal_var_use(var),
            TyKind::SigThis => self.try_fold_sig_self_ty_use(),
            TyKind::Reference(re, muta, pointee) => Ok(tcx.intern(TyKind::Reference(
                self.try_fold_re(re)?,
                muta,
                self.try_fold_ty(pointee)?,
            ))),
            TyKind::Adt(instance) => {
                Ok(tcx.intern(TyKind::Adt(self.try_fold_adt_instance(instance)?)))
            }
            TyKind::FnDef(def, Some(args)) => {
                Ok(tcx.intern(TyKind::FnDef(def, Some(self.try_fold_ty_or_re_list(args)?))))
            }
            TyKind::FnDef(def, None) => Ok(tcx.intern(TyKind::FnDef(def, None))),
            TyKind::Trait(clause_list) => {
                Ok(tcx.intern(TyKind::Trait(self.try_fold_clause_list(clause_list)?)))
            }
            TyKind::Tuple(tys) => Ok(tcx.intern(TyKind::Tuple(self.try_fold_ty_list(tys)?))),
            TyKind::SigGeneric(generic) => self.try_fold_ty_sig_generic_use(generic),
        }
    }

    fn super_sig_self_ty_use(&mut self) -> Result<Ty, Self::Error> {
        Ok(self.tcx().intern(TyKind::SigThis))
    }

    fn super_re_infer_var_use(&mut self, var: InferReVar) -> Result<Re, Self::Error> {
        Ok(Re::InferVar(var))
    }

    fn super_re_universal_var_use(&mut self, var: UniversalReVar) -> Result<Re, Self::Error> {
        Ok(Re::UniversalVar(var))
    }

    fn super_ty_infer_var_use(&mut self, var: InferTyVar) -> Result<Ty, Self::Error> {
        Ok(self.tcx().intern(TyKind::InferVar(var)))
    }

    fn super_ty_universal_var_use(&mut self, var: UniversalTyVar) -> Result<Ty, Self::Error> {
        Ok(self.tcx().intern(TyKind::UniversalVar(var)))
    }

    fn super_re_sig_generic_use(&mut self, generic: Obj<RegionGeneric>) -> Result<Re, Self::Error> {
        Ok(Re::SigGeneric(generic))
    }

    fn super_ty_sig_generic_use(&mut self, generic: Obj<TypeGeneric>) -> Result<Ty, Self::Error> {
        Ok(self.tcx().intern(TyKind::SigGeneric(generic)))
    }
}

impl<'tcx, T: ?Sized + TyFolder<'tcx>> TyFolderSuper<'tcx> for T {}

pub trait TyFolderInfallible<'tcx>: TyFolder<'tcx, Error = Infallible> {
    fn fold_clause_list(&mut self, clauses: TraitClauseList) -> TraitClauseList {
        let Ok(v) = self.try_fold_clause_list(clauses);
        v
    }

    fn fold_clause(&mut self, clause: TraitClause) -> TraitClause {
        let Ok(v) = self.try_fold_clause(clause);
        v
    }

    fn fold_param_list(&mut self, params: TraitParamList) -> TraitParamList {
        let Ok(v) = self.try_fold_param_list(params);
        v
    }

    fn fold_param(&mut self, param: TraitParam) -> TraitParam {
        let Ok(v) = self.try_fold_param(param);
        v
    }

    // === Instances === //

    fn fold_trait_spec(&mut self, spec: TraitSpec) -> TraitSpec {
        let Ok(v) = self.try_fold_trait_spec(spec);
        v
    }

    fn fold_trait_instance(&mut self, instance: TraitInstance) -> TraitInstance {
        let Ok(v) = self.try_fold_trait_instance(instance);
        v
    }

    fn fold_adt_instance(&mut self, instance: AdtInstance) -> AdtInstance {
        let Ok(v) = self.try_fold_adt_instance(instance);
        v
    }

    // === Types === //

    fn fold_ty_or_re(&mut self, ty_or_re: TyOrRe) -> TyOrRe {
        let Ok(v) = self.try_fold_ty_or_re(ty_or_re);
        v
    }

    fn fold_ty_or_re_list(&mut self, list: TyOrReList) -> TyOrReList {
        let Ok(v) = self.try_fold_ty_or_re_list(list);
        v
    }

    fn fold_ty_list(&mut self, list: TyList) -> TyList {
        let Ok(v) = self.try_fold_ty_list(list);
        v
    }

    fn fold_re(&mut self, re: Re) -> Re {
        let Ok(v) = self.try_fold_re(re);
        v
    }

    fn fold_ty(&mut self, ty: Ty) -> Ty {
        let Ok(v) = self.try_fold_ty(ty);
        v
    }

    fn fold_self_ty_use(&mut self) -> Ty {
        let Ok(v) = self.try_fold_sig_self_ty_use();
        v
    }

    fn fold_re_infer_use(&mut self, var: InferReVar) -> Re {
        let Ok(v) = self.try_fold_re_infer_var_use(var);
        v
    }

    fn fold_ty_infer_use(&mut self, var: InferTyVar) -> Ty {
        let Ok(v) = self.try_fold_ty_infer_var_use(var);
        v
    }

    fn fold_re_generic_use(&mut self, generic: Obj<RegionGeneric>) -> Re {
        let Ok(v) = self.try_fold_re_sig_generic_use(generic);
        v
    }

    fn fold_ty_generic_use(&mut self, generic: Obj<TypeGeneric>) -> Ty {
        let Ok(v) = self.try_fold_ty_sig_generic_use(generic);
        v
    }
}

impl<'tcx, T: ?Sized + TyFolder<'tcx, Error = Infallible>> TyFolderInfallible<'tcx> for T {}

pub trait TyFolderPreservesSpans<'tcx>: TyFolder<'tcx> {
    fn try_fold_spanned_clause_list(
        &mut self,
        clauses: SpannedTraitClauseList,
    ) -> Result<SpannedTraitClauseList, Self::Error> {
        self.try_fold_clause_list(clauses.value)
            .map(|value| Spanned::new_raw(value, clauses.span_info))
    }

    fn try_fold_spanned_clause(
        &mut self,
        clause: SpannedTraitClause,
    ) -> Result<SpannedTraitClause, Self::Error> {
        self.try_fold_clause(clause.value)
            .map(|value| Spanned::new_raw(value, clause.span_info))
    }

    fn try_fold_spanned_param_list(
        &mut self,
        params: SpannedTraitParamList,
    ) -> Result<SpannedTraitParamList, Self::Error> {
        self.try_fold_param_list(params.value)
            .map(|value| Spanned::new_raw(value, params.span_info))
    }

    fn try_fold_spanned_param(
        &mut self,
        param: SpannedTraitParam,
    ) -> Result<SpannedTraitParam, Self::Error> {
        self.try_fold_param(param.value)
            .map(|value| Spanned::new_raw(value, param.span_info))
    }

    // === Instances === //

    fn try_fold_spanned_trait_spec(
        &mut self,
        spec: SpannedTraitSpec,
    ) -> Result<SpannedTraitSpec, Self::Error> {
        self.try_fold_trait_spec(spec.value)
            .map(|value| Spanned::new_raw(value, spec.span_info))
    }

    fn try_fold_spanned_trait_instance(
        &mut self,
        instance: SpannedTraitInstance,
    ) -> Result<SpannedTraitInstance, Self::Error> {
        self.try_fold_trait_instance(instance.value)
            .map(|value| Spanned::new_raw(value, instance.span_info))
    }

    fn try_fold_spanned_adt_instance(
        &mut self,
        instance: SpannedAdtInstance,
    ) -> Result<SpannedAdtInstance, Self::Error> {
        self.try_fold_adt_instance(instance.value)
            .map(|value| Spanned::new_raw(value, instance.span_info))
    }

    // === Types === //

    fn try_fold_spanned_ty_or_re(
        &mut self,
        ty_or_re: SpannedTyOrRe,
    ) -> Result<SpannedTyOrRe, Self::Error> {
        self.try_fold_ty_or_re(ty_or_re.value)
            .map(|value| Spanned::new_raw(value, ty_or_re.span_info))
    }

    fn try_fold_spanned_ty_or_re_list(
        &mut self,
        list: SpannedTyOrReList,
    ) -> Result<SpannedTyOrReList, Self::Error> {
        self.try_fold_ty_or_re_list(list.value)
            .map(|value| Spanned::new_raw(value, list.span_info))
    }

    fn try_fold_spanned_ty_list(
        &mut self,
        list: SpannedTyList,
    ) -> Result<SpannedTyList, Self::Error> {
        self.try_fold_ty_list(list.value)
            .map(|value| Spanned::new_raw(value, list.span_info))
    }

    fn try_fold_spanned_re(&mut self, re: SpannedRe) -> Result<SpannedRe, Self::Error> {
        self.try_fold_re(re.value)
            .map(|value| Spanned::new_raw(value, re.span_info))
    }

    fn try_fold_spanned_ty(&mut self, ty: SpannedTy) -> Result<SpannedTy, Self::Error> {
        self.try_fold_ty(ty.value)
            .map(|value| Spanned::new_raw(value, ty.span_info))
    }
}

pub trait TyFolderInfalliblePreservesSpans<'tcx>:
    TyFolderPreservesSpans<'tcx, Error = Infallible>
{
    fn fold_spanned_clause_list(
        &mut self,
        clauses: SpannedTraitClauseList,
    ) -> SpannedTraitClauseList {
        let Ok(v) = self.try_fold_spanned_clause_list(clauses);
        v
    }

    fn fold_spanned_clause(&mut self, clause: SpannedTraitClause) -> SpannedTraitClause {
        let Ok(v) = self.try_fold_spanned_clause(clause);
        v
    }

    fn fold_spanned_param_list(&mut self, params: SpannedTraitParamList) -> SpannedTraitParamList {
        let Ok(v) = self.try_fold_spanned_param_list(params);
        v
    }

    fn fold_spanned_param(&mut self, param: SpannedTraitParam) -> SpannedTraitParam {
        let Ok(v) = self.try_fold_spanned_param(param);
        v
    }

    // === Instances === //

    fn fold_spanned_trait_spec(&mut self, spec: SpannedTraitSpec) -> SpannedTraitSpec {
        let Ok(v) = self.try_fold_spanned_trait_spec(spec);
        v
    }

    fn fold_spanned_trait_instance(
        &mut self,
        instance: SpannedTraitInstance,
    ) -> SpannedTraitInstance {
        let Ok(v) = self.try_fold_spanned_trait_instance(instance);
        v
    }

    fn fold_spanned_adt_instance(&mut self, instance: SpannedAdtInstance) -> SpannedAdtInstance {
        let Ok(v) = self.try_fold_spanned_adt_instance(instance);
        v
    }

    // === Types === //

    fn fold_spanned_ty_or_re(&mut self, ty_or_re: SpannedTyOrRe) -> SpannedTyOrRe {
        let Ok(v) = self.try_fold_spanned_ty_or_re(ty_or_re);
        v
    }

    fn fold_spanned_ty_or_re_list(&mut self, list: SpannedTyOrReList) -> SpannedTyOrReList {
        let Ok(v) = self.try_fold_spanned_ty_or_re_list(list);
        v
    }

    fn fold_spanned_ty_list(&mut self, list: SpannedTyList) -> SpannedTyList {
        let Ok(v) = self.try_fold_spanned_ty_list(list);
        v
    }

    fn fold_spanned_re(&mut self, re: SpannedRe) -> SpannedRe {
        let Ok(v) = self.try_fold_spanned_re(re);
        v
    }

    fn fold_spanned_ty(&mut self, ty: SpannedTy) -> SpannedTy {
        let Ok(v) = self.try_fold_spanned_ty(ty);
        v
    }
}

impl<'tcx, T> TyFolderInfalliblePreservesSpans<'tcx> for T where
    T: ?Sized + TyFolderPreservesSpans<'tcx, Error = Infallible>
{
}
