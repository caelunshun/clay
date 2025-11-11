use crate::{
    base::{Session, analysis::Spanned, arena::Obj, syntax::Span},
    semantic::{
        analysis::TyCtxt,
        syntax::{
            AdtDef, AdtInstance, AnyGeneric, Crate, GenericBinder, ImplDef, Item, ItemKind, Re,
            RegionGeneric, SpannedAdtInstance, SpannedAdtInstanceView, SpannedRe,
            SpannedTraitClause, SpannedTraitClauseList, SpannedTraitClauseView,
            SpannedTraitInstance, SpannedTraitInstanceView, SpannedTraitParam,
            SpannedTraitParamList, SpannedTraitParamView, SpannedTraitSpec, SpannedTraitSpecView,
            SpannedTy, SpannedTyList, SpannedTyOrRe, SpannedTyOrReList, SpannedTyOrReView,
            SpannedTyView, TraitClause, TraitClauseList, TraitDef, TraitInstance, TraitParam,
            TraitParamList, TraitSpec, Ty, TyKind, TyList, TyOrRe, TyOrReList, TypeGeneric,
        },
    },
};
use std::{convert::Infallible, ops::ControlFlow};

// === Visitor === //

pub trait TyVisitor<'tcx> {
    type Break;

    fn tcx(&self) -> &'tcx TyCtxt;

    fn session(&self) -> &'tcx Session {
        &self.tcx().session
    }

    // === Items === //

    fn visit_crate(&mut self, krate: Obj<Crate>) -> ControlFlow<Self::Break> {
        self.walk_crate(krate)
    }

    fn visit_item(&mut self, item: Obj<Item>) -> ControlFlow<Self::Break> {
        self.walk_item(item)
    }

    fn visit_trait(&mut self, def: Obj<TraitDef>) -> ControlFlow<Self::Break> {
        self.walk_trait(def)
    }

    fn visit_adt(&mut self, def: Obj<AdtDef>) -> ControlFlow<Self::Break> {
        self.walk_adt(def)
    }

    fn visit_impl(&mut self, def: Obj<ImplDef>) -> ControlFlow<Self::Break> {
        self.walk_impl(def)
    }

    fn visit_generic_binder(&mut self, binder: Obj<GenericBinder>) -> ControlFlow<Self::Break> {
        self.walk_generic_binder(binder)
    }

    fn visit_any_generic_def(&mut self, generic: AnyGeneric) -> ControlFlow<Self::Break> {
        self.walk_any_generic_def(generic)
    }

    fn visit_ty_generic_def(&mut self, generic: Obj<TypeGeneric>) -> ControlFlow<Self::Break> {
        self.walk_ty_generic_def(generic)
    }

    fn visit_re_generic_def(&mut self, generic: Obj<RegionGeneric>) -> ControlFlow<Self::Break> {
        self.walk_re_generic_def(generic)
    }

    // === Clauses === //

    fn visit_spanned_clause_list(
        &mut self,
        clauses: SpannedTraitClauseList,
    ) -> ControlFlow<Self::Break> {
        self.walk_clause_list(clauses)
    }

    fn visit_spanned_clause(&mut self, clause: SpannedTraitClause) -> ControlFlow<Self::Break> {
        self.walk_clause(clause)
    }

    fn visit_spanned_param_list(
        &mut self,
        params: SpannedTraitParamList,
    ) -> ControlFlow<Self::Break> {
        self.walk_param_list(params)
    }

    fn visit_spanned_param(&mut self, param: SpannedTraitParam) -> ControlFlow<Self::Break> {
        self.walk_param(param)
    }

    // === Instances === //

    fn visit_spanned_trait_spec(&mut self, spec: SpannedTraitSpec) -> ControlFlow<Self::Break> {
        self.walk_trait_spec(spec)
    }

    fn visit_spanned_trait_instance(
        &mut self,
        instance: SpannedTraitInstance,
    ) -> ControlFlow<Self::Break> {
        self.walk_trait_instance(instance)
    }

    fn visit_spanned_adt_instance(
        &mut self,
        instance: SpannedAdtInstance,
    ) -> ControlFlow<Self::Break> {
        self.walk_adt_instance(instance)
    }

    // === Types === //

    fn visit_spanned_ty_or_re(&mut self, ty_or_re: SpannedTyOrRe) -> ControlFlow<Self::Break> {
        self.walk_ty_or_re(ty_or_re)
    }

    fn visit_spanned_ty_or_re_list(&mut self, list: SpannedTyOrReList) -> ControlFlow<Self::Break> {
        self.walk_ty_or_re_list(list)
    }

    fn visit_spanned_ty_list(&mut self, list: SpannedTyList) -> ControlFlow<Self::Break> {
        self.walk_ty_list(list)
    }

    fn visit_spanned_re(&mut self, re: SpannedRe) -> ControlFlow<Self::Break> {
        self.walk_re(re)
    }

    fn visit_spanned_ty(&mut self, ty: SpannedTy) -> ControlFlow<Self::Break> {
        self.walk_ty(ty)
    }

    fn visit_spanned_self_ty_use(&mut self, span: Option<Span>) -> ControlFlow<Self::Break> {
        _ = span;

        ControlFlow::Continue(())
    }

    fn visit_spanned_re_generic_use(
        &mut self,
        span: Option<Span>,
        generic: Obj<RegionGeneric>,
    ) -> ControlFlow<Self::Break> {
        _ = (span, generic);

        ControlFlow::Continue(())
    }

    fn visit_spanned_ty_generic_use(
        &mut self,
        span: Option<Span>,
        generic: Obj<TypeGeneric>,
    ) -> ControlFlow<Self::Break> {
        _ = (span, generic);

        ControlFlow::Continue(())
    }
}

pub trait TyVisitorWalk<'tcx>: TyVisitor<'tcx> {
    // === Items === //

    fn walk_crate(&mut self, krate: Obj<Crate>) -> ControlFlow<Self::Break> {
        let s = self.session();

        for &item in krate.r(s).items.iter() {
            self.visit_item(item)?;
        }

        for &impl_ in krate.r(s).impls.iter() {
            self.visit_impl(impl_)?;
        }

        ControlFlow::Continue(())
    }

    fn walk_item(&mut self, item: Obj<Item>) -> ControlFlow<Self::Break> {
        let s = self.session();

        match *item.r(s).kind {
            ItemKind::Trait(def) => {
                self.visit_trait(def)?;
            }
            ItemKind::Adt(def) => {
                self.visit_adt(def)?;
            }
        }

        ControlFlow::Continue(())
    }

    fn walk_trait(&mut self, def: Obj<TraitDef>) -> ControlFlow<Self::Break> {
        let s = self.session();

        let TraitDef {
            item: _,
            generics,
            inherits,
            regular_generic_count: _,
            associated_types: _, // (in `generics`)
            methods,
            impls: _,
        } = def.r(s);

        self.visit_generic_binder(*generics)?;
        self.visit_spanned_clause_list(**inherits)?;

        // TODO: `methods`

        ControlFlow::Continue(())
    }

    fn walk_adt(&mut self, def: Obj<AdtDef>) -> ControlFlow<Self::Break> {
        todo!()
    }

    fn walk_impl(&mut self, def: Obj<ImplDef>) -> ControlFlow<Self::Break> {
        let s = self.session();
        let ImplDef {
            span: _,
            generics,
            trait_,
            target,
            methods,
            generic_solve_order: _,
        } = def.r(s);

        self.visit_generic_binder(*generics)?;
        self.visit_spanned_ty(*target)?;

        if let Some(trait_) = *trait_ {
            self.visit_spanned_trait_instance(trait_)?;
        }

        // TODO: `methods`

        ControlFlow::Continue(())
    }

    fn walk_generic_binder(&mut self, binder: Obj<GenericBinder>) -> ControlFlow<Self::Break> {
        let s = self.session();

        for &generic in &binder.r(s).generics {
            self.visit_any_generic_def(generic)?;
        }

        ControlFlow::Continue(())
    }

    fn walk_any_generic_def(&mut self, generic: AnyGeneric) -> ControlFlow<Self::Break> {
        match generic {
            AnyGeneric::Re(def) => self.visit_re_generic_def(def),
            AnyGeneric::Ty(def) => self.visit_ty_generic_def(def),
        }
    }

    fn walk_ty_generic_def(&mut self, generic: Obj<TypeGeneric>) -> ControlFlow<Self::Break> {
        let s = self.session();

        let TypeGeneric {
            span: _,
            ident: _,
            binder: _,
            user_clauses,
            elaborated_clauses: _,
            is_synthetic: _,
        } = generic.r(s);

        self.visit_spanned_clause_list(**user_clauses)?;

        ControlFlow::Continue(())
    }

    fn walk_re_generic_def(&mut self, generic: Obj<RegionGeneric>) -> ControlFlow<Self::Break> {
        let s = self.session();

        let RegionGeneric {
            span: _,
            lifetime: _,
            binder: _,
            clauses,
        } = generic.r(s);

        self.visit_spanned_clause_list(**clauses)?;

        ControlFlow::Continue(())
    }

    // === Clauses === //

    fn walk_clause_list(&mut self, clauses: SpannedTraitClauseList) -> ControlFlow<Self::Break> {
        for clause in clauses.iter(self.session()) {
            self.visit_spanned_clause(clause)?;
        }

        ControlFlow::Continue(())
    }

    fn walk_clause(&mut self, clause: SpannedTraitClause) -> ControlFlow<Self::Break> {
        match clause.view(self.tcx()) {
            SpannedTraitClauseView::Outlives(re) => {
                self.visit_spanned_re(re)?;
            }
            SpannedTraitClauseView::Trait(spec) => {
                self.visit_spanned_trait_spec(spec)?;
            }
        }

        ControlFlow::Continue(())
    }

    fn walk_param_list(&mut self, params: SpannedTraitParamList) -> ControlFlow<Self::Break> {
        for param in params.iter(self.session()) {
            self.visit_spanned_param(param)?;
        }

        ControlFlow::Continue(())
    }

    fn walk_param(&mut self, param: SpannedTraitParam) -> ControlFlow<Self::Break> {
        match param.view(self.tcx()) {
            SpannedTraitParamView::Equals(ty_or_re) => {
                self.walk_ty_or_re(ty_or_re)?;
            }
            SpannedTraitParamView::Unspecified(clauses) => {
                self.visit_spanned_clause_list(clauses)?;
            }
        }

        ControlFlow::Continue(())
    }

    // === Instances === //

    fn walk_trait_spec(&mut self, spec: SpannedTraitSpec) -> ControlFlow<Self::Break> {
        let SpannedTraitSpecView { def: _, params } = spec.view(self.tcx());
        self.visit_spanned_param_list(params)?;

        ControlFlow::Continue(())
    }

    fn walk_trait_instance(&mut self, instance: SpannedTraitInstance) -> ControlFlow<Self::Break> {
        let SpannedTraitInstanceView { def: _, params } = instance.view(self.tcx());
        self.visit_spanned_ty_or_re_list(params)?;

        ControlFlow::Continue(())
    }

    fn walk_adt_instance(&mut self, instance: SpannedAdtInstance) -> ControlFlow<Self::Break> {
        let SpannedAdtInstanceView { def: _, params } = instance.view(self.tcx());
        self.visit_spanned_ty_or_re_list(params)?;

        ControlFlow::Continue(())
    }

    // === Types === //

    fn walk_ty_or_re(&mut self, ty_or_re: SpannedTyOrRe) -> ControlFlow<Self::Break> {
        match ty_or_re.view(self.tcx()) {
            SpannedTyOrReView::Re(re) => self.visit_spanned_re(re),
            SpannedTyOrReView::Ty(ty) => self.visit_spanned_ty(ty),
        }
    }

    fn walk_ty_or_re_list(&mut self, list: SpannedTyOrReList) -> ControlFlow<Self::Break> {
        for ty_or_re in list.iter(self.session()) {
            self.visit_spanned_ty_or_re(ty_or_re)?;
        }

        ControlFlow::Continue(())
    }

    fn walk_ty_list(&mut self, list: SpannedTyList) -> ControlFlow<Self::Break> {
        for ty in list.iter(self.session()) {
            self.visit_spanned_ty(ty)?;
        }

        ControlFlow::Continue(())
    }

    fn walk_re(&mut self, re: SpannedRe) -> ControlFlow<Self::Break> {
        match re.value {
            Re::Gc | Re::InferVar(_) | Re::ExplicitInfer | Re::Erased => {
                // (dead end)
            }
            Re::Universal(generic) => {
                self.visit_spanned_re_generic_use(re.own_span(), generic)?;
            }
        }

        ControlFlow::Continue(())
    }

    fn walk_ty(&mut self, ty: SpannedTy) -> ControlFlow<Self::Break> {
        match ty.view(self.tcx()) {
            SpannedTyView::Simple(..)
            | SpannedTyView::FnDef(..)
            | SpannedTyView::ExplicitInfer
            | SpannedTyView::InferVar(..)
            | SpannedTyView::Error(..) => {
                // (dead end)
            }
            SpannedTyView::This => {
                self.visit_spanned_self_ty_use(ty.own_span())?;
            }
            SpannedTyView::Reference(re, pointee) => {
                self.visit_spanned_re(re)?;
                self.visit_spanned_ty(pointee)?;
            }
            SpannedTyView::Adt(instance) => {
                self.visit_spanned_adt_instance(instance)?;
            }
            SpannedTyView::Trait(clause_list) => {
                self.visit_spanned_clause_list(clause_list)?;
            }
            SpannedTyView::Tuple(tys) => {
                self.visit_spanned_ty_list(tys)?;
            }
            SpannedTyView::Universal(generic) => {
                self.visit_spanned_ty_generic_use(ty.own_span(), generic)?;
            }
        }

        ControlFlow::Continue(())
    }
}

impl<'tcx, T: ?Sized + TyVisitor<'tcx>> TyVisitorWalk<'tcx> for T {}

pub trait TyVisitorUnspanned<'tcx>: TyVisitor<'tcx> {
    // === Clauses === //

    fn visit_clause_list(&mut self, clauses: TraitClauseList) -> ControlFlow<Self::Break> {
        self.visit_spanned_clause_list(Spanned::new_unspanned(clauses))
    }

    fn visit_clause(&mut self, clause: TraitClause) -> ControlFlow<Self::Break> {
        self.visit_spanned_clause(Spanned::new_unspanned(clause))
    }

    fn visit_param_list(&mut self, params: TraitParamList) -> ControlFlow<Self::Break> {
        self.visit_spanned_param_list(Spanned::new_unspanned(params))
    }

    fn visit_param(&mut self, param: TraitParam) -> ControlFlow<Self::Break> {
        self.visit_spanned_param(Spanned::new_unspanned(param))
    }

    // === Instances === //

    fn visit_trait_spec(&mut self, spec: TraitSpec) -> ControlFlow<Self::Break> {
        self.visit_spanned_trait_spec(Spanned::new_unspanned(spec))
    }

    fn visit_trait_instance(&mut self, instance: TraitInstance) -> ControlFlow<Self::Break> {
        self.visit_spanned_trait_instance(Spanned::new_unspanned(instance))
    }

    fn visit_adt_instance(&mut self, instance: AdtInstance) -> ControlFlow<Self::Break> {
        self.visit_spanned_adt_instance(Spanned::new_unspanned(instance))
    }

    // === Types === //

    fn visit_ty_or_re(&mut self, ty_or_re: TyOrRe) -> ControlFlow<Self::Break> {
        self.visit_spanned_ty_or_re(Spanned::new_unspanned(ty_or_re))
    }

    fn visit_ty_or_re_list(&mut self, list: TyOrReList) -> ControlFlow<Self::Break> {
        self.visit_spanned_ty_or_re_list(Spanned::new_unspanned(list))
    }

    fn visit_ty_list(&mut self, list: TyList) -> ControlFlow<Self::Break> {
        self.visit_spanned_ty_list(Spanned::new_unspanned(list))
    }

    fn visit_re(&mut self, re: Re) -> ControlFlow<Self::Break> {
        self.visit_spanned_re(Spanned::new_unspanned(re))
    }

    fn visit_ty(&mut self, ty: Ty) -> ControlFlow<Self::Break> {
        self.visit_spanned_ty(Spanned::new_unspanned(ty))
    }

    fn visit_self_ty_use(&mut self) -> ControlFlow<Self::Break> {
        self.visit_spanned_self_ty_use(None)
    }

    fn visit_re_generic_use(&mut self, generic: Obj<RegionGeneric>) -> ControlFlow<Self::Break> {
        self.visit_spanned_re_generic_use(None, generic)
    }

    fn visit_ty_generic_use(&mut self, generic: Obj<TypeGeneric>) -> ControlFlow<Self::Break> {
        self.visit_spanned_ty_generic_use(None, generic)
    }
}

impl<'tcx, T: ?Sized + TyVisitor<'tcx>> TyVisitorUnspanned<'tcx> for T {}

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

    fn try_fold_self_ty_use(&mut self) -> Result<Ty, Self::Error> {
        self.super_self_ty_use()
    }

    fn try_fold_re_generic_use(&mut self, generic: Obj<RegionGeneric>) -> Result<Re, Self::Error> {
        self.super_re_generic_use(generic)
    }

    fn try_fold_ty_generic_use(&mut self, generic: Obj<TypeGeneric>) -> Result<Ty, Self::Error> {
        self.super_ty_generic_use(generic)
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

        Ok(self.tcx().intern_trait_clause_list(&out))
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

        Ok(self.tcx().intern_trait_param_list(&out))
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

        Ok(self.tcx().intern_ty_or_re_list(&out))
    }

    fn super_ty_list(&mut self, list: TyList) -> Result<TyList, Self::Error> {
        let list = list.r(self.session());
        let mut out = Vec::with_capacity(list.len());

        for &ty in list {
            out.push(self.try_fold_ty(ty)?);
        }

        Ok(self.tcx().intern_ty_list(&out))
    }

    fn super_re(&mut self, re: Re) -> Result<Re, Self::Error> {
        match re {
            Re::Gc | Re::InferVar(_) | Re::ExplicitInfer | Re::Erased => Ok(re),
            Re::Universal(generic) => self.try_fold_re_generic_use(generic),
        }
    }

    fn super_ty(&mut self, ty: Ty) -> Result<Ty, Self::Error> {
        let tcx = self.tcx();

        match *ty.r(&tcx.session) {
            TyKind::Simple(..)
            | TyKind::FnDef(..)
            | TyKind::ExplicitInfer
            | TyKind::InferVar(..)
            | TyKind::Error(..) => Ok(ty),
            TyKind::This => self.try_fold_self_ty_use(),
            TyKind::Reference(re, pointee) => Ok(tcx.intern_ty(TyKind::Reference(
                self.try_fold_re(re)?,
                self.try_fold_ty(pointee)?,
            ))),
            TyKind::Adt(instance) => {
                Ok(tcx.intern_ty(TyKind::Adt(self.try_fold_adt_instance(instance)?)))
            }
            TyKind::Trait(clause_list) => {
                Ok(tcx.intern_ty(TyKind::Trait(self.try_fold_clause_list(clause_list)?)))
            }
            TyKind::Tuple(tys) => Ok(tcx.intern_ty(TyKind::Tuple(self.try_fold_ty_list(tys)?))),
            TyKind::Universal(generic) => self.try_fold_ty_generic_use(generic),
        }
    }

    fn super_self_ty_use(&mut self) -> Result<Ty, Self::Error> {
        Ok(self.tcx().intern_ty(TyKind::This))
    }

    fn super_re_generic_use(&mut self, generic: Obj<RegionGeneric>) -> Result<Re, Self::Error> {
        Ok(Re::Universal(generic))
    }

    fn super_ty_generic_use(&mut self, generic: Obj<TypeGeneric>) -> Result<Ty, Self::Error> {
        Ok(self.tcx().intern_ty(TyKind::Universal(generic)))
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
        let Ok(v) = self.try_fold_self_ty_use();
        v
    }

    fn fold_re_generic_use(&mut self, generic: Obj<RegionGeneric>) -> Re {
        let Ok(v) = self.try_fold_re_generic_use(generic);
        v
    }

    fn fold_ty_generic_use(&mut self, generic: Obj<TypeGeneric>) -> Ty {
        let Ok(v) = self.try_fold_ty_generic_use(generic);
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
