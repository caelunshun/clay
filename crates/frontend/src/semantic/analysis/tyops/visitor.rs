use crate::{
    base::{Session, arena::Obj},
    semantic::{
        analysis::TyCtxt,
        syntax::{
            AdtDef, AdtInstance, AnyGeneric, Crate, GenericBinder, ImplDef, Item, ItemKind, Re,
            RegionGeneric, TraitClause, TraitClauseList, TraitDef, TraitInstance, TraitParam,
            TraitParamList, TraitSpec, Ty, TyKind, TyList, TyOrRe, TyOrReList, TypeGeneric,
        },
    },
};
use std::ops::ControlFlow;

// === Visitor === //

pub trait TyVisitor<'tcx> {
    type Break;

    fn tcx(&self) -> &'tcx TyCtxt;

    fn session(&self) -> &'tcx Session {
        &self.tcx().session
    }

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

    fn visit_item(&mut self, item: Obj<Item>) -> ControlFlow<Self::Break> {
        self.walk_item(item)
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

    fn visit_trait(&mut self, def: Obj<TraitDef>) -> ControlFlow<Self::Break> {
        self.walk_trait(def)
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
        self.visit_clause_list(**inherits)?;

        // TODO: `methods`

        ControlFlow::Continue(())
    }

    fn visit_adt(&mut self, def: Obj<AdtDef>) -> ControlFlow<Self::Break> {
        self.walk_adt(def)
    }

    fn walk_adt(&mut self, def: Obj<AdtDef>) -> ControlFlow<Self::Break> {
        todo!()
    }

    fn visit_impl(&mut self, def: Obj<ImplDef>) -> ControlFlow<Self::Break> {
        self.walk_impl(def)
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
        self.visit_ty(*target)?;

        if let Some(trait_) = *trait_ {
            self.walk_trait_instance(trait_)?;
        }

        // TODO: `methods`

        ControlFlow::Continue(())
    }

    fn visit_generic_binder(&mut self, binder: Obj<GenericBinder>) -> ControlFlow<Self::Break> {
        self.walk_generic_binder(binder)
    }

    fn walk_generic_binder(&mut self, binder: Obj<GenericBinder>) -> ControlFlow<Self::Break> {
        let s = self.session();

        for &generic in &binder.r(s).generics {
            self.walk_any_generic_def(generic)?;
        }

        ControlFlow::Continue(())
    }

    fn walk_any_generic_def(&mut self, generic: AnyGeneric) -> ControlFlow<Self::Break> {
        match generic {
            AnyGeneric::Re(def) => self.visit_re_generic_def(def),
            AnyGeneric::Ty(def) => self.visit_ty_generic_def(def),
        }
    }

    fn visit_ty_generic_def(&mut self, generic: Obj<TypeGeneric>) -> ControlFlow<Self::Break> {
        self.walk_ty_generic_def(generic)
    }

    fn walk_ty_generic_def(&mut self, generic: Obj<TypeGeneric>) -> ControlFlow<Self::Break> {
        let s = self.session();

        let TypeGeneric {
            span: _,
            ident: _,
            binder: _,
            user_clauses,
            instantiated_clauses: _,
            is_synthetic: _,
        } = generic.r(s);

        self.visit_clause_list(**user_clauses)?;

        ControlFlow::Continue(())
    }

    fn visit_re_generic_def(&mut self, generic: Obj<RegionGeneric>) -> ControlFlow<Self::Break> {
        self.walk_re_generic_def(generic)
    }

    fn walk_re_generic_def(&mut self, generic: Obj<RegionGeneric>) -> ControlFlow<Self::Break> {
        let s = self.session();

        let RegionGeneric {
            span: _,
            lifetime: _,
            binder: _,
            clauses,
        } = generic.r(s);

        self.visit_clause_list(**clauses)?;

        ControlFlow::Continue(())
    }

    // === Clauses === //

    fn visit_clause_list(&mut self, clauses: TraitClauseList) -> ControlFlow<Self::Break> {
        self.walk_clause_list(clauses)
    }

    fn walk_clause_list(&mut self, clauses: TraitClauseList) -> ControlFlow<Self::Break> {
        for &clause in clauses.r(self.session()) {
            self.visit_clause(clause)?;
        }

        ControlFlow::Continue(())
    }

    fn visit_clause(&mut self, clause: TraitClause) -> ControlFlow<Self::Break> {
        self.walk_clause(clause)
    }

    fn walk_clause(&mut self, clause: TraitClause) -> ControlFlow<Self::Break> {
        match clause {
            TraitClause::Outlives(re) => {
                self.visit_re(re)?;
            }
            TraitClause::Trait(spec) => {
                self.visit_trait_spec(spec)?;
            }
        }

        ControlFlow::Continue(())
    }

    fn visit_param_list(&mut self, params: TraitParamList) -> ControlFlow<Self::Break> {
        self.walk_param_list(params)
    }

    fn walk_param_list(&mut self, params: TraitParamList) -> ControlFlow<Self::Break> {
        for &param in params.r(self.session()) {
            self.visit_param(param)?;
        }

        ControlFlow::Continue(())
    }

    fn visit_param(&mut self, param: TraitParam) -> ControlFlow<Self::Break> {
        self.walk_param(param)
    }

    fn walk_param(&mut self, param: TraitParam) -> ControlFlow<Self::Break> {
        match param {
            TraitParam::Equals(ty_or_re) => {
                self.walk_ty_or_re(ty_or_re)?;
            }
            TraitParam::Unspecified(clauses) => {
                self.visit_clause_list(clauses)?;
            }
        }

        ControlFlow::Continue(())
    }

    // === Instances === //

    fn visit_trait_spec(&mut self, spec: TraitSpec) -> ControlFlow<Self::Break> {
        self.walk_trait_spec(spec)
    }

    fn walk_trait_spec(&mut self, spec: TraitSpec) -> ControlFlow<Self::Break> {
        let TraitSpec { def: _, params } = spec;
        self.visit_param_list(params)?;

        ControlFlow::Continue(())
    }

    fn visit_trait_instance(&mut self, instance: TraitInstance) -> ControlFlow<Self::Break> {
        self.walk_trait_instance(instance)
    }

    fn walk_trait_instance(&mut self, instance: TraitInstance) -> ControlFlow<Self::Break> {
        let TraitInstance { def: _, params } = instance;
        self.walk_ty_or_re_list(params)?;

        ControlFlow::Continue(())
    }

    fn visit_adt_instance(&mut self, instance: AdtInstance) -> ControlFlow<Self::Break> {
        self.walk_adt_instance(instance)
    }

    fn walk_adt_instance(&mut self, instance: AdtInstance) -> ControlFlow<Self::Break> {
        let AdtInstance { def: _, params } = instance;
        self.walk_ty_or_re_list(params)?;

        ControlFlow::Continue(())
    }

    // === Types === //

    fn walk_ty_or_re(&mut self, ty_or_re: TyOrRe) -> ControlFlow<Self::Break> {
        match ty_or_re {
            TyOrRe::Re(re) => self.visit_re(re),
            TyOrRe::Ty(ty) => self.visit_ty(ty),
        }
    }

    fn walk_ty_or_re_list(&mut self, list: TyOrReList) -> ControlFlow<Self::Break> {
        for &ty_or_re in list.r(self.session()) {
            self.walk_ty_or_re(ty_or_re)?;
        }

        ControlFlow::Continue(())
    }

    fn walk_ty_list(&mut self, list: TyList) -> ControlFlow<Self::Break> {
        for &ty in list.r(self.session()) {
            self.walk_ty(ty)?;
        }

        ControlFlow::Continue(())
    }

    fn visit_re(&mut self, re: Re) -> ControlFlow<Self::Break> {
        self.walk_re(re)
    }

    fn walk_re(&mut self, re: Re) -> ControlFlow<Self::Break> {
        match re {
            Re::Gc | Re::InferVar(_) | Re::ExplicitInfer | Re::Erased => {
                // (dead end)
            }
            Re::Universal(generic) => {
                self.visit_re_generic_use(generic)?;
            }
        }

        ControlFlow::Continue(())
    }

    fn visit_ty(&mut self, ty: Ty) -> ControlFlow<Self::Break> {
        self.walk_ty(ty)
    }

    fn walk_ty(&mut self, ty: Ty) -> ControlFlow<Self::Break> {
        let s = self.session();

        match *ty.r(s) {
            TyKind::Simple(..)
            | TyKind::FnDef(..)
            | TyKind::ExplicitInfer
            | TyKind::InferVar(..)
            | TyKind::Error(..) => {
                // (dead end)
            }
            TyKind::This => {
                self.visit_self_ty_use()?;
            }
            TyKind::Reference(re, pointee) => {
                self.visit_re(re)?;
                self.visit_ty(pointee)?;
            }
            TyKind::Adt(instance) => {
                self.walk_adt_instance(instance)?;
            }
            TyKind::Trait(clause_list) => {
                self.visit_clause_list(clause_list)?;
            }
            TyKind::Tuple(tys) => {
                self.walk_ty_list(tys)?;
            }
            TyKind::Universal(generic) => {
                self.visit_ty_generic_use(generic)?;
            }
        }

        ControlFlow::Continue(())
    }

    fn visit_self_ty_use(&mut self) -> ControlFlow<Self::Break> {
        ControlFlow::Continue(())
    }

    fn visit_re_generic_use(&mut self, generic: Obj<RegionGeneric>) -> ControlFlow<Self::Break> {
        _ = generic;

        ControlFlow::Continue(())
    }

    fn visit_ty_generic_use(&mut self, generic: Obj<TypeGeneric>) -> ControlFlow<Self::Break> {
        _ = generic;

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

    fn visit_clause_list(
        &mut self,
        clauses: TraitClauseList,
    ) -> Result<TraitClauseList, Self::Error> {
        self.walk_clause_list(clauses)
    }

    fn walk_clause_list(
        &mut self,
        clauses: TraitClauseList,
    ) -> Result<TraitClauseList, Self::Error> {
        let list = clauses.r(self.session());
        let mut out = Vec::with_capacity(list.len());

        for &ty in list {
            out.push(self.visit_clause(ty)?);
        }

        Ok(self.tcx().intern_trait_clause_list(&out))
    }

    fn visit_clause(&mut self, clause: TraitClause) -> Result<TraitClause, Self::Error> {
        self.walk_clause(clause)
    }

    fn walk_clause(&mut self, clause: TraitClause) -> Result<TraitClause, Self::Error> {
        match clause {
            TraitClause::Outlives(re) => Ok(TraitClause::Outlives(self.visit_re(re)?)),
            TraitClause::Trait(spec) => Ok(TraitClause::Trait(self.visit_trait_spec(spec)?)),
        }
    }

    fn visit_param_list(&mut self, params: TraitParamList) -> Result<TraitParamList, Self::Error> {
        self.walk_param_list(params)
    }

    fn walk_param_list(&mut self, params: TraitParamList) -> Result<TraitParamList, Self::Error> {
        let list = params.r(self.session());
        let mut out = Vec::with_capacity(list.len());

        for &ty in list {
            out.push(self.visit_param(ty)?);
        }

        Ok(self.tcx().intern_trait_param_list(&out))
    }

    fn visit_param(&mut self, param: TraitParam) -> Result<TraitParam, Self::Error> {
        self.walk_param(param)
    }

    fn walk_param(&mut self, param: TraitParam) -> Result<TraitParam, Self::Error> {
        match param {
            TraitParam::Equals(ty_or_re) => Ok(TraitParam::Equals(self.walk_ty_or_re(ty_or_re)?)),
            TraitParam::Unspecified(clauses) => {
                Ok(TraitParam::Unspecified(self.visit_clause_list(clauses)?))
            }
        }
    }

    // === Instances === //

    fn visit_trait_spec(&mut self, spec: TraitSpec) -> Result<TraitSpec, Self::Error> {
        self.walk_trait_spec(spec)
    }

    fn walk_trait_spec(&mut self, spec: TraitSpec) -> Result<TraitSpec, Self::Error> {
        Ok(TraitSpec {
            def: spec.def,
            params: self.visit_param_list(spec.params)?,
        })
    }

    fn visit_trait_instance(
        &mut self,
        instance: TraitInstance,
    ) -> Result<TraitInstance, Self::Error> {
        self.walk_trait_instance(instance)
    }

    fn walk_trait_instance(
        &mut self,
        instance: TraitInstance,
    ) -> Result<TraitInstance, Self::Error> {
        Ok(TraitInstance {
            def: instance.def,
            params: self.walk_ty_or_re_list(instance.params)?,
        })
    }

    fn visit_adt_instance(&mut self, instance: AdtInstance) -> Result<AdtInstance, Self::Error> {
        self.walk_adt_instance(instance)
    }

    fn walk_adt_instance(&mut self, instance: AdtInstance) -> Result<AdtInstance, Self::Error> {
        Ok(AdtInstance {
            def: instance.def,
            params: self.walk_ty_or_re_list(instance.params)?,
        })
    }

    // === Types === //

    fn walk_ty_or_re(&mut self, ty_or_re: TyOrRe) -> Result<TyOrRe, Self::Error> {
        match ty_or_re {
            TyOrRe::Re(re) => Ok(TyOrRe::Re(self.visit_re(re)?)),
            TyOrRe::Ty(ty) => Ok(TyOrRe::Ty(self.visit_ty(ty)?)),
        }
    }

    fn walk_ty_or_re_list(&mut self, list: TyOrReList) -> Result<TyOrReList, Self::Error> {
        let list = list.r(self.session());
        let mut out = Vec::with_capacity(list.len());

        for &ty in list {
            out.push(self.walk_ty_or_re(ty)?);
        }

        Ok(self.tcx().intern_ty_or_re_list(&out))
    }

    fn walk_ty_list(&mut self, list: TyList) -> Result<TyList, Self::Error> {
        let list = list.r(self.session());
        let mut out = Vec::with_capacity(list.len());

        for &ty in list {
            out.push(self.walk_ty(ty)?);
        }

        Ok(self.tcx().intern_ty_list(&out))
    }

    fn visit_re(&mut self, re: Re) -> Result<Re, Self::Error> {
        self.walk_re(re)
    }

    fn walk_re(&mut self, re: Re) -> Result<Re, Self::Error> {
        match re {
            Re::Gc | Re::InferVar(_) | Re::ExplicitInfer | Re::Erased => Ok(re),
            Re::Universal(generic) => self.visit_re_generic_use(generic),
        }
    }

    fn visit_ty(&mut self, ty: Ty) -> Result<Ty, Self::Error> {
        self.walk_ty(ty)
    }

    fn walk_ty(&mut self, ty: Ty) -> Result<Ty, Self::Error> {
        let tcx = self.tcx();

        match *ty.r(&tcx.session) {
            TyKind::Simple(..)
            | TyKind::FnDef(..)
            | TyKind::ExplicitInfer
            | TyKind::InferVar(..)
            | TyKind::Error(..) => Ok(ty),
            TyKind::This => self.visit_self_ty_use(),
            TyKind::Reference(re, pointee) => Ok(tcx.intern_ty(TyKind::Reference(
                self.visit_re(re)?,
                self.visit_ty(pointee)?,
            ))),
            TyKind::Adt(instance) => {
                Ok(tcx.intern_ty(TyKind::Adt(self.visit_adt_instance(instance)?)))
            }
            TyKind::Trait(clause_list) => {
                Ok(tcx.intern_ty(TyKind::Trait(self.visit_clause_list(clause_list)?)))
            }
            TyKind::Tuple(tys) => Ok(tcx.intern_ty(TyKind::Tuple(self.walk_ty_list(tys)?))),
            TyKind::Universal(generic) => self.visit_ty_generic_use(generic),
        }
    }

    fn visit_self_ty_use(&mut self) -> Result<Ty, Self::Error> {
        self.walk_self_ty_use()
    }

    fn walk_self_ty_use(&mut self) -> Result<Ty, Self::Error> {
        Ok(self.tcx().intern_ty(TyKind::This))
    }

    fn visit_re_generic_use(&mut self, generic: Obj<RegionGeneric>) -> Result<Re, Self::Error> {
        self.walk_re_generic_use(generic)
    }

    fn walk_re_generic_use(&mut self, generic: Obj<RegionGeneric>) -> Result<Re, Self::Error> {
        Ok(Re::Universal(generic))
    }

    fn visit_ty_generic_use(&mut self, generic: Obj<TypeGeneric>) -> Result<Ty, Self::Error> {
        self.walk_ty_generic_use(generic)
    }

    fn walk_ty_generic_use(&mut self, generic: Obj<TypeGeneric>) -> Result<Ty, Self::Error> {
        Ok(self.tcx().intern_ty(TyKind::Universal(generic)))
    }
}
