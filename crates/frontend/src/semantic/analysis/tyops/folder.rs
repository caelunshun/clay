use crate::{
    base::{
        Session,
        analysis::Spanned,
        arena::{HasInterner, HasListInterner, Intern},
    },
    semantic::{
        analysis::TyCtxt,
        syntax::{
            AdtInstance, FnInstance, HrtbBinder, HrtbBinderKind, HrtbDebruijnDef,
            HrtbDebruijnDefList, Re, SpannedAdtInstance, SpannedAdtInstanceView, SpannedFnInstance,
            SpannedFnInstanceView, SpannedHrtbBinder, SpannedHrtbBinderKind,
            SpannedHrtbBinderKindView, SpannedHrtbBinderView, SpannedHrtbDebruijnDef,
            SpannedHrtbDebruijnDefList, SpannedHrtbDebruijnDefView, SpannedRe, SpannedTraitClause,
            SpannedTraitClauseList, SpannedTraitClauseView, SpannedTraitInstance,
            SpannedTraitInstanceView, SpannedTraitParam, SpannedTraitParamList,
            SpannedTraitParamView, SpannedTraitSpec, SpannedTraitSpecView, SpannedTy,
            SpannedTyList, SpannedTyOrRe, SpannedTyOrReList, SpannedTyOrReView,
            SpannedTyProjection, SpannedTyProjectionView, SpannedTyView, TraitClause,
            TraitClauseList, TraitInstance, TraitParam, TraitParamList, TraitSpec, Ty, TyKind,
            TyList, TyOrRe, TyOrReList, TyProjection,
        },
    },
};
use std::{convert::Infallible, hash};

// === Helpers === //

fn super_interned_list<'tcx, T, V>(
    folder: &mut T,
    values: Spanned<Intern<[V]>>,
) -> Result<Intern<[V]>, T::Error>
where
    T: ?Sized + TyFolder<'tcx>,
    V: Clone + hash::Hash + Eq + TyFoldable,
    TyCtxt: HasListInterner<V>,
{
    let tcx = folder.tcx();
    let s = folder.session();

    let mut out = Vec::with_capacity(values.len(s));

    for value in values.iter(tcx) {
        out.push(folder.fold_spanned_fallible(value)?);
    }

    Ok(tcx.intern_list(&out))
}

// === Core traits === //

pub trait TyFoldable: Sized {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>;

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>;
}

pub trait TyFolderPreservesSpans<'tcx>: TyFolder<'tcx> {}

pub trait TyFolder<'tcx> {
    type Error;

    fn tcx(&self) -> &'tcx TyCtxt;

    fn session(&self) -> &'tcx Session {
        &self.tcx().session
    }

    // === Clauses === //

    fn fold_clause_list(
        &mut self,
        clauses: SpannedTraitClauseList,
    ) -> Result<TraitClauseList, Self::Error> {
        self.super_spanned_fallible(clauses)
    }

    fn fold_clause(&mut self, clause: SpannedTraitClause) -> Result<TraitClause, Self::Error> {
        self.super_spanned_fallible(clause)
    }

    fn fold_param_list(
        &mut self,
        params: SpannedTraitParamList,
    ) -> Result<TraitParamList, Self::Error> {
        self.super_spanned_fallible(params)
    }

    fn fold_param(&mut self, param: SpannedTraitParam) -> Result<TraitParam, Self::Error> {
        self.super_spanned_fallible(param)
    }

    // === Instances === //

    fn fold_trait_spec(&mut self, spec: SpannedTraitSpec) -> Result<TraitSpec, Self::Error> {
        self.super_spanned_fallible(spec)
    }

    fn fold_trait_instance(
        &mut self,
        instance: SpannedTraitInstance,
    ) -> Result<TraitInstance, Self::Error> {
        self.super_spanned_fallible(instance)
    }

    fn fold_adt_instance(
        &mut self,
        instance: SpannedAdtInstance,
    ) -> Result<AdtInstance, Self::Error> {
        self.super_spanned_fallible(instance)
    }

    fn fold_fn_instance(&mut self, instance: SpannedFnInstance) -> Result<FnInstance, Self::Error> {
        self.super_spanned_fallible(instance)
    }

    // === Types === //

    fn fold_ty_or_re(&mut self, ty_or_re: SpannedTyOrRe) -> Result<TyOrRe, Self::Error> {
        self.super_spanned_fallible(ty_or_re)
    }

    fn fold_ty_or_re_list(&mut self, list: SpannedTyOrReList) -> Result<TyOrReList, Self::Error> {
        self.super_spanned_fallible(list)
    }

    fn fold_ty_list(&mut self, list: SpannedTyList) -> Result<TyList, Self::Error> {
        self.super_spanned_fallible(list)
    }

    fn fold_re(&mut self, re: SpannedRe) -> Result<Re, Self::Error> {
        self.super_spanned_fallible(re)
    }

    fn fold_ty(&mut self, ty: SpannedTy) -> Result<Ty, Self::Error> {
        self.super_spanned_fallible(ty)
    }

    fn fold_ty_projection(
        &mut self,
        projection: SpannedTyProjection,
    ) -> Result<TyProjection, Self::Error> {
        self.super_spanned_fallible(projection)
    }

    // === Binders === //

    fn fold_hrtb_binder<T: Copy + TyFoldable>(
        &mut self,
        binder: SpannedHrtbBinder<T>,
    ) -> Result<HrtbBinder<T>, Self::Error> {
        self.super_spanned_fallible(binder)
    }

    fn fold_hrtb_binder_kind(
        &mut self,
        kind: SpannedHrtbBinderKind,
    ) -> Result<HrtbBinderKind, Self::Error> {
        self.super_spanned_fallible(kind)
    }

    fn fold_hrtb_debruijn_def_list(
        &mut self,
        defs: SpannedHrtbDebruijnDefList,
    ) -> Result<HrtbDebruijnDefList, Self::Error> {
        self.super_spanned_fallible(defs)
    }

    fn fold_hrtb_debruijn_def(
        &mut self,
        defs: SpannedHrtbDebruijnDef,
    ) -> Result<HrtbDebruijnDef, Self::Error> {
        self.super_spanned_fallible(defs)
    }
}

// === Extensions === //

pub trait TyFolderExt<'tcx>: TyFolder<'tcx> {
    fn fold_spanned_fallible<T: TyFoldable>(
        &mut self,
        value: Spanned<T>,
    ) -> Result<T, Self::Error> {
        T::fold_raw(value, self)
    }

    fn super_spanned_fallible<T: TyFoldable>(
        &mut self,
        value: Spanned<T>,
    ) -> Result<T, Self::Error> {
        T::super_raw(value, self)
    }

    fn fold_fallible<T: TyFoldable>(&mut self, value: T) -> Result<T, Self::Error> {
        self.fold_spanned_fallible(Spanned::new_unspanned(value))
    }

    fn super_fallible<T: TyFoldable>(&mut self, value: T) -> Result<T, Self::Error> {
        self.super_spanned_fallible(Spanned::new_unspanned(value))
    }

    fn fold_preserved_fallible<T: TyFoldable>(
        &mut self,
        value: Spanned<T>,
    ) -> Result<Spanned<T>, Self::Error>
    where
        Self: TyFolderPreservesSpans<'tcx>,
    {
        let old_span_info = value.span_info;

        T::fold_raw(value, self).map(|new_value| Spanned::new_raw(new_value, old_span_info))
    }

    fn super_preserved_fallible<T: TyFoldable>(
        &mut self,
        value: Spanned<T>,
    ) -> Result<Spanned<T>, Self::Error>
    where
        Self: TyFolderPreservesSpans<'tcx>,
    {
        let old_span_info = value.span_info;

        T::super_raw(value, self).map(|new_value| Spanned::new_raw(new_value, old_span_info))
    }
}

impl<'tcx, T: ?Sized + TyFolder<'tcx>> TyFolderExt<'tcx> for T {}

pub trait TyFolderInfallibleExt<'tcx>: TyFolder<'tcx, Error = Infallible> {
    fn fold_spanned<T: TyFoldable>(&mut self, value: Spanned<T>) -> T {
        let Ok(v) = self.fold_spanned_fallible(value);
        v
    }

    fn super_spanned<T: TyFoldable>(&mut self, value: Spanned<T>) -> T {
        let Ok(v) = self.super_spanned_fallible(value);
        v
    }

    fn fold<T: TyFoldable>(&mut self, value: T) -> T {
        let Ok(v) = self.fold_fallible(value);
        v
    }

    fn super_<T: TyFoldable>(&mut self, value: T) -> T {
        let Ok(v) = self.super_fallible(value);
        v
    }

    fn fold_preserved<T: TyFoldable>(&mut self, value: Spanned<T>) -> Spanned<T>
    where
        Self: TyFolderPreservesSpans<'tcx>,
    {
        let Ok(v) = self.fold_preserved_fallible(value);
        v
    }

    fn super_preserved<T: TyFoldable>(&mut self, value: Spanned<T>) -> Spanned<T>
    where
        Self: TyFolderPreservesSpans<'tcx>,
    {
        let Ok(v) = self.super_preserved_fallible(value);
        v
    }
}

impl<'tcx, T: ?Sized + TyFolder<'tcx, Error = Infallible>> TyFolderInfallibleExt<'tcx> for T {}

// === Clauses === //

impl TyFoldable for TraitClauseList {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_clause_list(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        super_interned_list(folder, me)
    }
}

impl TyFoldable for TraitClause {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_clause(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        Ok(match me.view(folder.tcx()) {
            SpannedTraitClauseView::Outlives(dir, ty_or_re) => {
                TraitClause::Outlives(dir, folder.fold_spanned_fallible(ty_or_re)?)
            }
            SpannedTraitClauseView::Trait(spec) => {
                TraitClause::Trait(folder.fold_spanned_fallible(spec)?)
            }
        })
    }
}

impl TyFoldable for TraitParamList {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_param_list(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        super_interned_list(folder, me)
    }
}

impl TyFoldable for TraitParam {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_param(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        Ok(match me.view(folder.tcx()) {
            SpannedTraitParamView::Equals(ty_or_re) => {
                TraitParam::Equals(folder.fold_spanned_fallible(ty_or_re)?)
            }
            SpannedTraitParamView::Unspecified(clauses) => {
                TraitParam::Unspecified(folder.fold_spanned_fallible(clauses)?)
            }
        })
    }
}

// === Instances === //

impl TyFoldable for TraitSpec {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_trait_spec(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        let SpannedTraitSpecView { def, params } = me.view(folder.tcx());

        Ok(TraitSpec {
            def,
            params: folder.fold_spanned_fallible(params)?,
        })
    }
}

impl TyFoldable for TraitInstance {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_trait_instance(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        let SpannedTraitInstanceView { def, params } = me.view(folder.tcx());

        Ok(TraitInstance {
            def,
            params: folder.fold_spanned_fallible(params)?,
        })
    }
}

impl TyFoldable for AdtInstance {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_adt_instance(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        let SpannedAdtInstanceView { def, params } = me.view(folder.tcx());

        Ok(AdtInstance {
            def,
            params: folder.fold_spanned_fallible(params)?,
        })
    }
}

impl TyFoldable for FnInstance {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_fn_instance(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        let SpannedFnInstanceView { def, impl_ty, args } = me.view(folder.tcx());

        Ok(FnInstance {
            def,
            impl_ty: match impl_ty {
                Some(v) => Some(folder.fold_spanned_fallible(v)?),
                None => None,
            },
            args: match args {
                Some(v) => Some(folder.fold_spanned_fallible(v)?),
                None => None,
            },
        })
    }
}

// === Types === //

impl TyFoldable for TyOrRe {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_ty_or_re(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        Ok(match me.view(folder.tcx()) {
            SpannedTyOrReView::Re(re) => TyOrRe::Re(folder.fold_spanned_fallible(re)?),
            SpannedTyOrReView::Ty(ty) => TyOrRe::Ty(folder.fold_spanned_fallible(ty)?),
        })
    }
}

impl TyFoldable for TyOrReList {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_ty_or_re_list(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        super_interned_list(folder, me)
    }
}

impl TyFoldable for TyList {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_ty_list(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        super_interned_list(folder, me)
    }
}

impl TyFoldable for Re {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_re(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
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
                // (dead end)
                _ = folder;
                Ok(me.value)
            }
        }
    }
}

impl TyFoldable for Ty {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_ty(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        let tcx = folder.tcx();
        let s = folder.session();

        let kind = match me.view(tcx) {
            SpannedTyView::Simple(_)
            | SpannedTyView::SigInfer
            | SpannedTyView::Error(_)
            | SpannedTyView::SigThis
            | SpannedTyView::SigGeneric(_)
            | SpannedTyView::HrtbVar(_)
            | SpannedTyView::InferVar(_)
            | SpannedTyView::UniversalVar(_) => {
                // (dead end)
                *me.value.r(s)
            }
            SpannedTyView::SigProject(project) => {
                TyKind::SigProject(folder.fold_spanned_fallible(project)?)
            }
            SpannedTyView::Reference(re, muta, pointee) => TyKind::Reference(
                folder.fold_spanned_fallible(re)?,
                muta,
                folder.fold_spanned_fallible(pointee)?,
            ),
            SpannedTyView::FnDef(def) => TyKind::FnDef(folder.fold_spanned_fallible(def)?),
            SpannedTyView::Adt(instance) => TyKind::Adt(folder.fold_spanned_fallible(instance)?),
            SpannedTyView::Trait(re, muta, clause_list) => TyKind::Trait(
                folder.fold_spanned_fallible(re)?,
                muta,
                folder.fold_spanned_fallible(clause_list)?,
            ),
            SpannedTyView::Tuple(tys) => TyKind::Tuple(folder.fold_spanned_fallible(tys)?),
        };

        Ok(tcx.intern(kind))
    }
}

impl TyFoldable for TyProjection {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_ty_projection(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        let SpannedTyProjectionView {
            target,
            spec,
            assoc_span: _,
            assoc,
        } = me.view(folder.tcx());

        Ok(TyProjection {
            target: folder.fold_spanned_fallible(target)?,
            spec: folder.fold_spanned_fallible(spec)?,
            assoc,
        })
    }
}

// === Binders === //

impl<T: TyFoldable + Copy> TyFoldable for HrtbBinder<T> {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_hrtb_binder(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        let SpannedHrtbBinderView { kind, inner } = me.view(folder.tcx());

        Ok(HrtbBinder {
            kind: folder.fold_spanned_fallible(kind)?,
            inner: folder.fold_spanned_fallible(inner)?,
        })
    }
}

impl TyFoldable for HrtbBinderKind {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_hrtb_binder_kind(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        Ok(match me.view(folder.tcx()) {
            SpannedHrtbBinderKindView::Signature(binder) => HrtbBinderKind::Signature(binder),
            SpannedHrtbBinderKindView::Imported(clauses) => {
                HrtbBinderKind::Imported(folder.fold_spanned_fallible(clauses)?)
            }
        })
    }
}

impl TyFoldable for HrtbDebruijnDefList {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_hrtb_debruijn_def_list(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        super_interned_list(folder, me)
    }
}

impl TyFoldable for HrtbDebruijnDef {
    fn fold_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_hrtb_debruijn_def(me)
    }

    fn super_raw<'tcx, F>(me: Spanned<Self>, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        let SpannedHrtbDebruijnDefView {
            spawned_from,
            kind,
            clauses,
        } = me.view(folder.tcx());

        Ok(HrtbDebruijnDef {
            spawned_from,
            kind,
            clauses: folder.fold_spanned_fallible(clauses)?,
        })
    }
}
