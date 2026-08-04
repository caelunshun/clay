use crate::{
    base::{
        Session,
        arena::{HasInterner, HasListInterner, Intern},
    },
    semantic::syntax::{
        AdtInstance, FnInstance, FnInstanceInner, FnOwner, FnOwnerAdtCtor, FnOwnerInherent,
        FnOwnerTrait, HrtbBinder, HrtbDebruijnDef, HrtbDebruijnDefList, Re, TraitClause,
        TraitClauseList, TraitInstance, TraitParam, TraitParamList, TraitSpec, Ty, TyCtxt, TyKind,
        TyList, TyOrRe, TyOrReList,
    },
};
use std::{convert::Infallible, hash};

// === Helpers === //

fn super_interned_list<'tcx, T, V>(
    folder: &mut T,
    values: Intern<[V]>,
) -> Result<Intern<[V]>, T::Error>
where
    T: ?Sized + TyFolder<'tcx>,
    V: Copy + hash::Hash + Eq + TyFoldable,
    TyCtxt: HasListInterner<V>,
{
    let tcx = folder.tcx();
    let s = folder.session();

    let mut out = Vec::with_capacity(values.r(s).len());

    for &value in values.r(s) {
        out.push(folder.fold_fallible(value)?);
    }

    Ok(tcx.intern_list(&out))
}

// === Core traits === //

pub trait TyFoldable: Sized {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>;

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>;
}

pub trait TyFolder<'tcx> {
    type Error;

    fn tcx(&self) -> &'tcx TyCtxt;

    fn session(&self) -> &'tcx Session {
        &self.tcx().session
    }

    // === Clauses === //

    fn fold_clause_list(
        &mut self,
        clauses: TraitClauseList,
    ) -> Result<TraitClauseList, Self::Error> {
        self.super_fallible(clauses)
    }

    fn fold_clause(&mut self, clause: TraitClause) -> Result<TraitClause, Self::Error> {
        self.super_fallible(clause)
    }

    fn fold_param_list(&mut self, params: TraitParamList) -> Result<TraitParamList, Self::Error> {
        self.super_fallible(params)
    }

    fn fold_param(&mut self, param: TraitParam) -> Result<TraitParam, Self::Error> {
        self.super_fallible(param)
    }

    // === Instances === //

    fn fold_trait_spec(&mut self, spec: TraitSpec) -> Result<TraitSpec, Self::Error> {
        self.super_fallible(spec)
    }

    fn fold_trait_instance(
        &mut self,
        instance: TraitInstance,
    ) -> Result<TraitInstance, Self::Error> {
        self.super_fallible(instance)
    }

    fn fold_adt_instance(&mut self, instance: AdtInstance) -> Result<AdtInstance, Self::Error> {
        self.super_fallible(instance)
    }

    fn fold_fn_instance(&mut self, instance: FnInstance) -> Result<FnInstance, Self::Error> {
        self.super_fallible(instance)
    }

    fn fold_fn_owner(&mut self, owner: FnOwner) -> Result<FnOwner, Self::Error> {
        self.super_fallible(owner)
    }

    // === Types === //

    fn fold_ty_or_re(&mut self, ty_or_re: TyOrRe) -> Result<TyOrRe, Self::Error> {
        self.super_fallible(ty_or_re)
    }

    fn fold_ty_or_re_list(&mut self, list: TyOrReList) -> Result<TyOrReList, Self::Error> {
        self.super_fallible(list)
    }

    fn fold_ty_list(&mut self, list: TyList) -> Result<TyList, Self::Error> {
        self.super_fallible(list)
    }

    fn fold_re(&mut self, re: Re) -> Result<Re, Self::Error> {
        self.super_fallible(re)
    }

    fn fold_ty(&mut self, ty: Ty) -> Result<Ty, Self::Error> {
        self.super_fallible(ty)
    }

    // === Binders === //

    fn fold_hrtb_binder(&mut self, binder: HrtbBinder) -> Result<HrtbBinder, Self::Error> {
        self.super_fallible(binder)
    }

    fn fold_hrtb_debruijn_def_list(
        &mut self,
        defs: HrtbDebruijnDefList,
    ) -> Result<HrtbDebruijnDefList, Self::Error> {
        self.super_fallible(defs)
    }

    fn fold_hrtb_debruijn_def(
        &mut self,
        defs: HrtbDebruijnDef,
    ) -> Result<HrtbDebruijnDef, Self::Error> {
        self.super_fallible(defs)
    }
}

// === Extensions === //

pub trait TyFolderExt<'tcx>: TyFolder<'tcx> {
    fn fold_fallible<T: TyFoldable>(&mut self, value: T) -> Result<T, Self::Error> {
        T::fold_raw(value, self)
    }

    fn super_fallible<T: TyFoldable>(&mut self, value: T) -> Result<T, Self::Error> {
        T::super_raw(value, self)
    }
}

impl<'tcx, T: ?Sized + TyFolder<'tcx>> TyFolderExt<'tcx> for T {}

pub trait TyFolderInfallibleExt<'tcx>: TyFolder<'tcx, Error = Infallible> {
    fn fold<T: TyFoldable>(&mut self, value: T) -> T {
        let Ok(v) = self.fold_fallible(value);
        v
    }

    fn super_<T: TyFoldable>(&mut self, value: T) -> T {
        let Ok(v) = self.super_fallible(value);
        v
    }
}

impl<'tcx, T: ?Sized + TyFolder<'tcx, Error = Infallible>> TyFolderInfallibleExt<'tcx> for T {}

// === Clauses === //

impl TyFoldable for TraitClauseList {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_clause_list(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        super_interned_list(folder, me)
    }
}

impl TyFoldable for TraitClause {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_clause(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        Ok(match me {
            TraitClause::Outlives(dir, ty_or_re) => {
                TraitClause::Outlives(dir, folder.fold_fallible(ty_or_re)?)
            }
            TraitClause::Trait(spec) => TraitClause::Trait(folder.fold_fallible(spec)?),
        })
    }
}

impl TyFoldable for TraitParamList {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_param_list(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        super_interned_list(folder, me)
    }
}

impl TyFoldable for TraitParam {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_param(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        Ok(match me {
            TraitParam::Equals(ty_or_re) => TraitParam::Equals(folder.fold_fallible(ty_or_re)?),
            TraitParam::Unspecified(clauses) => {
                TraitParam::Unspecified(folder.fold_fallible(clauses)?)
            }
        })
    }
}

// === Instances === //

impl TyFoldable for TraitSpec {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_trait_spec(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        let TraitSpec { def, params } = me;

        Ok(TraitSpec {
            def,
            params: folder.fold_fallible(params)?,
        })
    }
}

impl TyFoldable for TraitInstance {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_trait_instance(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        let TraitInstance { def, params } = me;

        Ok(TraitInstance {
            def,
            params: folder.fold_fallible(params)?,
        })
    }
}

impl TyFoldable for AdtInstance {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_adt_instance(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        let AdtInstance { def, params } = me;

        Ok(AdtInstance {
            def,
            params: folder.fold_fallible(params)?,
        })
    }
}

impl TyFoldable for FnInstance {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_fn_instance(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        let tcx = folder.tcx();
        let s = folder.session();

        let FnInstanceInner { owner, early_args } = *me.r(s);

        Ok(tcx.intern(FnInstanceInner {
            owner: folder.fold_fallible(owner)?,
            early_args: match early_args {
                Some(early_args) => Some(folder.fold_fallible(early_args)?),
                None => None,
            },
        }))
    }
}

impl TyFoldable for FnOwner {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_fn_owner(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        match me {
            FnOwner::Item(def) => Ok(FnOwner::Item(def)),
            FnOwner::Trait(FnOwnerTrait {
                instance,
                self_ty,
                method_idx,
            }) => Ok(FnOwner::Trait(FnOwnerTrait {
                instance: folder.fold_fallible(instance)?,
                self_ty: folder.fold_fallible(self_ty)?,
                method_idx,
            })),
            FnOwner::Inherent(FnOwnerInherent {
                self_ty,
                block,
                method_idx,
            }) => Ok(FnOwner::Inherent(FnOwnerInherent {
                self_ty: folder.fold_fallible(self_ty)?,
                block,
                method_idx,
            })),
            FnOwner::AdtCtor(FnOwnerAdtCtor { ctor }) => {
                Ok(FnOwner::AdtCtor(FnOwnerAdtCtor { ctor }))
            }
        }
    }
}

// === Types === //

impl TyFoldable for TyOrRe {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_ty_or_re(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        Ok(match me {
            TyOrRe::Re(re) => TyOrRe::Re(folder.fold_fallible(re)?),
            TyOrRe::Ty(ty) => TyOrRe::Ty(folder.fold_fallible(ty)?),
        })
    }
}

impl TyFoldable for TyOrReList {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_ty_or_re_list(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        super_interned_list(folder, me)
    }
}

impl TyFoldable for TyList {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_ty_list(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        super_interned_list(folder, me)
    }
}

impl TyFoldable for Re {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_re(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        match me {
            Re::Gc
            | Re::Erased
            | Re::Error(_)
            | Re::HrtbVar(_)
            | Re::InferVar(_)
            | Re::UniversalVar(_) => {
                // (dead end)
                _ = folder;
                Ok(me)
            }
        }
    }
}

impl TyFoldable for Ty {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_ty(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        let tcx = folder.tcx();
        let s = folder.session();

        let kind = match *me.r(s) {
            TyKind::Simple(_)
            | TyKind::Error(_)
            | TyKind::HrtbVar(_)
            | TyKind::InferVar(_)
            | TyKind::UniversalVar(_) => {
                // (dead end)
                *me.r(s)
            }
            TyKind::Reference(re, muta, pointee) => TyKind::Reference(
                folder.fold_fallible(re)?,
                muta,
                folder.fold_fallible(pointee)?,
            ),
            TyKind::FnDef(def) => TyKind::FnDef(folder.fold_fallible(def)?),
            TyKind::Adt(instance) => TyKind::Adt(folder.fold_fallible(instance)?),
            TyKind::Trait(re, muta, clause_list) => TyKind::Trait(
                folder.fold_fallible(re)?,
                muta,
                folder.fold_fallible(clause_list)?,
            ),
            TyKind::Tuple(tys) => TyKind::Tuple(folder.fold_fallible(tys)?),
        };

        Ok(tcx.intern(kind))
    }
}

// === Binders === //

impl TyFoldable for HrtbBinder {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_hrtb_binder(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        let HrtbBinder { defs, inner } = me;

        Ok(HrtbBinder {
            defs: folder.fold_fallible(defs)?,
            inner: folder.fold_fallible(inner)?,
        })
    }
}

impl TyFoldable for HrtbDebruijnDefList {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_hrtb_debruijn_def_list(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        super_interned_list(folder, me)
    }
}

impl TyFoldable for HrtbDebruijnDef {
    fn fold_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        folder.fold_hrtb_debruijn_def(me)
    }

    fn super_raw<'tcx, F>(me: Self, folder: &mut F) -> Result<Self, F::Error>
    where
        F: ?Sized + TyFolder<'tcx>,
    {
        let HrtbDebruijnDef {
            span,
            name,
            kind,
            clauses,
        } = me;

        Ok(HrtbDebruijnDef {
            span,
            name,
            kind,
            clauses: folder.fold_fallible(clauses)?,
        })
    }
}
