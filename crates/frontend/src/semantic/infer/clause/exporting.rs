use crate::{
    base::{
        Diag,
        arena::{HasInterner as _, Obj},
        syntax::Span,
    },
    semantic::{
        infer::ClauseCx,
        syntax::{
            AdtInstance, FnInstance, FnInstanceInner, FnOwner, HrtbBinder, HrtbDebruijnDef,
            HrtbDebruijnDefList, HrtbProjection, Re, RelationMode, SigAdtInstance, SigFnInstance,
            SigFnOwner, SigGenericList, SigHrtbBinder, SigHrtbDebruijnDef, SigHrtbDebruijnDefList,
            SigProjectType, SigRe, SigReKind, SigTraitClause, SigTraitClauseKind,
            SigTraitClauseList, SigTraitParam, SigTraitParamKind, SigTraitParamList, SigTraitSpec,
            SigTy, SigTyInner, SigTyKind, SigTyList, SigTyOrRe, SigTyOrReList, TraitClause,
            TraitClauseList, TraitParam, TraitParamList, TraitSpec, Ty, TyKind, TyList, TyOrRe,
            TyOrReList, UniversalReVarSourceInfo, UniversalTy, UniversalTyProjInner,
            UniversalTyRootSourceInfo,
        },
    },
};

impl<'tcx> ClauseCx<'tcx> {
    pub fn exporter(&mut self, span: Span) -> SigExporter<'_, 'tcx> {
        SigExporter { ccx: self, span }
    }

    pub fn export<T: SigExportable<'tcx>>(&mut self, span: Span, val: T) -> T::Output {
        self.exporter(span).export(val)
    }
}

pub trait SigExportable<'tcx>: Sized {
    type Output;

    fn export(me: Self, exporter: &mut SigExporter<'_, 'tcx>) -> Self::Output;
}

macro_rules! impl_sig_exportable {
    ( $( $method:ident: $src:ty => $dest:ty; )* ) => {$(
        impl<'tcx> SigExportable<'tcx> for $src {
            type Output = $dest;

            fn export(
                me: Self,
                exporter: &mut SigExporter<'_, 'tcx>,
            ) -> Self::Output {
                exporter.$method(me)
            }
        }
    )*};
}

impl_sig_exportable! {
    export_ty_list: TyList => SigTyList;
    export_ty_or_re_list: TyOrReList => SigTyOrReList;
    export_ty_or_re: TyOrRe => SigTyOrRe;
    export_re: Re => SigRe;
    export_ty: Ty => SigTy;
    export_adt: AdtInstance => SigAdtInstance;
    export_fn_instance: FnInstance => SigFnInstance;
    export_fn_owner: FnOwner => SigFnOwner;
    export_hrtb_projection: HrtbProjection => SigProjectType;
    export_trait_clause_list: TraitClauseList => SigTraitClauseList;
    export_trait_clause: TraitClause => SigTraitClause;
    export_hrtb_binder: HrtbBinder => SigHrtbBinder;
    export_hrtb_debruijn_def_list: HrtbDebruijnDefList => SigHrtbDebruijnDefList;
    export_hrtb_debruijn_def: HrtbDebruijnDef => SigHrtbDebruijnDef;
    export_trait_spec: TraitSpec => SigTraitSpec;
    export_trait_param_list: TraitParamList => SigTraitParamList;
    export_trait_param: TraitParam => SigTraitParam;
    export_universal_ty: UniversalTy => SigTy;
}

pub struct SigExporter<'a, 'tcx> {
    pub ccx: &'a mut ClauseCx<'tcx>,
    pub span: Span,
}

impl<'a, 'tcx> SigExporter<'a, 'tcx> {
    pub fn export<T: SigExportable<'tcx>>(&mut self, val: T) -> T::Output {
        T::export(val, self)
    }

    pub fn export_ty_list(&mut self, list: TyList) -> SigTyList {
        let s = self.ccx.session();

        Obj::new_iter(list.r(s).iter().map(|&ty| self.export_ty(ty)), s)
    }

    pub fn export_ty_or_re_list(&mut self, list: TyOrReList) -> SigTyOrReList {
        let s = self.ccx.session();

        Obj::new_iter(list.r(s).iter().map(|&term| self.export_ty_or_re(term)), s)
    }

    pub fn export_ty_or_re(&mut self, term: TyOrRe) -> SigTyOrRe {
        match term {
            TyOrRe::Re(re) => SigTyOrRe::Re(self.export_re(re)),
            TyOrRe::Ty(ty) => SigTyOrRe::Ty(self.export_ty(ty)),
        }
    }

    pub fn export_re(&mut self, re: Re) -> SigRe {
        let kind = match re {
            Re::Gc => SigReKind::Gc,
            Re::HrtbVar(debruijn) => SigReKind::HrtbVar(debruijn),
            Re::InferVar(_) => SigReKind::Infer,
            Re::UniversalVar(var) => match self.ccx.lookup_universal_re_src_info(var) {
                UniversalReVarSourceInfo::Root(generic) => SigReKind::Generic(generic),
                UniversalReVarSourceInfo::ElaboratedLub
                | UniversalReVarSourceInfo::InstantiatedHrtbVar
                | UniversalReVarSourceInfo::HrtbWf { .. }
                | UniversalReVarSourceInfo::MirLocal(_) => {
                    todo!()
                }
            },
            Re::Error(error) => SigReKind::Error(error),
        };

        SigRe {
            span: self.span,
            kind,
        }
    }

    pub fn export_ty(&mut self, ty: Ty) -> SigTy {
        let s = self.ccx.session();
        let tcx = self.ccx.tcx();

        let ty = self.ccx.peel_ty_infer_var_without_poll(ty);

        let kind = match *ty.r(s) {
            TyKind::Simple(kind) => SigTyKind::Simple(kind),
            TyKind::Reference(re, muta, pointee) => {
                SigTyKind::Reference(self.export_re(re), muta, self.export_ty(pointee))
            }
            TyKind::Adt(adt) => SigTyKind::Adt(self.export_adt(adt)),
            TyKind::Trait(re, muta, clauses) => SigTyKind::Trait(
                self.export_re(re),
                muta,
                self.export_trait_clause_list(clauses),
            ),
            TyKind::Tuple(types) => SigTyKind::Tuple(self.export_ty_list(types)),
            TyKind::FnDef(def) => SigTyKind::FnDef(self.export_fn_instance(def)),
            TyKind::HrtbVar(idx) => SigTyKind::HrtbVar(idx),
            TyKind::HrtbProjection(proj) => SigTyKind::Project(self.export_hrtb_projection(proj)),
            TyKind::InferVar(var) => {
                let err = Diag::span_err(self.span, "type hints required for this type").emit();

                self.ccx
                    .unify_ty_and_ty(
                        tcx.intern(TyKind::InferVar(var)),
                        tcx.intern(TyKind::Error(err)),
                        RelationMode::Equate,
                    )
                    .unwrap()
                    .report_never();

                SigTyKind::Error(err)
            }
            TyKind::Universal(universal) => return self.export_universal_ty(universal),
            TyKind::Error(error) => SigTyKind::Error(error),
        };

        Obj::new(
            SigTyInner {
                span: self.span,
                kind,
            },
            s,
        )
    }

    pub fn export_adt(&mut self, adt: AdtInstance) -> SigAdtInstance {
        let AdtInstance { def, params } = adt;

        SigAdtInstance {
            def,
            params: SigGenericList {
                segment_span: self.span,
                elems: self.export_ty_or_re_list(params),
            },
        }
    }

    pub fn export_fn_instance(&mut self, instance: FnInstance) -> SigFnInstance {
        let s = self.ccx.session();

        let FnInstanceInner { owner, early_args } = *instance.r(s);

        let owner = self.export_fn_owner(owner);
        let early_args = early_args.map(|early_args| SigGenericList {
            segment_span: self.span,
            elems: self.export_ty_or_re_list(early_args),
        });

        SigFnInstance {
            span: self.span,
            owner,
            early_args,
        }
    }

    pub fn export_fn_owner(&mut self, owner: FnOwner) -> SigFnOwner {
        match owner {
            FnOwner::Item(def) => SigFnOwner::Item(def),
            FnOwner::Trait {
                instance,
                self_ty,
                method_idx,
            } => SigFnOwner::Trait {
                instance: self.export_trait_spec(instance),
                self_ty: self.export_ty(self_ty),
                method_idx,
            },
            FnOwner::Inherent {
                self_ty,
                block,
                method_idx,
            } => SigFnOwner::Inherent {
                self_ty: self.export_ty(self_ty),
                block,
                method_idx,
            },
            FnOwner::AdtCtor(def) => SigFnOwner::AdtCtor(def),
        }
    }

    pub fn export_hrtb_projection(&mut self, proj: HrtbProjection) -> SigProjectType {
        let HrtbProjection {
            target,
            spec,
            assoc_idx,
        } = proj;

        SigProjectType {
            target: self.export_ty(target),
            spec: self.export_trait_spec(spec),
            assoc_span: self.span,
            assoc_idx,
        }
    }

    pub fn export_trait_clause_list(&mut self, clauses: TraitClauseList) -> SigTraitClauseList {
        let s = self.ccx.session();

        let elems = Obj::new_iter(
            clauses
                .r(s)
                .iter()
                .map(|&clause| self.export_trait_clause(clause)),
            s,
        );

        SigTraitClauseList {
            span: self.span,
            elems,
        }
    }

    pub fn export_trait_clause(&mut self, clause: TraitClause) -> SigTraitClause {
        let kind = match clause {
            TraitClause::Outlives(dir, other) => {
                SigTraitClauseKind::Outlives(dir, self.export_ty_or_re(other))
            }
            TraitClause::Trait(binder) => {
                SigTraitClauseKind::Trait(self.export_hrtb_binder(binder))
            }
        };

        SigTraitClause {
            span: self.span,
            kind,
        }
    }

    pub fn export_hrtb_binder(&mut self, binder: HrtbBinder) -> SigHrtbBinder {
        let HrtbBinder { defs, inner } = binder;

        SigHrtbBinder {
            defs_span: self.span,
            defs: self.export_hrtb_debruijn_def_list(defs),
            inner: self.export_trait_spec(inner),
        }
    }

    pub fn export_hrtb_debruijn_def_list(
        &mut self,
        defs: HrtbDebruijnDefList,
    ) -> SigHrtbDebruijnDefList {
        let s = self.ccx.session();

        Obj::new_iter(
            defs.r(s)
                .iter()
                .map(|&def| self.export_hrtb_debruijn_def(def)),
            s,
        )
    }

    pub fn export_hrtb_debruijn_def(&mut self, def: HrtbDebruijnDef) -> SigHrtbDebruijnDef {
        let HrtbDebruijnDef {
            span: _,
            name,
            kind,
            clauses,
        } = def;

        SigHrtbDebruijnDef {
            span: self.span,
            name,
            kind,
            clauses: self.export_trait_clause_list(clauses),
        }
    }

    pub fn export_trait_spec(&mut self, spec: TraitSpec) -> SigTraitSpec {
        let TraitSpec { def, params } = spec;

        SigTraitSpec {
            span: self.span,
            def,
            params: self.export_trait_param_list(params),
        }
    }

    pub fn export_trait_param_list(&mut self, params: TraitParamList) -> SigTraitParamList {
        let s = self.ccx.session();

        Obj::new_iter(
            params
                .r(s)
                .iter()
                .map(|&param| self.export_trait_param(param)),
            s,
        )
    }

    pub fn export_trait_param(&mut self, param: TraitParam) -> SigTraitParam {
        let kind = match param {
            TraitParam::Equals(term) => SigTraitParamKind::Equals(self.export_ty_or_re(term)),
            TraitParam::Unspecified(clauses) => {
                SigTraitParamKind::Unspecified(self.export_trait_clause_list(clauses))
            }
        };

        SigTraitParam {
            span: self.span,
            kind,
        }
    }

    pub fn export_universal_ty(&mut self, universal: UniversalTy) -> SigTy {
        let s = self.ccx.session();

        let kind = match universal {
            UniversalTy::Root(root) => match self.ccx.lookup_universal_ty_root_src_info(root) {
                UniversalTyRootSourceInfo::Root(generic) => SigTyKind::Generic(generic),
                UniversalTyRootSourceInfo::InstantiatedHrtb(_)
                | UniversalTyRootSourceInfo::WfTraitSelf
                | UniversalTyRootSourceInfo::WfReflexive { .. }
                | UniversalTyRootSourceInfo::WfHrtbUniversal { .. } => unreachable!(),
            },
            UniversalTy::Projection(proj) => {
                let UniversalTyProjInner {
                    target,
                    as_spec,
                    assoc_idx,
                    cache_idx: _,
                } = *proj.r(s);

                SigTyKind::Project(SigProjectType {
                    target: self.export_universal_ty(target),
                    spec: self.export_trait_spec(as_spec),
                    assoc_span: self.span,
                    assoc_idx,
                })
            }
        };

        Obj::new(
            SigTyInner {
                span: self.span,
                kind,
            },
            s,
        )
    }
}
