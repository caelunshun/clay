use crate::{
    base::{Diag, arena::HasInterner as _, syntax::HasSpan as _},
    semantic::{
        analysis::{ClauseCx, ClauseCxPrinter, ClauseOrigin},
        syntax::{
            HrtbBinder, InferTyVarSourceInfo, Re, RelationMode, SpannedHrtbBinder, SpannedRe,
            SpannedTy, Ty, TyCtxt, TyFoldable, TyFolder, TyFolderInfallibleExt as _, TyKind,
            TyProjection, TyVisitable, UniversalTyVar, UniversalTyVarSourceInfo,
        },
    },
};
use std::convert::Infallible;

impl<'tcx> ClauseCx<'tcx> {
    pub fn exporter(&mut self) -> ClauseCxExporter<'_, 'tcx> {
        ClauseCxExporter { ccx: self }
    }
}

pub struct ClauseCxExporter<'a, 'tcx> {
    pub ccx: &'a mut ClauseCx<'tcx>,
}

impl<'tcx> TyFolder<'tcx> for ClauseCxExporter<'_, 'tcx> {
    type Error = Infallible;

    fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    fn fold_hrtb_binder<T: Copy + TyVisitable + TyFoldable>(
        &mut self,
        binder: SpannedHrtbBinder<T>,
    ) -> Result<HrtbBinder<T>, Self::Error> {
        // TODO: Fold whatever we need to.
        Ok(self.super_(binder.value))
    }

    fn fold_ty(&mut self, ty: SpannedTy) -> Result<Ty, Self::Error> {
        let s = self.session();
        let tcx = self.tcx();

        let TyKind::InferVar(var) = *ty.value.r(s) else {
            return Ok(self.super_(ty.value));
        };

        let Ok(resolved) = self.ccx.lookup_ty_infer_var_without_poll(var) else {
            let var_ty = tcx.intern(TyKind::InferVar(var));

            let error = match self.ccx.lookup_infer_ty_src_info(var) {
                InferTyVarSourceInfo::Local { name } => Diag::span_err(
                    name.span(),
                    format_args!("type annotations required for local `{name}`"),
                )
                .emit(),
                InferTyVarSourceInfo::HrtbLhsInstantiation { span }
                | InferTyVarSourceInfo::ProjectionResult { span, .. }
                | InferTyVarSourceInfo::Imported { span, .. }
                | InferTyVarSourceInfo::FunctionArgs { span }
                | InferTyVarSourceInfo::FunctionRetVal { span }
                | InferTyVarSourceInfo::MethodReceiver { span }
                | InferTyVarSourceInfo::OverloadedResult { span }
                | InferTyVarSourceInfo::Literal { span }
                | InferTyVarSourceInfo::ForLoopElem { span }
                | InferTyVarSourceInfo::IndexInput { span }
                | InferTyVarSourceInfo::IndexOutput { span }
                | InferTyVarSourceInfo::LoopDemand { span }
                | InferTyVarSourceInfo::HoleInfer { span }
                | InferTyVarSourceInfo::PatType { span }
                | InferTyVarSourceInfo::EmptyArrayElem { span } => Diag::span_err(
                    span,
                    format_args!("failed to infer a type of `{}`", {
                        let mut printer = ClauseCxPrinter::new(self.ccx);
                        printer.push_ty(var_ty);
                        printer.finish()
                    }),
                )
                .emit(),

                // TODO
                InferTyVarSourceInfo::UniversalElabHelper => {
                    Diag::anon_err("universal elab helper went uninferred, good luck!").emit()
                }
                InferTyVarSourceInfo::TraitAssocPlaceholderHelper => todo!(),
                InferTyVarSourceInfo::UnifyHelper => todo!(),
                InferTyVarSourceInfo::DerefHelper => todo!(),
                InferTyVarSourceInfo::MethodLookupHelper => todo!(),
            };

            let error_ty = tcx.intern(TyKind::Error(error));

            _ = self.ccx.ucx_mut().unify_ty_and_ty(
                &ClauseOrigin::delay_bug(),
                var_ty,
                error_ty,
                RelationMode::Equate,
            );

            self.ccx.poll_obligations();

            return Ok(error_ty);
        };

        match *resolved.r(s) {
            TyKind::SigThis
            | TyKind::SigInfer
            | TyKind::SigGeneric(_)
            | TyKind::SigProject(_)
            | TyKind::SigAlias(_, _)
            | TyKind::InferVar(_) => unreachable!(),

            TyKind::Simple(_)
            | TyKind::Reference(_, _, _)
            | TyKind::Adt(_)
            | TyKind::Trait(_, _, _)
            | TyKind::Tuple(_)
            | TyKind::FnDef(_)
            | TyKind::Error(_) => Ok(self.super_(resolved)),

            TyKind::UniversalVar(var) => Ok(self.fold_universal_var(var)),

            TyKind::HrtbVar(hrtb_debruijn) => todo!(),
        }
    }

    fn fold_re(&mut self, re: SpannedRe) -> Result<Re, Self::Error> {
        assert_eq!(re.value, Re::Erased);
        Ok(Re::SigInfer)
    }
}

impl ClauseCxExporter<'_, '_> {
    fn fold_universal_var(&mut self, var: UniversalTyVar) -> Ty {
        let tcx = self.tcx();

        match self.ccx.lookup_universal_ty_src_info(var) {
            // `Self` in trait method body.
            UniversalTyVarSourceInfo::TraitSelf => tcx.intern(TyKind::SigThis),

            // No universal leaks.
            UniversalTyVarSourceInfo::HrtbVar => unreachable!(),

            UniversalTyVarSourceInfo::Root(generic) => {
                // This must belong to us because we cannot leak other universals
                // into the root scope.
                tcx.intern(TyKind::SigGeneric(generic))
            }

            UniversalTyVarSourceInfo::Projection(var, spec, assoc) => {
                tcx.intern(TyKind::SigProject(TyProjection {
                    target: self.fold_universal_var(var),
                    spec: self.fold(spec),
                    assoc,
                }))
            }
        }
    }
}
