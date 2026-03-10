use crate::{
    base::{
        Diag,
        arena::{HasInterner, Obj},
    },
    semantic::{
        analysis::{
            BodyCtxt, ClauseCxPrinter, ClauseOrigin, FloatingInferVar, TyCtxt, TyFoldable,
            TyFolder, TyFolderInfallibleExt,
        },
        syntax::{Expr, InferTyVarSourceInfo, RelationMode, SpannedTy, Ty, TyKind},
    },
};
use std::convert::Infallible;

impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
    pub fn confirm(&mut self) {
        let tcx = self.tcx();

        // Assign fallbacks to integer literal inference holes.
        self.ccx_mut().poll_obligations();

        for idx in 0..self.int_infers.len() {
            let var = self.int_infers[idx];

            let Err(FloatingInferVar { perm_set, .. }) =
                self.ccx().lookup_ty_infer_var_without_poll(var)
            else {
                continue;
            };

            let var_ty = tcx.intern(TyKind::InferVar(var));

            let Some(fallback) = perm_set.to_infer_fallback(tcx) else {
                continue;
            };

            _ = self.ucx_mut().unify_ty_and_ty(
                &ClauseOrigin::never_printed(),
                var_ty,
                fallback,
                RelationMode::Equate,
            );

            self.ccx_mut().poll_obligations();
        }

        // Lower the function to its THIR representation.
        // TODO
    }

    fn confirm_expr_without_adjustments(&mut self, expr: Obj<Expr>) {
        todo!()
    }

    fn confirm_ty<T: TyFoldable>(&mut self, ty: T) -> T {
        struct ConfirmFolder<'a, 'b, 'tcx> {
            bcx: &'a mut BodyCtxt<'b, 'tcx>,
        }

        impl<'tcx> TyFolder<'tcx> for ConfirmFolder<'_, '_, 'tcx> {
            type Error = Infallible;

            fn tcx(&self) -> &'tcx TyCtxt {
                self.bcx.tcx()
            }

            fn fold_ty(&mut self, ty: SpannedTy) -> Result<Ty, Self::Error> {
                let s = self.session();
                let tcx = self.tcx();

                let TyKind::InferVar(var) = *ty.value.r(s) else {
                    return Ok(self.super_(ty.value));
                };

                if let Ok(resolved) = self.bcx.ccx().lookup_ty_infer_var_without_poll(var) {
                    return Ok(self.super_(resolved));
                }

                let var_ty = tcx.intern(TyKind::InferVar(var));

                let error = match self.bcx.ccx().lookup_infer_ty_src_info(var) {
                    InferTyVarSourceInfo::Local { name } => Diag::span_err(
                        name.span,
                        format_args!("type annotations required for local `{}`", name.text),
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
                    | InferTyVarSourceInfo::HoleInfer { span } => Diag::span_err(
                        span,
                        format_args!("failed to infer a type of `{}`", {
                            let mut printer = ClauseCxPrinter::new(self.bcx.ccx());
                            printer.push_ty(var_ty);
                            printer.finish()
                        }),
                    )
                    .emit(),

                    InferTyVarSourceInfo::UniversalElabHelper => todo!(),
                    InferTyVarSourceInfo::TraitAssocPlaceholderHelper => todo!(),
                    InferTyVarSourceInfo::UnifyHelper => todo!(),
                    InferTyVarSourceInfo::DerefHelper => todo!(),
                    InferTyVarSourceInfo::MethodLookupHelper => todo!(),
                };

                let error_ty = tcx.intern(TyKind::Error(error));

                _ = self.bcx.ucx_mut().unify_ty_and_ty(
                    &ClauseOrigin::never_printed(),
                    var_ty,
                    error_ty,
                    RelationMode::Equate,
                );

                self.bcx.ccx_mut().poll_obligations();

                Ok(error_ty)
            }
        }

        ConfirmFolder { bcx: self }.fold(ty)
    }
}
