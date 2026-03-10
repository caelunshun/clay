use crate::{
    base::{Diag, arena::HasInterner},
    semantic::{
        analysis::{BodyCtxt, ClauseCxPrinter, ClauseOrigin, FloatingInferVar},
        syntax::{InferTyVarSourceInfo, RelationMode, TyKind},
    },
};

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

        // Error out for types that are missing inferences.
        self.ccx_mut().poll_obligations();

        for idx in 0..self.needs_infer.len() {
            let var = self.needs_infer[idx];

            if self.ccx().lookup_ty_infer_var_without_poll(var).is_ok() {
                continue;
            }

            let var_ty = tcx.intern(TyKind::InferVar(var));

            let error = match self.ccx().lookup_infer_ty_src_info(var) {
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
                        let mut printer = ClauseCxPrinter::new(self.ccx());
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

            _ = self.ucx_mut().unify_ty_and_ty(
                &ClauseOrigin::never_printed(),
                var_ty,
                tcx.intern(TyKind::Error(error)),
                RelationMode::Equate,
            );

            self.ccx_mut().poll_obligations();
        }
    }
}
