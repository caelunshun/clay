use crate::{
    base::{
        Diag,
        arena::{HasInterner as _, HasListInterner as _, Obj},
    },
    parse::token::Ident,
    semantic::{
        analysis::typeck::{BodyCtxt, infra::lookup::LookupMethodResult},
        infer::{HrtbUniverse, ObligeCause, ObligeCauseOrigin},
        lower::generics::normalize_positional_generic_arity_zip,
        syntax::{
            Divergence, FnInstanceInner, HirExpr, InferTyVarSourceInfo, RelationMode,
            SpannedTyOrReList, TraitParam, TraitSpec, Ty, TyKind, TyOrRe,
        },
    },
};

impl BodyCtxt<'_, '_> {
    pub fn check_expr_inner_call(
        &mut self,
        expr: Obj<HirExpr>,
        callee: Obj<HirExpr>,
        actual_args: Obj<[Obj<HirExpr>]>,
        divergence: &mut Divergence,
    ) -> Ty {
        let tcx = self.tcx();
        let s = self.session();

        let callee = self.check_expr(callee, None).and_do(divergence);

        if let TyKind::Error(err) = *self.ccx_mut().peel_ty_infer_var_after_poll(callee).r(s) {
            for &actual in actual_args.r(s) {
                self.check_expr(actual, None).and_do(divergence);
            }

            return tcx.intern(TyKind::Error(err));
        }

        let site_span = expr.r(s).span;
        let fn_once_trait = self.krate().r(s).lang_items.fn_once_trait().unwrap();
        let input_ty = self.ccx_mut().fresh_ty_infer(
            HrtbUniverse::ROOT,
            InferTyVarSourceInfo::FunctionArgs { span: site_span },
        );

        let output_ty = self.ccx_mut().fresh_ty_infer(
            HrtbUniverse::ROOT,
            InferTyVarSourceInfo::FunctionRetVal { span: site_span },
        );

        self.ccx_mut().oblige_ty_meets_trait_instantiated(
            ObligeCause::new_report(ObligeCauseOrigin::HirBodyCheckFunctionCall { site_span }),
            HrtbUniverse::ROOT,
            callee,
            TraitSpec {
                def: fn_once_trait,
                params: tcx.intern_list(&[
                    TraitParam::Equals(TyOrRe::Ty(input_ty)),
                    TraitParam::Equals(TyOrRe::Ty(output_ty)),
                ]),
            },
        );

        let TyKind::Tuple(expected_args) =
            self.ccx_mut().peel_ty_infer_var_after_poll(input_ty).r(s)
        else {
            return tcx.intern(TyKind::Error(
                Diag::span_err(site_span, "annotations needed on input type").emit(),
            ));
        };

        if expected_args.r(s).len() != actual_args.r(s).len() {
            return tcx.intern(TyKind::Error(
                Diag::span_err(site_span, "argument count mismatch").emit(),
            ));
        }

        for (&actual, &expected) in actual_args.r(s).iter().zip(expected_args.r(s)) {
            self.check_expr_demand(actual, expected).and_do(divergence);
        }

        output_ty
    }

    pub fn check_expr_inner_method_call(
        &mut self,
        receiver: Obj<HirExpr>,
        name: Ident,
        generics: Option<SpannedTyOrReList>,
        args: Obj<[Obj<HirExpr>]>,
        divergence: &mut Divergence,
    ) -> Ty {
        let tcx = self.tcx();
        let s = self.session();

        let receiver_span = receiver.r(s).span;
        let receiver = self.check_expr(receiver, None).and_do(divergence);
        let receiver = self.ccx_mut().peel_ty_infer_var_after_poll(receiver);

        let env = self.import_env;
        let generic_segment_span = generics.map(|v| v.own_span());
        let generic_param_spans =
            generics.map(|v| v.iter(tcx).map(|v| v.own_span()).collect::<Vec<_>>());

        let generics = generics.map(|generics| {
            self.ccx_mut()
                .import_report_here(HrtbUniverse::ROOT_REF, env, generics)
        });

        match *receiver.r(s) {
            TyKind::InferVar(_) => {
                return tcx.intern(TyKind::Error(
                    Diag::span_err(
                        receiver_span,
                        "type of receiver must be known by this point",
                    )
                    .emit(),
                ));
            }
            TyKind::Error(error) => {
                return tcx.intern(TyKind::Error(error));
            }
            _ => {
                // (fallthrough)
            }
        }

        let Some(LookupMethodResult {
            receiver,
            resolution,
        }) = self.lookup_method(receiver, name)
        else {
            return tcx.intern(TyKind::Error(
                Diag::span_err(name.span, "failed to find applicable method").emit(),
            ));
        };

        let self_ty = self.ccx_mut().fresh_ty_infer(
            HrtbUniverse::ROOT,
            InferTyVarSourceInfo::MethodReceiver { span: name.span },
        );

        let owner = self
            .ccx_mut()
            .create_infer_env_for_fn_def_as_blank_owner(resolution, self_ty);

        let generics = generics.map(|generics| {
            normalize_positional_generic_arity_zip(
                tcx,
                owner.def(s).r(s).generics,
                None,
                generic_segment_span.unwrap(),
                generics.r(s),
                generic_param_spans.as_ref().unwrap(),
            )
        });

        let instance = tcx.intern(FnInstanceInner {
            owner,
            early_args: generics,
        });

        let instance_env = self.ccx_mut().create_infer_env_for_fn_instance(
            &ObligeCause::new_report(ObligeCauseOrigin::HirBodyCheckFunctionCall {
                site_span: name.span,
            }),
            HrtbUniverse::ROOT_REF,
            instance,
        );

        let (expected_args, expected_output) = self.ccx_mut().import_fn_instance_sig(
            &ObligeCause::new_empty_report(),
            HrtbUniverse::ROOT_REF,
            instance_env.as_ref(),
            resolution,
        );

        let (self_ty, expected_args) = expected_args.r(s).split_first().unwrap();

        self.ccx_mut().oblige_ty_unifies_ty(
            ObligeCause::new_report(ObligeCauseOrigin::HirBodyCheckFunctionCall {
                site_span: name.span,
            }),
            *self_ty,
            receiver,
            RelationMode::Equate,
        );

        if expected_args.len() != args.r(s).len() {
            return tcx.intern(TyKind::Error(
                Diag::span_err(name.span, "argument count mismatch").emit(),
            ));
        }

        for (&actual, &expected) in args.r(s).iter().zip(expected_args) {
            self.check_expr_demand(actual, expected).and_do(divergence);
        }

        expected_output
    }

    pub fn check_expr_inner_field(
        &mut self,
        receiver: Obj<HirExpr>,
        name: Ident,
        divergence: &mut Divergence,
    ) -> Ty {
        let tcx = self.tcx();
        let receiver = self.check_expr(receiver, None).and_do(divergence);

        if let Some(ty) = self.lookup_field(receiver, name) {
            ty
        } else {
            tcx.intern(TyKind::Error(
                Diag::span_err(name.span, "no such field").emit(),
            ))
        }
    }
}
