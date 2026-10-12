use crate::{
    base::{
        Diag,
        arena::{HasInterner, HasListInterner as _, LateInit, Obj},
    },
    parse::token::Ident,
    semantic::{
        analysis::typeck::{
            BodyCtxt,
            infra::{
                confirm::ThirExprConfirmedWithTy,
                lookup::{LookupFieldResult, LookupMethodResult},
            },
        },
        infer::{ClauseFuel, FixArity, HrtbUniverse, SpannedError},
        syntax::{
            Divergence, HirExpr, InferTyVarSourceInfo, InstantiatedFnSig, RelationMode,
            SigGenericList, ThirExpr, ThirExprKind, TraitParam, TraitSpec, TyKind, TyOrRe,
        },
    },
};

impl BodyCtxt<'_, '_> {
    pub fn check_expr_inner_call(
        &mut self,
        expr: Obj<HirExpr>,
        callee_expr: Obj<HirExpr>,
        actual_args: Obj<[Obj<HirExpr>]>,
        divergence: &mut Divergence,
    ) -> ThirExprConfirmedWithTy {
        let tcx = self.tcx();
        let s = self.session();

        let callee = self.check_expr(callee_expr, None).and_do(divergence);

        if let TyKind::Error(err) = *self.ccx_mut().peel_ty_infer_var_after_poll(callee).r(s) {
            for &actual in actual_args.r(s) {
                self.check_expr(actual, None).and_do(divergence);
            }

            return self.put_thir_expr_err(expr, err);
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

        self.ccx_mut()
            .oblige_ty_meets_trait_instantiated(
                ClauseFuel::new(),
                HrtbUniverse::ROOT,
                callee,
                TraitSpec {
                    def: fn_once_trait,
                    params: tcx.intern_list(&[
                        TraitParam::Equals(TyOrRe::Ty(input_ty)),
                        TraitParam::Equals(TyOrRe::Ty(output_ty)),
                    ]),
                },
            )
            // TODO
            .map(move |_ccx, error| SpannedError(site_span, error))
            .report_loud();

        let TyKind::Tuple(expected_args) =
            self.ccx_mut().peel_ty_infer_var_after_poll(input_ty).r(s)
        else {
            return self.put_thir_expr_err(
                expr,
                Diag::span_err(site_span, "annotations needed on input type").emit(),
            );
        };

        if expected_args.r(s).len() != actual_args.r(s).len() {
            return self.put_thir_expr_err(
                expr,
                Diag::span_err(site_span, "argument count mismatch").emit(),
            );
        }

        for (&actual, &expected) in actual_args.r(s).iter().zip(expected_args.r(s)) {
            self.check_expr_demand(actual, expected).and_do(divergence);
        }

        self.put_thir_expr(expr, output_ty, move |bcx| {
            ThirExprKind::Call(
                bcx.confirm_thir_expr_post(callee_expr),
                bcx.confirm_thir_expr_list_post(actual_args),
            )
        })
    }

    pub fn check_expr_inner_method_call(
        &mut self,
        expr: Obj<HirExpr>,
        receiver_expr: Obj<HirExpr>,
        name: Ident,
        generics: Option<SigGenericList>,
        args: Obj<[Obj<HirExpr>]>,
        divergence: &mut Divergence,
    ) -> ThirExprConfirmedWithTy {
        let s = self.session();

        let receiver_span = receiver_expr.r(s).span;
        let receiver = self.check_expr(receiver_expr, None).and_do(divergence);
        let receiver = self.ccx_mut().peel_ty_infer_var_after_poll(receiver);

        match *receiver.r(s) {
            TyKind::InferVar(_) => {
                let err = Diag::span_err(
                    receiver_span,
                    "type of receiver must be known by this point",
                )
                .emit();

                return self.put_thir_expr_err(expr, err);
            }
            TyKind::Error(err) => {
                return self.put_thir_expr_err(expr, err);
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
            return self.put_thir_expr_err(
                expr,
                Diag::span_err(name.span, "failed to find applicable method").emit(),
            );
        };

        let self_ty = self.ccx_mut().fresh_ty_infer(
            HrtbUniverse::ROOT,
            InferTyVarSourceInfo::MethodReceiver { span: name.span },
        );

        let owner = self
            .ccx_mut()
            .fresh_type_relative_fn_def_to_fn_owner(
                ClauseFuel::new(),
                HrtbUniverse::ROOT_REF,
                self_ty,
                resolution,
            )
            // TODO
            .map(move |_ccx, error| SpannedError(name.span, error))
            .report_loud();

        let instance = self
            .ccx
            .importer_here(self.import_env)
            .import_fn_instance_from_owner(owner, generics, FixArity::Normalize)
            .report_loud();

        let InstantiatedFnSig {
            args: expected_args,
            ret_ty: expected_output,
        } = self
            .ccx_mut()
            .resolve_fn_instance_sig(ClauseFuel::new(), HrtbUniverse::ROOT_REF, instance)
            // TODO
            .report_loud();

        let (self_ty, expected_args) = expected_args.r(s).split_first().unwrap();

        self.ccx_mut()
            .oblige_ty_unifies_ty(*self_ty, receiver, RelationMode::Equate)
            // TODO
            .map(move |_ccx, error| SpannedError(name.span, error))
            .report_loud();

        if expected_args.len() != args.r(s).len() {
            return self.put_thir_expr_err(
                expr,
                Diag::span_err(name.span, "argument count mismatch").emit(),
            );
        }

        for (&actual, &expected) in args.r(s).iter().zip(expected_args) {
            self.check_expr_demand(actual, expected).and_do(divergence);
        }

        self.put_thir_expr(expr, expected_output, move |bcx| {
            let s = bcx.session();
            let tcx = bcx.tcx();

            ThirExprKind::Call(
                Obj::new(
                    ThirExpr {
                        span: expr.r(s).span,
                        ty: bcx
                            .ccx_mut()
                            .export(expr.r(s).span, tcx.intern(TyKind::FnDef(instance))),
                        kind: LateInit::new(ThirExprKind::CreateZst),
                    },
                    s,
                ),
                bcx.confirm_thir_expr_iter_post(
                    [receiver_expr]
                        .iter()
                        .chain(args.r(s))
                        .copied()
                        .collect::<Vec<_>>(),
                ),
            )
        })
    }

    pub fn check_expr_inner_field(
        &mut self,
        expr: Obj<HirExpr>,
        receiver_expr: Obj<HirExpr>,
        name: Ident,
        divergence: &mut Divergence,
    ) -> ThirExprConfirmedWithTy {
        let receiver = self.check_expr(receiver_expr, None).and_do(divergence);

        match self.lookup_field(receiver_expr, receiver, name) {
            Ok(Some(LookupFieldResult { ty, index })) => self.put_thir_expr(expr, ty, move |bcx| {
                ThirExprKind::Field(bcx.confirm_thir_expr_post(receiver_expr), index)
            }),
            Ok(None) => {
                self.put_thir_expr_err(expr, Diag::span_err(name.span, "no such field").emit())
            }
            Err(err) => self.put_thir_expr_err(expr, err),
        }
    }
}
