use crate::{
    base::{
        Diag, Session,
        analysis::SpannedViewEncode,
        arena::{HasInterner, HasListInterner as _, Obj},
        syntax::Span,
    },
    parse::ast::AstLit,
    semantic::{
        analysis::{
            ClauseCx, ClauseImportEnvRef, ClauseOrigin, ClauseOriginKind, CrateTypeckVisitor,
            TyCtxt, TyFolderInfallibleExt, TyVisitorInfallibleExt, UnifyCx, UnifyCxMode,
            typeck::body::lookup::LookupMethodResult,
        },
        lower::generics::normalize_positional_generic_arity,
        syntax::{
            Block, Crate, Divergence, Expr, ExprKind, FnDef, FnInstanceInner, FnLocal,
            HrtbUniverse, InferTyVar, Item, Pat, PatKind, Re, RelationMode, SimpleTyKind,
            SpannedFnInstanceView, SpannedFnOwnerView, SpannedTy, SpannedTyView, Stmt, StructExpr,
            TraitParam, TraitSpec, Ty, TyAndDivergence, TyKind, TyOrRe,
        },
    },
};
use rustc_hash::FxHashMap;

// === Driver === //

impl<'tcx> CrateTypeckVisitor<'tcx> {
    pub fn visit_fn_def(&mut self, def: Obj<FnDef>) {
        let s = self.session();
        let tcx = self.tcx();

        // Setup a `ClauseCx` for signature validation.
        let mut ccx_sig = ClauseCx::new(tcx, self.coherence, self.krate, UnifyCxMode::RegionAware);
        let env_sig = ccx_sig.import_fn_def_env_as_universal(
            &ClauseOrigin::empty_report(),
            HrtbUniverse::ROOT_REF,
            def,
        );

        // WF-check the signature.
        self.visit_generic_binder(&mut ccx_sig, env_sig.as_ref(), def.r(s).generics);

        // TODO
        // if let Some(self_param) = *def.r(s).self_param {
        //     self.visit_spanned_ty(self_param)?;
        // }

        for arg in def.r(s).args.r(s) {
            let arg = ccx_sig
                .importer(
                    &ClauseOrigin::empty_report(),
                    HrtbUniverse::ROOT,
                    env_sig.as_ref(),
                )
                .fold_preserved(arg.ty);

            ccx_sig.wf_visitor(HrtbUniverse::ROOT).visit_spanned(arg);
        }

        let ret_ty = ccx_sig
            .importer(
                &ClauseOrigin::empty_report(),
                HrtbUniverse::ROOT,
                env_sig.as_ref(),
            )
            .fold_preserved(*def.r(s).ret_ty);

        ccx_sig.wf_visitor(HrtbUniverse::ROOT).visit_spanned(ret_ty);

        // Check the body
        if let Some(body) = *def.r(s).body {
            let mut ccx_body =
                ClauseCx::new(tcx, self.coherence, self.krate, UnifyCxMode::RegionBlind);

            let env_body = ccx_body.import_fn_def_env_as_universal(
                &ClauseOrigin::empty_report(),
                HrtbUniverse::ROOT_REF,
                def,
            );

            let mut bcx = BodyCtxt::new(&mut ccx_body, def, env_body.as_ref());

            for arg in def.r(s).args.r(s) {
                bcx.check_pat_and_ascription(arg.pat, Some(arg.ty));
            }

            _ = bcx.check_block(body);

            ccx_body.verify();
        }

        ccx_sig.verify();
    }
}

// === BodyCtxt === //

pub struct BodyCtxt<'a, 'tcx> {
    pub ccx: &'a mut ClauseCx<'tcx>,
    pub def: Obj<FnDef>,
    pub import_env: ClauseImportEnvRef<'a>,
    pub local_types: FxHashMap<Obj<FnLocal>, Ty>,
    pub needs_infer: Vec<NeedsInfer>,
}

#[derive(Copy, Clone)]
pub struct NeedsInfer {
    pub span: Span,
    pub var: InferTyVar,
}

impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
    pub fn new(
        ccx: &'a mut ClauseCx<'tcx>,
        def: Obj<FnDef>,
        import_env: ClauseImportEnvRef<'a>,
    ) -> Self {
        Self {
            ccx,
            def,
            import_env,
            local_types: FxHashMap::default(),
            needs_infer: Vec::new(),
        }
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.ccx.tcx()
    }

    pub fn session(&self) -> &'tcx Session {
        self.ccx.session()
    }

    pub fn krate(&self) -> Obj<Crate> {
        self.ccx().krate()
    }

    pub fn item(&self) -> Obj<Item> {
        let s = self.session();
        self.def.r(s).owner.as_item(s)
    }

    pub fn ccx(&self) -> &ClauseCx<'tcx> {
        self.ccx
    }

    pub fn ccx_mut(&mut self) -> &mut ClauseCx<'tcx> {
        self.ccx
    }

    pub fn ucx(&self) -> &UnifyCx<'tcx> {
        self.ccx.ucx()
    }

    pub fn ucx_mut(&mut self) -> &mut UnifyCx<'tcx> {
        self.ccx.ucx_mut()
    }

    pub fn type_of_local(&mut self, local: Obj<FnLocal>) -> Ty {
        let s = self.session();
        let tcx = self.tcx();

        *self.local_types.entry(local).or_insert_with(|| {
            let var = self.ccx.fresh_ty_infer_var(HrtbUniverse::ROOT);

            self.needs_infer.push(NeedsInfer {
                span: local.r(s).name.span,
                var,
            });

            tcx.intern(TyKind::InferVar(var))
        })
    }

    pub fn check_block(&mut self, block: Obj<Block>) -> TyAndDivergence {
        let s = self.session();
        let tcx = self.tcx();

        let mut divergence = Divergence::MayDiverge;

        for stmt in &block.r(s).stmts {
            match stmt {
                Stmt::Expr(expr) => {
                    self.check_expr(*expr).and_do(&mut divergence);
                }
                Stmt::Let(stmt) => {
                    let pat_ty = self.check_pat_and_ascription(stmt.r(s).pat, stmt.r(s).ascription);

                    if let Some(init) = stmt.r(s).init {
                        self.check_expr_demand(init, pat_ty).and_do(&mut divergence);
                    }

                    if let Some(else_clause) = stmt.r(s).else_clause {
                        let block = self.check_block(else_clause);

                        if block.divergence != Divergence::MustDiverge {
                            Diag::span_err(else_clause.r(s).span, "`else` block must diverge")
                                .emit();
                        }
                    }
                }
            }
        }

        let output = if let Some(last_expr) = block.r(s).last_expr {
            self.check_expr(last_expr).and_do(&mut divergence)
        } else {
            tcx.intern(TyKind::Tuple(tcx.intern_list(&[])))
        };

        TyAndDivergence::new(output, divergence)
    }

    pub fn check_pat_and_ascription(&mut self, pat: Obj<Pat>, ascription: Option<SpannedTy>) -> Ty {
        let pat_ty = self.type_of_pat(pat, None);

        let Some(ascription) = ascription else {
            return pat_ty;
        };

        let env = self.import_env;
        let ascription = self
            .ccx_mut()
            .importer(&ClauseOrigin::empty_report(), HrtbUniverse::ROOT, env)
            .fold_preserved(ascription);

        self.ccx_mut()
            .wf_visitor(HrtbUniverse::ROOT)
            .visit_spanned(ascription);

        self.ccx_mut().oblige_ty_unifies_ty(
            ClauseOrigin::root_report(ClauseOriginKind::Pattern {
                pat_span: ascription.own_span(),
            }),
            pat_ty,
            ascription.value,
            RelationMode::Equate,
        );

        pat_ty
    }

    pub fn check_expr(&mut self, expr: Obj<Expr>) -> TyAndDivergence {
        let s = self.session();
        let tcx = self.tcx();

        let mut divergence = Divergence::MayDiverge;
        let ty = match *expr.r(s).kind {
            ExprKind::Array(obj) => todo!(),
            ExprKind::Call(callee, actual_args) => 'call: {
                let callee = self.check_expr(callee).and_do(&mut divergence);

                if let TyKind::Error(err) =
                    *self.ccx_mut().peel_ty_infer_var_after_poll(callee).r(s)
                {
                    for &actual in actual_args.r(s) {
                        self.check_expr(actual).and_do(&mut divergence);
                    }

                    break 'call tcx.intern(TyKind::Error(err));
                }

                let site_span = expr.r(s).span;
                let fn_once_trait = self.krate().r(s).fn_once_lang_item(s).unwrap();
                let input_ty = self.ccx_mut().fresh_ty_infer(HrtbUniverse::ROOT);
                let output_ty = self.ccx_mut().fresh_ty_infer(HrtbUniverse::ROOT);

                self.ccx_mut().oblige_ty_meets_trait_instantiated(
                    ClauseOrigin::root_report(ClauseOriginKind::FunctionCall { site_span }),
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
                    break 'call tcx.intern(TyKind::Error(
                        Diag::span_err(site_span, "annotations needed on input type").emit(),
                    ));
                };

                if expected_args.r(s).len() != actual_args.r(s).len() {
                    break 'call tcx.intern(TyKind::Error(
                        Diag::span_err(site_span, "argument count mismatch").emit(),
                    ));
                }

                for (&actual, &expected) in actual_args.r(s).iter().zip(expected_args.r(s)) {
                    _ = self
                        .check_expr_demand(actual, expected)
                        .and_do(&mut divergence);
                }

                output_ty
            }
            ExprKind::MethodCall {
                receiver,
                name,
                generics,
                args,
            } => 'call: {
                let receiver_span = receiver.r(s).span;
                let receiver = self.check_expr(receiver).and_do(&mut divergence);
                let receiver = self.ccx_mut().peel_ty_infer_var_after_poll(receiver);

                let env = self.import_env;
                let generics = generics.map(|generics| {
                    let out = self
                        .ccx_mut()
                        .importer(&ClauseOrigin::empty_report(), HrtbUniverse::ROOT, env)
                        .fold_preserved(generics);

                    self.ccx_mut()
                        .wf_visitor(HrtbUniverse::ROOT)
                        .visit_spanned(out);

                    out
                });

                match *receiver.r(s) {
                    TyKind::InferVar(_) => {
                        break 'call tcx.intern(TyKind::Error(
                            Diag::span_err(
                                receiver_span,
                                "type of receiver must be known by this point",
                            )
                            .emit(),
                        ));
                    }
                    TyKind::Error(error) => {
                        break 'call tcx.intern(TyKind::Error(error));
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
                    break 'call tcx.intern(TyKind::Error(
                        Diag::span_err(name.span, "failed to find applicable method").emit(),
                    ));
                };

                let self_ty = self.ccx_mut().fresh_ty_infer(HrtbUniverse::ROOT);
                let owner = self
                    .ccx_mut()
                    .instantiate_fn_def_as_blank_owner_infer(resolution, self_ty);

                let generics = generics.map(|generics| {
                    normalize_positional_generic_arity(
                        tcx,
                        owner.def(s).r(s).generics,
                        None,
                        generics.own_span(),
                        &generics.iter(tcx).collect::<Vec<_>>(),
                    )
                    .value
                });

                let instance = tcx.intern(FnInstanceInner {
                    owner,
                    early_args: generics,
                });

                let instance_env = self.ccx_mut().instantiate_fn_instance_env_as_infer(
                    &ClauseOrigin::root_report(ClauseOriginKind::FunctionCall {
                        site_span: name.span,
                    }),
                    HrtbUniverse::ROOT_REF,
                    instance,
                );

                let (expected_args, expected_output) = self.ccx_mut().import_fn_instance_sig(
                    &ClauseOrigin::empty_report(),
                    HrtbUniverse::ROOT_REF,
                    instance_env.as_ref(),
                    resolution,
                );

                let (self_ty, expected_args) = expected_args.r(s).split_first().unwrap();

                self.ccx_mut().oblige_ty_unifies_ty(
                    ClauseOrigin::root_report(ClauseOriginKind::FunctionCall {
                        site_span: name.span,
                    }),
                    *self_ty,
                    receiver,
                    RelationMode::Equate,
                );

                if expected_args.len() != args.r(s).len() {
                    break 'call tcx.intern(TyKind::Error(
                        Diag::span_err(name.span, "argument count mismatch").emit(),
                    ));
                }

                for (&actual, &expected) in args.r(s).iter().zip(expected_args) {
                    _ = self
                        .check_expr_demand(actual, expected)
                        .and_do(&mut divergence);
                }

                expected_output
            }
            ExprKind::Tuple(children) => {
                let children = children
                    .r(s)
                    .iter()
                    .map(|&expr| self.check_expr(expr).and_do(&mut divergence))
                    .collect::<Vec<_>>();

                tcx.intern(TyKind::Tuple(tcx.intern_list(&children)))
            }
            ExprKind::Binary(ast_bin_op_spanned, obj, obj1) => todo!(),
            ExprKind::Unary(ast_un_op_kind, obj) => todo!(),
            ExprKind::Literal(lit) => match lit {
                AstLit::Number(_) => {
                    // TODO: Register inference constraints.
                    self.ccx.fresh_ty_infer(HrtbUniverse::ROOT)
                }
                AstLit::Char(_) => tcx.intern(TyKind::Simple(SimpleTyKind::Char)),
                AstLit::String(_) => tcx.intern(TyKind::Simple(SimpleTyKind::Str)),
                AstLit::Bool(_) => tcx.intern(TyKind::Simple(SimpleTyKind::Bool)),
            },
            ExprKind::TupleOrUnitCtor(adt_ctor_instance) => todo!(),
            ExprKind::FnItemLit(def, early_args) => {
                let env = self.import_env;
                let early_args = early_args.map(|early_args| {
                    self.ccx_mut()
                        .importer(&ClauseOrigin::empty_report(), HrtbUniverse::ROOT, env)
                        .fold_preserved(early_args)
                });

                let fn_ty = SpannedTyView::FnDef(
                    SpannedFnInstanceView {
                        owner: SpannedFnOwnerView::Item(def).encode(expr.r(s).span, tcx),
                        early_args,
                    }
                    .encode(expr.r(s).span, tcx),
                )
                .encode(expr.r(s).span, tcx);

                self.ccx_mut()
                    .wf_visitor(HrtbUniverse::ROOT)
                    .visit_spanned(fn_ty);

                fn_ty.value
            }
            ExprKind::TypeRelative {
                self_ty,
                as_trait,
                assoc_name,
                assoc_args,
            } => 'res: {
                let env = self.import_env;

                let self_ty = self
                    .ccx_mut()
                    .importer(&ClauseOrigin::empty_report(), HrtbUniverse::ROOT, env)
                    .fold_preserved(self_ty);

                self.ccx_mut()
                    .wf_visitor(HrtbUniverse::ROOT)
                    .visit_spanned(self_ty);

                let as_trait = as_trait.map(|as_trait| {
                    let out = self
                        .ccx_mut()
                        .importer(&ClauseOrigin::empty_report(), HrtbUniverse::ROOT, env)
                        .fold_preserved(as_trait);

                    self.ccx_mut()
                        .wf_visitor(HrtbUniverse::ROOT)
                        .with_clause_applies_to(self_ty.value)
                        .visit_spanned(out);

                    out.value
                });

                let assoc_args = assoc_args.map(|assoc_args| {
                    let out = self
                        .ccx_mut()
                        .importer(&ClauseOrigin::empty_report(), HrtbUniverse::ROOT, env)
                        .fold_preserved(assoc_args);

                    self.ccx_mut()
                        .wf_visitor(HrtbUniverse::ROOT)
                        .visit_spanned(out);

                    out
                });

                let Some(resolution) =
                    self.lookup_type_relative(self_ty.value, as_trait, assoc_name, assoc_args)
                else {
                    break 'res tcx.intern(TyKind::Error(
                        Diag::span_err(assoc_name.span, "not found").emit(),
                    ));
                };

                resolution
            }
            ExprKind::Cast(expr, as_ty) => {
                let env = self.import_env;
                let as_ty = self
                    .ccx_mut()
                    .importer(&ClauseOrigin::empty_report(), HrtbUniverse::ROOT, env)
                    .fold_preserved(as_ty);

                self.ccx_mut()
                    .wf_visitor(HrtbUniverse::ROOT)
                    .visit_spanned(as_ty);

                self.check_expr_demand(expr, as_ty.value)
                    .and_do(&mut divergence)
            }
            ExprKind::If {
                cond,
                truthy,
                falsy,
            } => {
                self.check_expr_demand(cond, tcx.intern(TyKind::Simple(SimpleTyKind::Bool)))
                    .and_do(&mut divergence);

                self.check_exprs_equate([Some(truthy), falsy].into_iter().flatten())
                    .and_do(&mut divergence)
            }
            ExprKind::While(cond, block) => {
                self.check_expr_demand(cond, tcx.intern(TyKind::Simple(SimpleTyKind::Bool)))
                    .and_do(&mut divergence);

                _ = self.check_block(block);

                tcx.intern(TyKind::Tuple(tcx.intern_list(&[])))
            }
            ExprKind::Let(pat, expr) => {
                let pat_ty = self.type_of_pat(pat, Some(&mut divergence));
                self.check_expr_demand(expr, pat_ty).and_do(&mut divergence);

                tcx.intern(TyKind::Simple(SimpleTyKind::Bool))
            }
            ExprKind::ForLoop { pat, iter, body } => todo!(),
            ExprKind::Loop(block) => todo!(),
            ExprKind::Match(obj, obj1) => todo!(),
            ExprKind::Block(block) => self.check_block(block).and_do(&mut divergence),
            ExprKind::Assign(pat, expr) => {
                let pat_ty = self.type_of_pat(pat, Some(&mut divergence));
                self.check_expr_demand(expr, pat_ty).and_do(&mut divergence)
            }
            ExprKind::AssignOp(ast_assign_op_kind, obj, obj1) => todo!(),
            ExprKind::Field(receiver, name) => {
                let receiver = self.check_expr(receiver).and_do(&mut divergence);

                if let Some(ty) = self.lookup_field(receiver, name) {
                    ty
                } else {
                    tcx.intern(TyKind::Error(
                        Diag::span_err(name.span, "no such field").emit(),
                    ))
                }
            }
            ExprKind::Index(obj, obj1) => todo!(),
            ExprKind::Range(range_expr) => todo!(),
            ExprKind::LocalSelf => todo!(),
            ExprKind::Local(local) => self.type_of_local(local),
            ExprKind::AddrOf(mutability, pointee) => {
                let pointee = self.check_expr(pointee).and_do(&mut divergence);
                tcx.intern(TyKind::Reference(Re::Erased, mutability, pointee))
            }
            ExprKind::Break { label, expr } => todo!(),
            ExprKind::Continue { label } => todo!(),
            ExprKind::Return(obj) => todo!(),
            ExprKind::Struct(StructExpr { ctor, fields, rest }) => todo!(),
            ExprKind::Error(err) => tcx.intern(TyKind::Error(err)),
        };

        TyAndDivergence::new(ty, divergence)
    }

    pub fn type_of_pat(&mut self, pat: Obj<Pat>, divergence: Option<&mut Divergence>) -> Ty {
        let s = self.session();

        match pat.r(s).kind {
            PatKind::Hole => self.ccx_mut().fresh_ty_infer(HrtbUniverse::ROOT),
            PatKind::NewName(local, bind_as) => {
                let local_ty = self.type_of_local(local);

                if let Some(bind_as) = bind_as {
                    let bind_as_ty = self.type_of_pat(bind_as, divergence);

                    self.ccx_mut().oblige_ty_unifies_ty(
                        ClauseOrigin::root_report(ClauseOriginKind::Pattern {
                            pat_span: pat.r(s).span,
                        }),
                        local_ty,
                        bind_as_ty,
                        RelationMode::Equate,
                    );
                }

                local_ty
            }
            PatKind::Slice(pat_list_front_and_tail) => todo!(),
            PatKind::Tuple(pat_list_front_and_tail) => todo!(),
            PatKind::Lit(obj) => todo!(),
            PatKind::Or(obj) => todo!(),
            PatKind::Ref(mutability, obj) => todo!(),
            PatKind::AdtUnit(adt_ctor_instance) => todo!(),
            PatKind::AdtTuple(adt_ctor_instance, pat_list_front_and_tail) => todo!(),
            PatKind::AdtNamed(adt_ctor_instance, obj) => todo!(),
            PatKind::PlaceExpr(expr) => self.check_expr(expr).and_do(divergence.unwrap()),
            PatKind::Range(range_expr) => todo!(),
            PatKind::Error(_) => self.ccx_mut().fresh_ty_infer(HrtbUniverse::ROOT),
        }
    }
}
