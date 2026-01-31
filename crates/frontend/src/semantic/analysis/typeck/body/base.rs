use crate::{
    base::{
        Session,
        arena::{HasInterner, HasListInterner as _, Obj},
        syntax::Span,
    },
    parse::ast::AstLit,
    semantic::{
        analysis::{
            ClauseCx, ClauseImportEnv, ClauseImportEnvRef, CrateTypeckVisitor, TyCtxt,
            TyFolderInfallibleExt, TyVisitorInfallibleExt, UnifyCx, UnifyCxMode,
        },
        syntax::{
            Block, Divergence, Expr, ExprKind, FnDef, FuncDefOwner, FuncLocal, InferTyVar,
            SimpleTyKind, Stmt, Ty, TyAndDivergence, TyKind,
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
        let mut ccx = ClauseCx::new(tcx, self.coherence, UnifyCxMode::RegionAware);
        let env = self.setup_env_for_fn_def(def, &mut ccx);

        // WF-check the signature.
        self.visit_generic_binder(&mut ccx, env.as_ref(), def.r(s).generics);

        // TODO
        // if let Some(self_param) = *def.r(s).self_param {
        //     self.visit_spanned_ty(self_param)?;
        // }

        for arg in def.r(s).args.r(s) {
            let arg = ccx.importer(env.as_ref()).fold_preserved(arg.ty);

            ccx.wf_visitor().visit_spanned(arg);
        }

        let ret_ty = ccx.importer(env.as_ref()).fold_preserved(*def.r(s).ret_ty);

        ccx.wf_visitor().visit_spanned(ret_ty);

        // Check the body
        if let Some(body) = *def.r(s).body {
            let mut bcx = BodyCtxt::new(&mut ccx, env.as_ref());
            bcx.check_block(body);
        }

        ccx.verify();
    }

    fn setup_env_for_fn_def(
        &mut self,
        def: Obj<FnDef>,
        ccx: &mut ClauseCx<'tcx>,
    ) -> ClauseImportEnv {
        let s = self.session();
        let tcx = self.tcx();

        let mut env = match def.r(s).owner {
            FuncDefOwner::Func(_item) => ClauseImportEnv {
                self_ty: tcx.intern(TyKind::SigThis),
                sig_generic_substs: Vec::new(),
            },
            FuncDefOwner::Method(def, _idx) => ccx.import_impl_block_env(def),
        };

        env.sig_generic_substs
            .extend_from_slice(&ccx.import_fn_item_env(env.self_ty, def));

        env
    }
}

// === BodyCtxt === //

pub struct BodyCtxt<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    import_env: ClauseImportEnvRef<'a>,
    local_types: FxHashMap<Obj<FuncLocal>, Ty>,
    needs_infer: Vec<NeedsInfer>,
}

#[derive(Copy, Clone)]
struct NeedsInfer {
    span: Span,
    var: InferTyVar,
}

impl<'a, 'tcx> BodyCtxt<'a, 'tcx> {
    pub fn new(ccx: &'a mut ClauseCx<'tcx>, import_env: ClauseImportEnvRef<'a>) -> Self {
        Self {
            ccx,
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

    pub fn type_of_local(&mut self, local: Obj<FuncLocal>) -> Ty {
        let s = self.session();
        let tcx = self.tcx();

        *self.local_types.entry(local).or_insert_with(|| {
            let var = self.ccx.fresh_ty_infer_var();

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
                    todo!()
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

    pub fn check_expr(&mut self, expr: Obj<Expr>) -> TyAndDivergence {
        let s = self.session();
        let tcx = self.tcx();

        let mut divergence = Divergence::MayDiverge;
        let ty = match *expr.r(s).kind {
            ExprKind::Array(obj) => todo!(),
            ExprKind::Call(obj, obj1) => todo!(),
            ExprKind::Method {
                callee,
                generics,
                args,
            } => todo!(),
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
                    self.ccx.fresh_ty_infer()
                }
                AstLit::Char(_) => tcx.intern(TyKind::Simple(SimpleTyKind::Char)),
                AstLit::String(_) => tcx.intern(TyKind::Simple(SimpleTyKind::Str)),
                AstLit::Bool(_) => tcx.intern(TyKind::Simple(SimpleTyKind::Bool)),
            },
            ExprKind::TupleOrUnitCtor(adt_ctor_instance) => todo!(),
            ExprKind::FnItemLit(obj, spanned) => todo!(),
            ExprKind::TypeRelative {
                self_ty,
                as_trait,
                assoc_name,
                assoc_args,
            } => todo!(),
            ExprKind::Cast(expr, as_ty) => {
                let env = self.import_env;
                let as_ty = self.ccx_mut().importer(env).fold(as_ty.value);
                self.check_expr_demand(expr, as_ty).and_do(&mut divergence)
            }
            ExprKind::If {
                cond,
                truthy,
                falsy,
            } => todo!(),
            ExprKind::While(obj, obj1) => todo!(),
            ExprKind::Let(obj, obj1) => todo!(),
            ExprKind::ForLoop { pat, iter, body } => todo!(),
            ExprKind::Loop(obj) => todo!(),
            ExprKind::Match(obj, obj1) => todo!(),
            ExprKind::Block(block) => self.check_block(block).and_do(&mut divergence),
            ExprKind::Assign(obj, obj1) => todo!(),
            ExprKind::AssignOp(ast_assign_op_kind, obj, obj1) => todo!(),
            ExprKind::Field(obj, ident) => todo!(),
            ExprKind::GenericMethodCall {
                target,
                method,
                generics,
                args,
            } => todo!(),
            ExprKind::Index(obj, obj1) => todo!(),
            ExprKind::Range(range_expr) => todo!(),
            ExprKind::LocalSelf => todo!(),
            ExprKind::Local(local) => self.type_of_local(local),
            ExprKind::AddrOf(mutability, obj) => todo!(),
            ExprKind::Break { label, expr } => todo!(),
            ExprKind::Continue { label } => todo!(),
            ExprKind::Return(obj) => todo!(),
            ExprKind::Struct(expr) => todo!(),
            ExprKind::Error(err) => tcx.intern(TyKind::Error(err)),
        };

        TyAndDivergence::new(ty, divergence)
    }
}
