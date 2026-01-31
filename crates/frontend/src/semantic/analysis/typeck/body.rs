use crate::{
    base::{
        Session,
        arena::{HasInterner, Obj},
        syntax::Span,
    },
    parse::ast::AstLit,
    semantic::{
        analysis::{
            ClauseCx, ClauseImportEnv, CrateTypeckVisitor, TyCtxt, TyFolderInfallibleExt,
            TyVisitorInfallibleExt, UnifyCxMode,
        },
        syntax::{
            Block, Divergence, Expr, ExprKind, FnDef, FuncDefOwner, FuncLocal, InferTyVar,
            Mutability, Re, SimpleTyKind, Stmt, TraitClauseList, Ty, TyAndDivergence, TyKind,
        },
    },
};
use rustc_hash::FxHashMap;
use smallvec::{SmallVec, smallvec};
use std::cmp::Ordering;

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
            let mut bcx = BodyChecker::new(&mut ccx);
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

pub struct BodyChecker<'a, 'tcx> {
    ccx: &'a mut ClauseCx<'tcx>,
    local_types: FxHashMap<Obj<FuncLocal>, Ty>,
    needs_infer: Vec<NeedsInfer>,
}

#[derive(Copy, Clone)]
struct NeedsInfer {
    span: Span,
    var: InferTyVar,
}

#[derive(Debug, Clone)]
enum UnresolvedCoercionTarget {
    Solid(Ty),
    ThinReference(SmallVec<[Ty; 1]>),
    WideReference(SmallVec<[Ty; 1]>),
}

impl UnresolvedCoercionTarget {
    fn new(bcx: &BodyChecker<'_, '_>, ty: Ty) -> Self {
        let s = bcx.session();

        match ty.r(s) {
            TyKind::SigThis | TyKind::SigInfer | TyKind::SigGeneric(_) | TyKind::SigProject(_) => {
                unreachable!()
            }

            TyKind::Simple(_)
            | TyKind::Adt(_)
            | TyKind::Tuple(_)
            | TyKind::FnDef(_, _)
            | TyKind::HrtbVar(_)
            | TyKind::InferVar(_)
            | TyKind::UniversalVar(_)
            | TyKind::Error(_) => Self::Solid(ty),

            TyKind::Reference(_, _, _) => Self::ThinReference(smallvec![ty]),
            TyKind::Trait(_, _, _) => Self::WideReference(smallvec![ty]),
        }
    }

    fn level(&self) -> u8 {
        match self {
            UnresolvedCoercionTarget::Solid(_) => 0,
            UnresolvedCoercionTarget::ThinReference(_) => 1,
            UnresolvedCoercionTarget::WideReference(_) => 2,
        }
    }

    fn merge(&mut self, other: UnresolvedCoercionTarget) {
        match self.level().cmp(&other.level()) {
            Ordering::Less => {
                *self = other;
            }
            Ordering::Greater => {
                // (keep the current target)
            }
            Ordering::Equal => match (self, other) {
                (UnresolvedCoercionTarget::Solid(_lhs), UnresolvedCoercionTarget::Solid(_rhs)) => {
                    // (prefer earlier solid choice)
                }
                (
                    UnresolvedCoercionTarget::ThinReference(lhs),
                    UnresolvedCoercionTarget::ThinReference(rhs),
                ) => {
                    lhs.extend(rhs);
                }
                (
                    UnresolvedCoercionTarget::WideReference(lhs),
                    UnresolvedCoercionTarget::WideReference(rhs),
                ) => {
                    lhs.extend(rhs);
                }
                _ => unreachable!(),
            },
        }
    }

    fn resolve(self, bcx: &BodyChecker<'_, '_>) -> ResolvedCoercionTarget {
        match self {
            UnresolvedCoercionTarget::Solid(ty) => ResolvedCoercionTarget::Solid(ty),
            UnresolvedCoercionTarget::ThinReference(options) => {
                todo!()
            }
            UnresolvedCoercionTarget::WideReference(options) => {
                todo!()
            }
        }
    }
}

enum ResolvedCoercionTarget {
    Solid(Ty),
    ThinReference(Re, Mutability, Ty),
    WideReference(Re, Mutability, TraitClauseList),
}

impl<'a, 'tcx> BodyChecker<'a, 'tcx> {
    pub fn new(ccx: &'a mut ClauseCx<'tcx>) -> Self {
        Self {
            ccx,
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

        todo!()
    }

    pub fn check_exprs_equate_with_demand(
        &mut self,
        exprs: &[Obj<Expr>],
        demand: Option<Ty>,
    ) -> TyAndDivergence {
        let mut divergence = Divergence::MayDiverge;

        // Compute GLB for coercion.
        let (mut glb, exprs) = if let Some(demand) = demand {
            (demand, exprs)
        } else {
            let (first, exprs) = exprs.split_first().unwrap();
            (self.check_expr(*first).and_do(&mut divergence), exprs)
        };

        let exprs = exprs
            .iter()
            .map(|&expr| (expr, self.check_expr(expr).and_do(&mut divergence)))
            .collect::<Vec<_>>();

        for &(_expr, ty) in &exprs {
            self.compute_coercion_glb(ty, &mut glb);
        }

        // Perform coercions.
        for &(expr, ty) in &exprs {
            todo!()
        }

        TyAndDivergence::new(glb, divergence)
    }

    fn compute_coercion_glb(&self, candidate_glb: Ty, current_glb: &mut Ty) {
        let s = self.session();

        match candidate_glb.r(s) {
            TyKind::SigThis | TyKind::SigGeneric(_) | TyKind::SigProject(_) => unreachable!(),

            TyKind::Simple(_)
            | TyKind::Adt(_)
            | TyKind::SigInfer
            | TyKind::Tuple(_)
            | TyKind::UniversalVar(_)
            | TyKind::InferVar(_)
            | TyKind::HrtbVar(_)
            | TyKind::FnDef(_, _)
            | TyKind::Error(_) => {
                // Cannot be a coercion target.
            }

            TyKind::Reference(_candidate_re, candidate_muta, candiate_ty) => {
                todo!()
            }

            TyKind::Trait(re, mutability, intern) => {
                // TODO
            }
        }
    }

    fn coerce_expr(&mut self, expr: Obj<Expr>, target: Ty) {
        todo!()
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
            ExprKind::Tuple(obj) => todo!(),
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
            ExprKind::Cast(obj, spanned) => todo!(),
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
            ExprKind::Block(obj) => todo!(),
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
