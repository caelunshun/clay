use crate::{
    base::arena::{HasInterner as _, HasListInterner as _, Obj},
    parse::ast::AstRangeLimits,
    semantic::{
        analysis::typeck::BodyCtxt,
        syntax::{
            AdtInstance, AdtItem, Divergence, DivergenceAnd, DivergenceJoin, HirRangeExpr, Ty,
            TyCtxt, TyKind, TyOrRe,
        },
    },
};

#[derive(Debug, Copy, Clone)]
pub enum CheckedRangeExpr {
    Full,
    RangeFrom(Ty),
    RangeTo(Ty),
    Range(Ty),
    RangeToInclusive(Ty),
    RangeInclusive(Ty),
}

impl CheckedRangeExpr {
    pub fn elem_ty(self) -> Option<Ty> {
        match self {
            CheckedRangeExpr::RangeFrom(ty)
            | CheckedRangeExpr::RangeTo(ty)
            | CheckedRangeExpr::Range(ty)
            | CheckedRangeExpr::RangeToInclusive(ty)
            | CheckedRangeExpr::RangeInclusive(ty) => Some(ty),
            CheckedRangeExpr::Full => None,
        }
    }
    pub fn range_ty(self, bcx: &mut BodyCtxt<'_, '_>) -> Ty {
        let s = bcx.session();
        let tcx = bcx.tcx();
        let lang_items = &bcx.krate().r(s).lang_items;

        fn make(tcx: &TyCtxt, item: Obj<AdtItem>, ty: Option<Ty>) -> Ty {
            tcx.intern(TyKind::Adt(AdtInstance {
                def: item,
                params: match ty {
                    Some(ty) => tcx.intern_list(&[TyOrRe::Ty(ty)]),
                    None => tcx.intern_list(&[]),
                },
            }))
        }

        match self {
            CheckedRangeExpr::Full => make(tcx, lang_items.range_full().unwrap(), None),
            CheckedRangeExpr::RangeFrom(ty) => {
                make(tcx, lang_items.range_from().unwrap(), Some(ty))
            }
            CheckedRangeExpr::RangeTo(ty) => make(tcx, lang_items.range_to().unwrap(), Some(ty)),
            CheckedRangeExpr::Range(ty) => make(tcx, lang_items.range().unwrap(), Some(ty)),
            CheckedRangeExpr::RangeToInclusive(ty) => {
                make(tcx, lang_items.range_to_inclusive().unwrap(), Some(ty))
            }
            CheckedRangeExpr::RangeInclusive(ty) => {
                make(tcx, lang_items.range_inclusive().unwrap(), Some(ty))
            }
        }
    }
}

impl<'tcx> BodyCtxt<'_, 'tcx> {
    pub fn check_range_expr(&mut self, expr: HirRangeExpr) -> DivergenceAnd<CheckedRangeExpr> {
        let mut divergence = Divergence::MayDiverge;

        let HirRangeExpr { low, high, limits } = expr;

        let ty = match (low, high) {
            (None, None) => None,
            (None, Some(rhs)) => Some(self.check_expr(rhs, None).and_do(&mut divergence)),
            (Some(lhs), None) => Some(self.check_expr(lhs, None).and_do(&mut divergence)),
            (Some(lhs), Some(rhs)) => Some(
                self.check_exprs_equate([lhs, rhs], DivergenceJoin::Sequential)
                    .and_do(&mut divergence),
            ),
        };

        let expr = match (low, high, limits) {
            (None, None, AstRangeLimits::HalfOpen) => CheckedRangeExpr::Full,
            (Some(_), None, AstRangeLimits::HalfOpen) => CheckedRangeExpr::RangeFrom(ty.unwrap()),
            (None, Some(_), AstRangeLimits::HalfOpen) => CheckedRangeExpr::RangeTo(ty.unwrap()),
            (Some(_), Some(_), AstRangeLimits::HalfOpen) => CheckedRangeExpr::Range(ty.unwrap()),
            (None, Some(_), AstRangeLimits::Closed) => {
                CheckedRangeExpr::RangeToInclusive(ty.unwrap())
            }
            (Some(_), Some(_), AstRangeLimits::Closed) => {
                CheckedRangeExpr::RangeInclusive(ty.unwrap())
            }
            (_, None, AstRangeLimits::Closed) => {
                unreachable!()
            }
        };

        DivergenceAnd::new(expr, divergence)
    }
}
