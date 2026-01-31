use crate::{
    base::arena::{HasInterner, HasListInterner, Obj},
    semantic::{
        analysis::{BodyCtxt, CheckOrigin, ClauseCx, NoTraitImplError, ObligationNotReady},
        syntax::{
            Divergence, Expr, Mutability, RelationMode, TraitClauseList, TraitItem, TraitParam,
            TraitSpec, Ty, TyAndDivergence, TyKind, TyOrRe,
        },
    },
};
use smallvec::{SmallVec, smallvec};
use std::cmp::Ordering;

// === BodyCtxt === //

impl BodyCtxt<'_, '_> {
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
}

// === Deref Chains === //

fn compute_deref_glb(ccx: &ClauseCx<'_>, pointees: &[Ty]) -> Vec<u32> {
    ccx.fork_throwaway(|ccx| compute_deref_glb_clobber_obligations(ccx, pointees))
}

fn compute_deref_glb_clobber_obligations(ccx: &mut ClauseCx<'_>, pointees: &[Ty]) -> Vec<u32> {
    let chains = pointees
        .iter()
        .map(|&origin| compute_deref_chain_clobber_obligations(ccx, origin))
        .collect::<Vec<_>>();

    let mut chain_iters = chains.iter().map(|v| v.iter().rev()).collect::<Vec<_>>();

    let (first_chain, other_chains) = chain_iters.split_first_mut().unwrap();

    // If these elements truly had a GLB, they'd have a shared lower bound at the end of the
    // list. We can simply work backwards from that shared lower bound until we find the last
    // element for which all elements are unifiable, at which point, we'd have found our GLB.
    let mut glb_offset_from_back = -1isize;

    'outer: for &first in first_chain {
        for other in &mut *other_chains {
            let Some(other) = other.next() else {
                // We've reached our GLB.
                break 'outer;
            };

            if ccx
                .ucx()
                .clone()
                .unify_ty_and_ty(
                    &CheckOrigin::never_printed(),
                    first,
                    *other,
                    RelationMode::Equate,
                )
                .is_err()
            {
                // We've reached our GLB.
                break 'outer;
            }
        }

        glb_offset_from_back += 1;
    }

    if glb_offset_from_back == -1 {
        // There is no GLB. Don't perform any dereferences.
        return vec![0; pointees.len()];
    }

    chains
        .iter()
        .map(|chain| chain.len() - glb_offset_from_back as usize)
        .map(|v| v as u32)
        .collect::<Vec<_>>()
}

fn compute_deref_chain_clobber_obligations(
    ccx: &mut ClauseCx<'_>,
    mut curr: Ty,
) -> SmallVec<[Ty; 1]> {
    let mut accum = smallvec![curr];
    let tcx = ccx.tcx();

    fn deref_lang_item() -> Obj<TraitItem> {
        todo!()
    }

    loop {
        let next_infer_var = ccx.fresh_ty_infer_var();
        let next_infer = tcx.intern(TyKind::InferVar(next_infer_var));

        match ccx.try_oblige_ty_meets_trait(
            &CheckOrigin::never_printed(),
            curr,
            TraitSpec {
                def: deref_lang_item(),
                params: tcx.intern_list(&[TraitParam::Equals(TyOrRe::Ty(next_infer))]),
            },
        ) {
            Ok(Ok(())) => {
                // (fallthrough)
            }
            Err(ObligationNotReady) | Ok(Err(NoTraitImplError { .. })) => break,
        }

        if let Ok(resolved) = ccx.lookup_ty_infer_var(next_infer_var) {
            curr = resolved;
            accum.push(resolved);
        } else {
            break;
        }
    }

    accum
}

// === CoercionTarget === //

#[derive(Debug, Clone)]
enum CoercionChoice {
    Solid(Ty),
    ThinReference(SmallVec<[Ty; 1]>),
    WideReference(SmallVec<[Ty; 1]>),
}

impl CoercionChoice {
    fn new(bcx: &BodyCtxt<'_, '_>, ty: Ty) -> Self {
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
            CoercionChoice::Solid(_) => 0,
            CoercionChoice::ThinReference(_) => 1,
            CoercionChoice::WideReference(_) => 2,
        }
    }

    fn merge(&mut self, other: CoercionChoice) {
        match self.level().cmp(&other.level()) {
            Ordering::Less => {
                *self = other;
            }
            Ordering::Greater => {
                // (keep the current target)
            }
            Ordering::Equal => match (self, other) {
                (CoercionChoice::Solid(_lhs), CoercionChoice::Solid(_rhs)) => {
                    // (prefer earlier solid choice)
                }
                (CoercionChoice::ThinReference(lhs), CoercionChoice::ThinReference(rhs)) => {
                    lhs.extend(rhs);
                }
                (CoercionChoice::WideReference(lhs), CoercionChoice::WideReference(rhs)) => {
                    lhs.extend(rhs);
                }
                _ => unreachable!(),
            },
        }
    }

    fn resolve(self, bcx: &BodyCtxt<'_, '_>) -> CoercionTarget {
        let s = bcx.session();

        match self {
            CoercionChoice::Solid(ty) => CoercionTarget::Solid(ty),
            CoercionChoice::ThinReference(refs) => {
                let refs = refs.iter().map(|v| match *v.r(s) {
                    TyKind::Reference(_, muta, pointee) => (muta, pointee),
                    _ => unreachable!(),
                });

                let to_muta = refs.clone().map(|v| v.0).min().unwrap();

                let deref_steps = compute_deref_glb(
                    bcx.ccx(),
                    &refs
                        .clone()
                        .map(|(_muta, pointee)| pointee)
                        .collect::<Vec<_>>(),
                );

                CoercionTarget::ThinReference {
                    to_muta,
                    deref_steps,
                }
            }
            CoercionChoice::WideReference(refs) => {
                let refs = refs.iter().map(|v| match *v.r(s) {
                    TyKind::Trait(_, muta, pointee) => (muta, pointee),
                    _ => unreachable!(),
                });

                let to_muta = refs.clone().map(|v| v.0).min().unwrap();

                todo!()
            }
        }
    }
}

enum CoercionTarget {
    Solid(Ty),
    ThinReference {
        to_muta: Mutability,
        deref_steps: Vec<u32>,
    },
    WideReference {
        to_muta: Mutability,
        to_clauses: TraitClauseList,
    },
}
