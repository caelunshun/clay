use crate::{
    base::arena::{HasInterner, HasListInterner, Obj},
    semantic::{
        analysis::{
            BodyCtxt, CheckOrigin, CheckOriginKind, ClauseCx, NoTraitImplError, ObligationNotReady,
        },
        syntax::{
            Divergence, Expr, Mutability, Re, RelationMode, TraitClauseList, TraitItem, TraitParam,
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
        exprs: impl IntoIterator<Item = Obj<Expr>>,
        demand: Option<Ty>,
    ) -> TyAndDivergence {
        if let Some(demand) = demand {
            self.check_exprs_demand(exprs, demand)
        } else {
            self.check_exprs_equate(exprs)
        }
    }

    pub fn check_exprs_equate(
        &mut self,
        exprs: impl IntoIterator<Item = Obj<Expr>>,
    ) -> TyAndDivergence {
        let mut divergence = Divergence::MayDiverge;

        let exprs = exprs
            .into_iter()
            .map(|expr| {
                let actual = self.check_expr(expr).and_do(&mut divergence);
                (expr, actual)
            })
            .collect::<Vec<_>>();

        // Compute GLB
        let (&(_first_expr, first_actual), other) = exprs.split_first().unwrap();

        let mut glb = CoercionPossibility::new(self, first_actual);

        for &(_other_expr, other_actual) in other {
            glb.merge(CoercionPossibility::new(self, other_actual));
        }

        let glb = glb.resolve(self);

        // Apply coercion
        let output = self.apply_coercions(&exprs, glb);

        TyAndDivergence::new(output, divergence)
    }

    pub fn check_exprs_demand(
        &mut self,
        exprs: impl IntoIterator<Item = Obj<Expr>>,
        demand: Ty,
    ) -> TyAndDivergence {
        let mut divergence = Divergence::MayDiverge;

        for expr in exprs {
            self.check_expr_demand(expr, demand).and_do(&mut divergence);
        }

        TyAndDivergence::new(demand, divergence)
    }

    pub fn check_expr_demand(&mut self, expr: Obj<Expr>, demand: Ty) -> TyAndDivergence {
        let mut divergence = Divergence::MayDiverge;

        let actual = self.check_expr(expr).and_do(&mut divergence);
        let target = CoercionPossibility::new(self, demand).resolve(self);
        self.apply_coercions(&[(expr, actual)], target);

        TyAndDivergence::new(demand, divergence)
    }

    fn apply_coercions(&mut self, exprs: &[(Obj<Expr>, Ty)], target: CoercionResolution) -> Ty {
        let s = self.session();
        let tcx = self.tcx();

        match target {
            CoercionResolution::Solid(solid) => {
                for &(expr, actual) in exprs {
                    self.ccx_mut().oblige_ty_unifies_ty(
                        CheckOrigin::root(CheckOriginKind::Coercion {
                            expr_span: expr.r(s).span,
                        }),
                        actual,
                        solid,
                        RelationMode::Equate,
                    );
                }

                solid
            }
            CoercionResolution::ThinReference {
                to_muta,
                deref_steps,
            } => {
                let unify_pointee = self.ccx_mut().fresh_ty_infer();
                let mut deref_steps = deref_steps.iter();

                for &(expr, actual) in exprs {
                    let mut output_pointee = actual;

                    match CoercionPossibility::new(self, actual) {
                        CoercionPossibility::Solid(_) | CoercionPossibility::WideReference(_) => {
                            // (nothing to do)
                        }
                        CoercionPossibility::ThinReference(_) => {
                            let deref_step_count = *deref_steps.next().unwrap();

                            for _ in 0..deref_step_count {
                                let next_output = self.ccx_mut().fresh_ty_infer();

                                self.ccx_mut().oblige_ty_meets_trait_instantiated(
                                    CheckOrigin::root(CheckOriginKind::Coercion {
                                        expr_span: expr.r(s).span,
                                    }),
                                    output_pointee,
                                    TraitSpec {
                                        def: deref_lang_item(),
                                        params: tcx.intern_list(&[TraitParam::Equals(TyOrRe::Ty(
                                            next_output,
                                        ))]),
                                    },
                                );

                                output_pointee = next_output;
                            }
                        }
                    }

                    self.ccx_mut().oblige_ty_unifies_ty(
                        CheckOrigin::root(CheckOriginKind::Coercion {
                            expr_span: expr.r(s).span,
                        }),
                        output_pointee,
                        unify_pointee,
                        RelationMode::Equate,
                    );
                }

                tcx.intern(TyKind::Reference(Re::Erased, to_muta, unify_pointee))
            }
            CoercionResolution::WideReference {
                to_muta,
                to_clauses,
            } => {
                for &(expr, actual) in exprs {
                    self.ccx_mut().oblige_ty_meets_clauses(
                        &CheckOrigin::root(CheckOriginKind::Coercion {
                            expr_span: expr.r(s).span,
                        }),
                        actual,
                        to_clauses,
                    );
                }

                tcx.intern(TyKind::Trait(Re::Erased, to_muta, to_clauses))
            }
        }
    }
}

// === CoercionTarget === //

#[derive(Debug, Clone)]
enum CoercionPossibility {
    Solid(Ty),
    ThinReference(SmallVec<[Ty; 1]>),
    WideReference(Ty),
}

impl CoercionPossibility {
    fn new(bcx: &BodyCtxt<'_, '_>, ty: Ty) -> Self {
        let s = bcx.session();
        let ty = bcx.ccx().peel_ty_infer_var(ty);

        match *ty.r(s) {
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
            TyKind::Trait(_, _, _) => Self::WideReference(ty),
        }
    }

    fn level(&self) -> u8 {
        match self {
            CoercionPossibility::Solid(_) => 0,
            CoercionPossibility::ThinReference(_) => 1,
            CoercionPossibility::WideReference(_) => 2,
        }
    }

    fn merge(&mut self, other: CoercionPossibility) {
        match self.level().cmp(&other.level()) {
            Ordering::Less => {
                *self = other;
            }
            Ordering::Greater => {
                // (keep the current target)
            }
            Ordering::Equal => match (self, other) {
                (CoercionPossibility::Solid(_), CoercionPossibility::Solid(_))
                | (CoercionPossibility::WideReference(_), CoercionPossibility::WideReference(_)) => {
                    // (prefer earlier choice)
                }
                (
                    CoercionPossibility::ThinReference(lhs),
                    CoercionPossibility::ThinReference(rhs),
                ) => {
                    lhs.extend(rhs);
                }
                _ => unreachable!(),
            },
        }
    }

    fn resolve(self, bcx: &BodyCtxt<'_, '_>) -> CoercionResolution {
        let s = bcx.session();

        match self {
            CoercionPossibility::Solid(ty) => CoercionResolution::Solid(ty),
            CoercionPossibility::ThinReference(refs) => {
                let refs = refs.iter().map(|&ty| match *ty.r(s) {
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

                let deref_steps = if deref_steps.contains(&0) {
                    deref_steps
                } else {
                    // Do not perform GLB coercion if the GLB target is not one of the existing
                    // references to match `rustc`'s behavior.
                    vec![0; refs.len()]
                };

                CoercionResolution::ThinReference {
                    to_muta,
                    deref_steps,
                }
            }
            CoercionPossibility::WideReference(ty) => {
                let TyKind::Trait(_, to_muta, to_clauses) = *ty.r(s) else {
                    unreachable!()
                };

                CoercionResolution::WideReference {
                    to_muta,
                    to_clauses,
                }
            }
        }
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

    loop {
        let next_infer_var = ccx.fresh_ty_infer_var();
        let next_infer = tcx.intern(TyKind::InferVar(next_infer_var));

        match ccx.try_oblige_ty_meets_trait_instantiated(
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

#[derive(Debug, Clone)]
enum CoercionResolution {
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

fn deref_lang_item() -> Obj<TraitItem> {
    todo!()
}
