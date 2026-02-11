use crate::{
    base::{
        Diag, ErrorGuaranteed,
        arena::{HasInterner, HasListInterner, Obj},
        syntax::Span,
    },
    parse::{ast::entry::C, token::Ident},
    semantic::{
        analysis::{
            BodyCtxt, ClauseCx, ClauseErrorProbe, ClauseOrigin, ClauseOriginKind,
            TyFolderInfallibleExt, UnboundVarHandlingMode,
        },
        syntax::{
            Crate, Divergence, Expr, FnDef, FnInstanceInner, FnOwner, FuncDefOwner, HrtbUniverse,
            Mutability, Re, RelationMode, TraitClauseList, TraitParam, TraitSpec, Ty,
            TyAndDivergence, TyKind, TyOrRe,
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

        self.ccx_mut().poll_obligations();
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

    // TODO: Save the coercions to a fact map
    // TODO: Check mutabilities
    fn apply_coercions(&mut self, exprs: &[(Obj<Expr>, Ty)], target: CoercionResolution) -> Ty {
        let s = self.session();
        let tcx = self.tcx();
        let krate = self.krate();

        match target {
            CoercionResolution::Solid(solid) => {
                for &(expr, actual) in exprs {
                    self.ccx_mut().oblige_ty_unifies_ty(
                        ClauseOrigin::root(ClauseOriginKind::Coercion {
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
                let unify_ty = self.ccx_mut().fresh_ty_infer(HrtbUniverse::ROOT);
                let mut deref_steps = deref_steps.iter();

                for &(expr, actual) in exprs {
                    let actual = self.ccx_mut().peel_ty_infer_var_after_poll(actual);

                    let output_ty = match CoercionPossibility::new(self, actual) {
                        CoercionPossibility::Solid(_) | CoercionPossibility::WideReference(_) => {
                            // Preserve the existing type.
                            actual
                        }
                        CoercionPossibility::ThinReference(_) => {
                            let deref_step_count = *deref_steps.next().unwrap();

                            let TyKind::Reference(_re, _muta, mut output_pointee) = *actual.r(s)
                            else {
                                unreachable!()
                            };

                            for _ in 0..deref_step_count {
                                let next_output = self.ccx_mut().fresh_ty_infer(HrtbUniverse::ROOT);

                                self.ccx_mut().oblige_ty_meets_trait_instantiated(
                                    ClauseOrigin::root(ClauseOriginKind::Coercion {
                                        expr_span: expr.r(s).span,
                                    }),
                                    output_pointee,
                                    TraitSpec {
                                        def: krate.r(s).deref_lang_item(s).unwrap(),
                                        params: tcx.intern_list(&[TraitParam::Equals(TyOrRe::Ty(
                                            next_output,
                                        ))]),
                                    },
                                    HrtbUniverse::ROOT,
                                );

                                output_pointee = next_output;
                            }

                            tcx.intern(TyKind::Reference(Re::Erased, to_muta, output_pointee))
                        }
                    };

                    self.ccx_mut().oblige_ty_unifies_ty(
                        ClauseOrigin::root(ClauseOriginKind::Coercion {
                            expr_span: expr.r(s).span,
                        }),
                        output_ty,
                        unify_ty,
                        RelationMode::Equate,
                    );
                }

                tcx.intern(TyKind::Reference(Re::Erased, to_muta, unify_ty))
            }
            CoercionResolution::WideReference {
                to_muta,
                to_clauses,
            } => {
                for &(expr, actual) in exprs {
                    self.ccx_mut().oblige_ty_meets_clauses(
                        &ClauseOrigin::root(ClauseOriginKind::Coercion {
                            expr_span: expr.r(s).span,
                        }),
                        actual,
                        to_clauses,
                        HrtbUniverse::ROOT_REF,
                    );
                }

                tcx.intern(TyKind::Trait(Re::Erased, to_muta, to_clauses))
            }
        }
    }

    pub fn lookup_method(
        &mut self,
        receiver_span: Span,
        receiver: Ty,
        name: Ident,
    ) -> Result<Obj<FnDef>, ErrorGuaranteed> {
        let s = self.session();
        let tcx = self.tcx();

        self.ccx_mut().poll_obligations();

        let receiver = self
            .ccx()
            .ucx()
            .substitutor(UnboundVarHandlingMode::NormalizeToRoot)
            .fold(receiver);

        if let TyKind::InferVar(_) = receiver.r(s) {
            return Err(
                Diag::span_err(receiver_span, "receiver type must be known by this point").emit(),
            );
        }

        for candidate in self
            .ccx()
            .coherence()
            .gather_inherent_impl_candidates(tcx, receiver, name.text)
        {
            debug_assert!(*candidate.r(s).has_self_param);

            // Check visibility
            if !candidate
                .r(s)
                .impl_vis
                .unwrap()
                .is_visible_to(self.scope(), s)
            {
                continue;
            }

            let FuncDefOwner::ImplMethod(block, method_idx) = *candidate.r(s).owner else {
                continue;
            };

            // See whether receiver is applicable.
            let mut fork = self.ccx().clone();

            let probe = ClauseErrorProbe::default();
            let origin = ClauseOrigin::never_printed().with_probe_sink(probe.clone());

            let self_ty = fork.fresh_ty_infer(HrtbUniverse::ROOT);
            let expected_receiver = fork.instantiate_fn_instance_receiver_as_infer(
                &origin,
                tcx.intern(FnInstanceInner {
                    owner: FnOwner::Inherent {
                        self_ty,
                        block,
                        method_idx,
                    },
                    early_args: None,
                }),
                HrtbUniverse::ROOT_REF,
            );

            fork.oblige_ty_unifies_ty(origin, receiver, expected_receiver, RelationMode::Equate);
            fork.poll_obligations();

            if probe.had_error() {
                continue;
            }

            dbg!(candidate.r(s).span);
        }

        Err(Diag::span_err(name.span, "not yet supported").emit())
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
    fn new(bcx: &mut BodyCtxt<'_, '_>, ty: Ty) -> Self {
        let s = bcx.session();

        let ty = bcx.ccx_mut().peel_ty_infer_var_after_poll(ty);

        match *ty.r(s) {
            TyKind::SigThis
            | TyKind::SigInfer
            | TyKind::SigGeneric(_)
            | TyKind::SigProject(_)
            | TyKind::SigAlias(_, _) => {
                unreachable!()
            }

            TyKind::Simple(_)
            | TyKind::Adt(_)
            | TyKind::Tuple(_)
            | TyKind::FnDef(_)
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
                    bcx.krate(),
                    &refs
                        .clone()
                        .map(|(_muta, pointee)| pointee)
                        .collect::<Vec<_>>(),
                );

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

fn compute_deref_glb(ccx: &ClauseCx<'_>, krate: Obj<Crate>, pointees: &[Ty]) -> Vec<u32> {
    compute_deref_glb_clobber_obligations(&mut ccx.clone(), krate, pointees)
}

fn compute_deref_glb_clobber_obligations(
    ccx: &mut ClauseCx<'_>,
    krate: Obj<Crate>,
    pointees: &[Ty],
) -> Vec<u32> {
    let chains = pointees
        .iter()
        .map(|&origin| compute_deref_chain_clobber_obligations(ccx, krate, origin))
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
                    &ClauseOrigin::never_printed(),
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
        .map(|chain| chain.len() - glb_offset_from_back as usize - 1)
        .map(|v| v as u32)
        .collect::<Vec<_>>()
}

fn compute_deref_chain_clobber_obligations(
    ccx: &mut ClauseCx<'_>,
    krate: Obj<Crate>,
    mut curr: Ty,
) -> SmallVec<[Ty; 1]> {
    let tcx = ccx.tcx();
    let s = ccx.session();

    let mut accum = smallvec![curr];

    loop {
        let next_infer_var = ccx.fresh_ty_infer_var(HrtbUniverse::ROOT);
        let next_infer = tcx.intern(TyKind::InferVar(next_infer_var));

        // This probing routine works by attempting to resolve an obligation as much as possible and
        // bailing out if an error occurs.
        //
        // Doing this roughly matches `rustc`'s behavior...
        //
        // ```
        // use core::ops::Deref;
        //
        // pub struct Foo;
        //
        // pub struct Bar<T>([T; 0]);
        //
        // impl<T> Bar<T> {
        //     fn bind(&self, _: T) {}
        // }
        //
        // impl<T: Copy> Deref for Bar<T> {
        //     type Target = Foo;
        //
        //     fn deref(&self) -> &Foo {
        //         &Foo
        //     }
        // }
        //
        // // Okay!
        // fn example_1() {
        //     let bar = &Bar::<_>([]);
        //     [&Foo, bar];
        //
        //     bar.bind(3i32);
        // }
        //
        // // No coercion is performed.
        // fn example_2() {
        //     let bar = &Bar::<_>([]);
        //     bar.bind(Vec::new());
        //     [&Foo, bar];
        // }
        //
        // // We complain about `Vec` not being `Copy`.
        // fn example_3() {
        //     let bar = &Bar::<_>([]);
        //     [&Foo, bar];
        //     bar.bind(Vec::new());
        // }
        // ```
        let probe = ClauseErrorProbe::default();

        ccx.oblige_ty_meets_trait_instantiated(
            ClauseOrigin::never_printed().with_probe_sink(probe.clone()),
            curr,
            TraitSpec {
                def: krate.r(s).deref_lang_item(s).unwrap(),
                params: tcx.intern_list(&[TraitParam::Equals(TyOrRe::Ty(next_infer))]),
            },
            HrtbUniverse::ROOT,
        );

        ccx.poll_obligations();

        if probe.had_error() {
            break;
        }

        if let Ok(resolved) = ccx.lookup_ty_infer_var_after_poll(next_infer_var) {
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
