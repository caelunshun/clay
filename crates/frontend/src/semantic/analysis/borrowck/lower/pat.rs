use crate::{
    base::{arena::Obj, syntax::Span},
    semantic::{
        analysis::borrowck::{
            lower::driver::MirFromThirCtx,
            scopes::{CanHoistLocals, MirScopedBuilder, MirScopedBuilderRef},
        },
        syntax::{
            MirLocal, MirLocalIdx, MirOperand, MirPlace, MirPlaceElem, MirRvalue, MirScopeIdx,
            MirSourceInfo, Mutability, ResolvedFieldIdx, SigRe, SigReKind, SigTyInner, SigTyKind,
            ThirExpr, ThirLetStmt, ThirLocal, ThirMatchArm, ThirPat, ThirPatKind,
        },
    },
};
use clay_core::FastHashMap;

#[derive(Debug, Copy, Clone)]
struct PatLowerScopes {
    pub local_scope: MirScopeIdx,
    pub match_logic: MirScopeIdx,
    pub break_on_accept: MirScopeIdx,
    pub break_on_reject: MirScopeIdx,
}

type LateUseProxyMap = FastHashMap<MirLocalIdx, LateUseProxyEntry>;

struct LateUseProxyEntry {
    ref_place: MirPlace,
    can_move_from: Option<Vec<MirPlace>>,
}

impl<'tcx> MirFromThirCtx<'tcx> {
    pub fn lower_fn_arg(
        &mut self,
        span: Span,
        scope: MirScopeIdx,
        arg_pat: Obj<ThirPat>,
        arg_value: MirPlace,
    ) {
        self.lower_let_stmt_common(span, scope, arg_pat, arg_value, |this, reject_scope| {
            this.push_unreachable(reject_scope, MirSourceInfo::Todo);
        });
    }

    pub fn lower_let_stmt(&mut self, scope: MirScopeIdx, stmt: Obj<ThirLetStmt>) {
        let s = self.session();

        let ThirLetStmt {
            span: _,
            pat,
            init,
            else_clause,
        } = *stmt.r(s);

        let Some(init) = init else {
            assert!(else_clause.is_none());
            self.lower_pat_names(scope, pat);

            return;
        };

        let init = self.lower_expr_place(scope, init, None);

        self.lower_let_stmt_common(stmt.r(s).span, scope, pat, init, |this, reject_scope| {
            if let Some(else_clause) = else_clause {
                this.lower_block_flat(reject_scope, else_clause, None);
            } else {
                this.push_unreachable(reject_scope, MirSourceInfo::Todo);
            }
        });
    }

    fn lower_let_stmt_common(
        &mut self,
        span: Span,
        scope: MirScopeIdx,
        pat: Obj<ThirPat>,
        scrutinee: MirPlace,
        on_reject: impl FnOnce(&mut Self, MirScopeIdx),
    ) {
        // Constructs the following nested scopes...
        //
        // ```
        // 'break_on_accept: {
        //     'break_on_reject: {
        //         pattern match;
        //         break 'break_on_accept or 'break_on_reject;
        //     }
        //
        //     else block;  // (provided by caller)
        // }
        //
        // continuing logic;
        // ```

        self.push_scope(
            scope,
            MirSourceInfo::Todo,
            CanHoistLocals::No,
            |this, break_on_accept| {
                this.push_scope(
                    break_on_accept,
                    MirSourceInfo::Todo,
                    CanHoistLocals::No,
                    |this, break_on_reject| {
                        let mut late_use_proxies = FastHashMap::default();

                        this.lower_pat(
                            &mut late_use_proxies,
                            PatLowerScopes {
                                local_scope: scope,
                                match_logic: break_on_reject,
                                break_on_accept,
                                break_on_reject,
                            },
                            pat,
                            scrutinee,
                        );

                        this.materialize_late_use_proxies(span, break_on_reject, late_use_proxies);
                    },
                );

                on_reject(this, break_on_accept);
            },
        );
    }

    pub fn lower_match(
        &mut self,
        scope: MirScopeIdx,
        scrutinee: Obj<ThirExpr>,
        arms: Obj<[ThirMatchArm]>,
        out_place: MirPlace,
    ) {
        let s = self.session();

        self.push_scope(
            scope,
            MirSourceInfo::Todo,
            CanHoistLocals::No,
            |this, match_scope| {
                // If our scrutinee is an owned enum, we will take ownership of it here. This allows us
                // to safely invoke guards when matching on enum variants.
                let scrutinee = this.lower_expr_place(match_scope, scrutinee, None);

                for &arm in arms.r(s) {
                    let ThirMatchArm {
                        span,
                        pat,
                        guard,
                        body,
                    } = arm;

                    // Constructs the following nested scopes...
                    //
                    // ```
                    // 'match_scope: {
                    //     // Arm 1
                    //     'break_on_reject: {
                    //         hoisted locals here;
                    //         'break_on_accept: {
                    //              pattern match;
                    //              break 'break_on_accept or 'break_on_reject;
                    //         }
                    //
                    //         if !guard {
                    //             break 'break_on_reject;
                    //         }
                    //
                    //         body;
                    //         break 'match_scope;
                    //     }
                    //
                    //     // Arm 2
                    //     // ...
                    //
                    //     unreachable;
                    // }
                    // continuing logic;
                    // ```

                    let mut late_use_proxies = FastHashMap::default();

                    this.push_scope(
                        match_scope,
                        MirSourceInfo::Todo,
                        CanHoistLocals::Yes,
                        |this, break_on_reject| {
                            this.push_scope(
                                break_on_reject,
                                MirSourceInfo::Todo,
                                CanHoistLocals::No,
                                |this, break_on_accept| {
                                    this.lower_pat(
                                        &mut late_use_proxies,
                                        PatLowerScopes {
                                            local_scope: break_on_reject,
                                            match_logic: break_on_reject,
                                            break_on_accept,
                                            break_on_reject,
                                        },
                                        pat,
                                        scrutinee,
                                    );
                                },
                            );

                            if let Some(guard) = guard {
                                this.push_scope(
                                    break_on_reject,
                                    MirSourceInfo::Todo,
                                    CanHoistLocals::No,
                                    |this, guard_scope| {
                                        // TODO: introduce guard move proxies

                                        this.lower_if_expr(
                                            guard_scope,
                                            guard,
                                            |this, truthy_scope| {
                                                this.push_break(
                                                    truthy_scope,
                                                    MirSourceInfo::Todo,
                                                    guard_scope,
                                                );
                                            },
                                            Some(|this: &mut MirFromThirCtx<'tcx>, falsy_scope| {
                                                this.push_break(
                                                    falsy_scope,
                                                    MirSourceInfo::Todo,
                                                    break_on_reject,
                                                );
                                            }),
                                        );
                                    },
                                );
                            }

                            this.materialize_late_use_proxies(
                                span,
                                break_on_reject,
                                late_use_proxies,
                            );
                            this.lower_expr_place(break_on_reject, body, Some(out_place));
                            this.push_break(break_on_reject, MirSourceInfo::Todo, match_scope);
                        },
                    );
                }

                this.push_unreachable(match_scope, MirSourceInfo::Todo);
            },
        );
    }

    pub fn lower_let_expr(
        &mut self,
        break_if_falsy: MirScopeIdx,
        pat: Obj<ThirPat>,
        scrutinee: Obj<ThirExpr>,
    ) {
        let s = self.session();

        // Constructs the following nested scopes...
        //
        // ```
        // 'break_if_falsy: {
        //     previous conditions;
        //
        //     'break_if_truthy: {
        //         pattern matching
        //         break 'break_if_truthy or 'break_if_falsy;
        //     }
        //
        //     further conditions;
        // }
        // ```

        let mut late_use_proxies = FastHashMap::default();

        let scrutinee = self.lower_expr_place(break_if_falsy, scrutinee, None);
        self.push_scope(
            break_if_falsy,
            MirSourceInfo::Todo,
            CanHoistLocals::No,
            |this, break_if_truthy| {
                this.lower_pat(
                    &mut late_use_proxies,
                    PatLowerScopes {
                        local_scope: break_if_falsy,
                        match_logic: break_if_truthy,
                        break_on_accept: break_if_truthy,
                        break_on_reject: break_if_falsy,
                    },
                    pat,
                    scrutinee,
                );
            },
        );

        self.materialize_late_use_proxies(pat.r(s).span, break_if_falsy, late_use_proxies);
    }

    fn lower_pat_names(&mut self, local_scope: MirScopeIdx, pat: Obj<ThirPat>) {
        let s = self.session();

        match *pat.r(s).kind {
            ThirPatKind::Hole | ThirPatKind::Error(_) => {
                // (nothing defined)
            }
            ThirPatKind::Binding {
                by_ref: _,
                local,
                and_bind,
            } => {
                _ = self.ensure_local_defined(local_scope, local);

                if let Some(and_bind) = and_bind {
                    self.lower_pat_names(local_scope, and_bind);
                }
            }
            ThirPatKind::Deref(pat) => {
                self.lower_pat_names(local_scope, pat);
            }
            ThirPatKind::Or(choices) => {
                for &choice in choices.r(s) {
                    self.lower_pat_names(local_scope, choice);
                }
            }
            ThirPatKind::Slice(list) => {
                for elem in list.all_elems(s) {
                    self.lower_pat_names(local_scope, elem);
                }
            }
            ThirPatKind::Tuple(list) => {
                for elem in list.all_elems(s) {
                    self.lower_pat_names(local_scope, elem);
                }
            }
            ThirPatKind::Adt(_ctor, fields) => {
                for field in fields.r(s) {
                    self.lower_pat_names(local_scope, field.pat);
                }
            }
        }
    }

    fn lower_pat(
        &mut self,
        late_use_proxies: &mut LateUseProxyMap,
        scopes: PatLowerScopes,
        pat: Obj<ThirPat>,
        scrutinee: MirPlace,
    ) {
        debug_assert!(self.can_hoist_local_into(scopes.local_scope));

        let tcx = self.tcx();
        let s = self.session();

        match *pat.r(s).kind {
            ThirPatKind::Hole => {
                // (trivially accepted)
            }
            ThirPatKind::Binding {
                by_ref,
                local,
                and_bind,
            } => {
                let mir_local = self.ensure_local_defined(scopes.local_scope, local);

                match by_ref {
                    Some(muta) => {
                        self.push_assign(
                            scopes.match_logic,
                            MirSourceInfo::Todo,
                            MirPlace::new(tcx, mir_local, []),
                            MirRvalue::Ref(muta, scrutinee),
                        );
                    }
                    None => {
                        let late_use_proxy =
                            late_use_proxies.entry(mir_local).or_insert_with(|| {
                                let span = local.r(s).ty.r(s).span;

                                let ref_local = self.push_local(
                                    scopes.local_scope,
                                    MirLocal {
                                        ty: Obj::new(
                                            SigTyInner {
                                                span,
                                                kind: SigTyKind::Reference(
                                                    SigRe {
                                                        span,
                                                        kind: SigReKind::Infer,
                                                    },
                                                    Mutability::Not,
                                                    local.r(s).ty,
                                                ),
                                            },
                                            s,
                                        ),
                                    },
                                );

                                LateUseProxyEntry {
                                    ref_place: MirPlace::new(tcx, ref_local, []),
                                    can_move_from: self
                                        .trait_cache
                                        .operand_mode(local.r(s).ty)
                                        .is_copy()
                                        .then(Vec::new),
                                }
                            });

                        if let Some(can_move_from) = &mut late_use_proxy.can_move_from {
                            can_move_from.push(scrutinee);
                        }

                        self.push_assign(
                            scopes.match_logic,
                            MirSourceInfo::Todo,
                            late_use_proxy.ref_place,
                            MirRvalue::Ref(Mutability::Not, scrutinee),
                        );
                    }
                }

                if let Some(and_bind) = and_bind {
                    self.lower_pat(late_use_proxies, scopes, and_bind, scrutinee);
                }
            }
            ThirPatKind::Deref(pat) => {
                self.lower_pat(
                    late_use_proxies,
                    scopes,
                    pat,
                    scrutinee.extend(tcx, [MirPlaceElem::DerefPtr]),
                );
            }
            ThirPatKind::Or(opts) => {
                self.lower_pat_or(
                    late_use_proxies,
                    scopes,
                    opts.r(s).iter().map(|&opt_pat| (opt_pat, scrutinee)),
                );
            }
            ThirPatKind::Slice(pat_list_front_and_tail) => todo!(),
            ThirPatKind::Tuple(list) => {
                let SigTyKind::Tuple(pat_tuple_elems) = pat.r(s).ty.r(s).kind else {
                    unreachable!()
                };

                self.lower_pat_and(
                    late_use_proxies,
                    scopes,
                    list.zip(0..pat_tuple_elems.r(s).len() as u32, s)
                        .map(|(pat, idx)| {
                            (
                                pat,
                                scrutinee.extend(
                                    tcx,
                                    [MirPlaceElem::Field(ResolvedFieldIdx::Tuple {
                                        field_idx: idx,
                                        max_elems: pat_tuple_elems.r(s).len() as u32,
                                    })],
                                ),
                            )
                        }),
                );
            }
            ThirPatKind::Adt(ctor, fields) => {
                // TODO: handle enums

                self.lower_pat_and(
                    late_use_proxies,
                    scopes,
                    fields.r(s).iter().map(|field| {
                        (
                            field.pat,
                            scrutinee.extend(
                                tcx,
                                [MirPlaceElem::Field(ResolvedFieldIdx::Adt(ctor, field.idx))],
                            ),
                        )
                    }),
                );
            }
            ThirPatKind::Error(_error) => {
                // (trivial)
            }
        }
    }

    fn lower_pat_and(
        &mut self,
        late_use_proxies: &mut LateUseProxyMap,
        scopes: PatLowerScopes,
        children: impl IntoIterator<Item = (Obj<ThirPat>, MirPlace)>,
    ) {
        for (pat, scrutinee) in children {
            self.push_scope(
                scopes.match_logic,
                MirSourceInfo::Todo,
                CanHoistLocals::No,
                |this, nested_accept| {
                    this.lower_pat(
                        late_use_proxies,
                        PatLowerScopes {
                            local_scope: scopes.local_scope,
                            match_logic: nested_accept,
                            break_on_accept: nested_accept,
                            break_on_reject: scopes.break_on_reject,
                        },
                        pat,
                        scrutinee,
                    );
                },
            );
        }

        self.push_break(
            scopes.match_logic,
            MirSourceInfo::Todo,
            scopes.break_on_accept,
        );
    }

    fn lower_pat_or(
        &mut self,
        late_use_proxies: &mut LateUseProxyMap,
        scopes: PatLowerScopes,
        children: impl IntoIterator<Item = (Obj<ThirPat>, MirPlace)>,
    ) {
        for (pat, scrutinee) in children {
            self.push_scope(
                scopes.match_logic,
                MirSourceInfo::Todo,
                CanHoistLocals::No,
                |this, nested_reject| {
                    this.lower_pat(
                        late_use_proxies,
                        PatLowerScopes {
                            local_scope: scopes.local_scope,
                            match_logic: nested_reject,
                            break_on_accept: scopes.break_on_accept,
                            break_on_reject: nested_reject,
                        },
                        pat,
                        scrutinee,
                    );
                },
            );
        }

        self.push_break(
            scopes.match_logic,
            MirSourceInfo::Todo,
            scopes.break_on_reject,
        );
    }

    fn materialize_late_use_proxies(
        &mut self,
        span: Span,
        scope: MirScopeIdx,
        map: LateUseProxyMap,
    ) {
        let tcx = self.tcx();

        for (dest, proxy) in map {
            let rvalue = match proxy.can_move_from {
                Some(can_move_from) => MirRvalue::MoveOutRef {
                    can_move_from,
                    ref_place: proxy.ref_place,
                },
                None => MirRvalue::Use(MirOperand::Copy(
                    proxy.ref_place.extend(tcx, [MirPlaceElem::DerefPtr]),
                )),
            };

            self.push_assign(
                scope,
                MirSourceInfo::Simple(span),
                MirPlace::new(tcx, dest, []),
                rvalue,
            );
        }
    }

    fn ensure_local_defined(
        &mut self,
        local_scope: MirScopeIdx,
        local: Obj<ThirLocal>,
    ) -> MirLocalIdx {
        let s = self.session();

        *self.thir_locals.entry(local).or_insert_with(|| {
            MirScopedBuilderRef {
                raw_builder: &mut self.raw_builder,
                trait_cache: &mut self.trait_cache,
            }
            .push_local(local_scope, MirLocal { ty: local.r(s).ty })
        })
    }
}
