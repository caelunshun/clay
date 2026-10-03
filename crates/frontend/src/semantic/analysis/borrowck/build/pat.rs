use crate::{
    base::{arena::Obj, syntax::Span},
    semantic::{
        analysis::borrowck::build::{driver::MirFromThirCtx, scope::MirBuilderScopeIdx},
        syntax::{
            MirAssignRvalue, MirLocalIdx, MirOperand, MirPlace, MirPlaceElem, MirStmt, MirStmtKind,
            MirStmtSourceInfo, Mutability, SigRe, SigReKind, SigTyInner, SigTyKind, ThirLetStmt,
            ThirLocal, ThirPat, ThirPatKind,
        },
    },
    utils::hash::FxHashMap,
};

#[derive(Debug, Copy, Clone)]
struct PatLowerScopes {
    pub local_scope: MirBuilderScopeIdx,
    pub match_logic: MirBuilderScopeIdx,
    pub break_on_accept: MirBuilderScopeIdx,
    pub break_on_reject: MirBuilderScopeIdx,
}

type LateUseProxyMap = FxHashMap<MirLocalIdx, LateUseProxyEntry>;

struct LateUseProxyEntry {
    ref_place: MirPlace,
    can_move_from: Option<Vec<MirPlace>>,
}

impl PatLowerScopes {
    #[must_use]
    pub fn nest_accept(self, scope: MirBuilderScopeIdx) -> Self {
        Self {
            match_logic: scope,
            break_on_accept: scope,
            ..self
        }
    }

    #[must_use]
    pub fn nest_reject(self, scope: MirBuilderScopeIdx) -> Self {
        Self {
            match_logic: scope,
            break_on_reject: scope,
            ..self
        }
    }
}

impl<'tcx> MirFromThirCtx<'tcx> {
    pub fn lower_let(&mut self, scope: MirBuilderScopeIdx, stmt: Obj<ThirLetStmt>) {
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

        // Constructs the following nested scopes...
        //
        // ```
        // 'break_on_accept: {
        //     'break_on_reject: {
        //         pattern match;
        //     }
        //     else block;
        // }
        // continuing logic;
        // ```

        let break_on_accept = self.builder.push_scope(scope);
        let break_on_reject = self.builder.push_scope(break_on_accept);

        let mut late_use_proxies = FxHashMap::default();

        self.lower_pat(
            &mut late_use_proxies,
            PatLowerScopes {
                local_scope: scope,
                match_logic: break_on_reject,
                break_on_accept,
                break_on_reject,
            },
            pat,
            init,
        );

        self.materialize_late_use_proxies(stmt.r(s).span, scope, late_use_proxies);

        if let Some(else_clause) = else_clause {
            self.lower_block(break_on_accept, else_clause, None);
        }

        self.builder.push_unreachable(break_on_accept);
    }

    fn lower_pat_names(&mut self, local_scope: MirBuilderScopeIdx, pat: Obj<ThirPat>) {
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

                let init_stmt = MirStmt {
                    span: MirStmtSourceInfo::Simple(pat.r(s).span),
                    kind: match by_ref {
                        Some(muta) => MirStmtKind::Assign(Box::new((
                            MirPlace::new(tcx, mir_local, []),
                            MirAssignRvalue::Ref(muta, scrutinee),
                        ))),
                        None => {
                            let late_use_proxy =
                                late_use_proxies.entry(mir_local).or_insert_with(|| {
                                    let span = local.r(s).ty.r(s).span;

                                    let ref_local = self.builder.push_local(
                                        scopes.local_scope,
                                        Obj::new(
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
                                    );

                                    LateUseProxyEntry {
                                        ref_place: MirPlace::new(tcx, ref_local, []),
                                        can_move_from: self
                                            .builder
                                            .operand_mode(local.r(s).ty)
                                            .is_copy()
                                            .then(Vec::new),
                                    }
                                });

                            if let Some(can_move_from) = &mut late_use_proxy.can_move_from {
                                can_move_from.push(scrutinee);
                            }

                            MirStmtKind::Assign(Box::new((
                                late_use_proxy.ref_place,
                                MirAssignRvalue::Ref(Mutability::Not, scrutinee),
                            )))
                        }
                    },
                };

                self.builder.push_statement(scopes.match_logic, init_stmt);

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
            ThirPatKind::Or(obj) => todo!(),
            ThirPatKind::Slice(pat_list_front_and_tail) => todo!(),
            ThirPatKind::Tuple(pat_list_front_and_tail) => todo!(),
            ThirPatKind::Adt(obj, obj1) => {
                // TODO: ensure enum ADTs are locked during matching.
                todo!()
            }
            ThirPatKind::Error(_error) => {
                // (trivial)
            }
        }
    }

    fn materialize_late_use_proxies(
        &mut self,
        span: Span,
        scope: MirBuilderScopeIdx,
        map: LateUseProxyMap,
    ) {
        let tcx = self.tcx();

        for (dest, proxy) in map {
            let rvalue = match proxy.can_move_from {
                Some(can_move_from) => MirAssignRvalue::MoveOutRef {
                    can_move_from,
                    ref_place: proxy.ref_place,
                },
                None => MirAssignRvalue::Use(MirOperand::Copy(
                    proxy.ref_place.extend(tcx, [MirPlaceElem::DerefPtr]),
                )),
            };

            self.builder.push_statement(
                scope,
                MirStmt {
                    span: MirStmtSourceInfo::Simple(span),
                    kind: MirStmtKind::Assign(Box::new((MirPlace::new(tcx, dest, []), rvalue))),
                },
            );
        }
    }

    fn ensure_local_defined(
        &mut self,
        local_scope: MirBuilderScopeIdx,
        local: Obj<ThirLocal>,
    ) -> MirLocalIdx {
        let s = self.session();

        *self
            .thir_locals
            .entry(local)
            .or_insert_with(|| self.builder.push_local(local_scope, local.r(s).ty))
    }
}
