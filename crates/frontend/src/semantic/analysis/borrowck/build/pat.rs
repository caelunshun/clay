use crate::{
    base::arena::Obj,
    semantic::{
        analysis::borrowck::build::{driver::MirFromThirCtx, scope::MirBuilderScopeIdx},
        syntax::{
            MirAssignRvalue, MirPlace, MirPlaceElem, MirStmt, MirStmtKind, MirStmtSourceInfo,
            ThirPat, ThirPatKind,
        },
    },
};

#[derive(Debug, Copy, Clone)]
pub struct PatLowerScopes {
    pub define_locals: MirBuilderScopeIdx,
    pub exec: MirBuilderScopeIdx,
    pub break_on_accept: MirBuilderScopeIdx,
    pub break_on_reject: MirBuilderScopeIdx,
}

impl PatLowerScopes {
    #[must_use]
    pub fn nest_accept(self, scope: MirBuilderScopeIdx) -> Self {
        Self {
            exec: scope,
            break_on_accept: scope,
            ..self
        }
    }

    #[must_use]
    pub fn nest_reject(self, scope: MirBuilderScopeIdx) -> Self {
        Self {
            exec: scope,
            break_on_reject: scope,
            ..self
        }
    }
}

impl<'tcx> MirFromThirCtx<'tcx> {
    pub fn lower_pat(&mut self, scopes: PatLowerScopes, pat: Obj<ThirPat>, scrutinee: MirPlace) {
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
                let mir_local = self.builder.push_local(scopes.define_locals, local.r(s).ty);

                self.thir_locals.insert(local, mir_local);

                let stmt = MirStmt {
                    span: MirStmtSourceInfo::Simple(pat.r(s).span),
                    kind: MirStmtKind::Assign(Box::new((
                        MirPlace::new(tcx, mir_local, []),
                        match by_ref {
                            Some(muta) => MirAssignRvalue::Ref(muta, scrutinee),
                            None => {
                                MirAssignRvalue::Use(self.builder.copy_or_move_operand(scrutinee))
                            }
                        },
                    ))),
                };

                self.builder.push_statement(scopes.exec, stmt);

                if let Some(and_bind) = and_bind {
                    self.lower_pat(scopes, and_bind, scrutinee);
                }
            }
            ThirPatKind::Deref(pat) => {
                self.lower_pat(scopes, pat, scrutinee.extend(tcx, [MirPlaceElem::DerefPtr]));
            }
            ThirPatKind::Or(obj) => todo!(),
            ThirPatKind::Slice(pat_list_front_and_tail) => todo!(),
            ThirPatKind::Tuple(pat_list_front_and_tail) => todo!(),
            ThirPatKind::Adt(obj, obj1) => todo!(),
            ThirPatKind::Error(_error) => {
                // (trivial)
            }
        }
    }
}
