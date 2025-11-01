use crate::{
    base::{Diag, ErrorGuaranteed},
    parse::{
        ast::{
            AstTraitClause, AstTraitClauseList, AstTraitParamKind, AstTraitSpec, AstTy, AstTyOrRe,
        },
        token::Lifetime,
    },
    typeck::{
        lower::entry::IntraItemLowerCtxt,
        syntax::{Re, TraitClause, TraitClauseList, TraitParam, TraitSpec, Ty, TyOrRe},
    },
};

impl IntraItemLowerCtxt<'_> {
    fn lower_clauses(&mut self, ast: Option<&AstTraitClauseList>) -> TraitClauseList {
        let Some(ast) = ast else {
            return self.tcx.intern_trait_clause_list(&[]);
        };

        let mut clauses = Vec::new();

        for ast in &ast.clauses {
            let Ok(ast) = ast else {
                continue;
            };

            let Ok(clause) = self.lower_clause(ast) else {
                continue;
            };

            clauses.push(clause);
        }

        self.tcx.intern_trait_clause_list(&clauses)
    }

    fn lower_clause(&mut self, ast: &AstTraitClause) -> Result<TraitClause, ErrorGuaranteed> {
        match ast {
            AstTraitClause::Outlives(lt) => Ok(TraitClause::Outlives(self.lower_re(lt))),
            AstTraitClause::Trait(spec) => Ok(TraitClause::Trait(self.lower_trait_spec(spec)?)),
        }
    }

    fn lower_trait_spec(&mut self, ast: &AstTraitSpec) -> Result<TraitSpec, ErrorGuaranteed> {
        let s = &self.tcx.session;

        let def = self
            .lookup(&ast.path)?
            .as_item()
            .and_then(|v| v.r(s).kind.as_trait())
            .ok_or_else(|| Diag::span_err(ast.path.span, "expected a trait").emit())?;

        let mut params = Vec::new();
        let mut reader = ast.params.iter();

        // Lower positional arguments
        if reader.len() < def.r(s).regular_generic_count as usize {
            return Err(Diag::span_err(ast.span, "missing generic parameters").emit());
        }

        for param in (&mut reader).take(def.r(s).regular_generic_count as usize) {
            match &param.kind {
                AstTraitParamKind::PositionalEquals(ty_or_re) => {
                    params.push(TraitParam::Equals(self.lower_ty_or_re(ty_or_re)));
                }
                AstTraitParamKind::NamedEquals(..) | AstTraitParamKind::NamedUnspecified(..) => {
                    return Err(Diag::span_err(ast.span, "missing generic parameters").emit());
                }
            }
        }

        // Lower trait clauses
        params.resize_with(def.r(s).generics.r(s).generics.len(), || {
            TraitParam::Unspecified(self.tcx.intern_trait_clause_list(&[]))
        });

        for param in &mut reader {
            let name = match &param.kind {
                AstTraitParamKind::NamedEquals(name, _) => name,
                AstTraitParamKind::NamedUnspecified(name, _) => name,
                AstTraitParamKind::PositionalEquals(..) => {
                    return Err(Diag::span_err(param.span, "too many generic parameters").emit());
                }
            };

            let Some(generic) = def.r(s).associated_types.get(&name.text) else {
                return Err(Diag::span_err(
                    name.span,
                    "trait does not have associated type with that name",
                )
                .emit());
            };

            let idx = generic.r(s).binder.idx as usize;

            match params[idx] {
                TraitParam::Unspecified(list) if list.r(s).is_empty() => {
                    // (fallthrough)
                }
                _ => {
                    return Err(Diag::span_err(
                        param.span,
                        "associated type mentioned more than once",
                    )
                    .emit());
                }
            }

            params[idx] = match &param.kind {
                AstTraitParamKind::NamedEquals(_, ast) => {
                    TraitParam::Equals(self.lower_ty_or_re(ast))
                }
                AstTraitParamKind::NamedUnspecified(_, ast) => {
                    TraitParam::Unspecified(self.lower_clauses(Some(ast)))
                }
                AstTraitParamKind::PositionalEquals(..) => unreachable!(),
            };
        }

        Ok(TraitSpec {
            def,
            params: self.tcx.intern_trait_param_list(&params),
        })
    }

    fn lower_ty_or_re(&mut self, ast: &AstTyOrRe) -> TyOrRe {
        match ast {
            AstTyOrRe::Re(ast) => TyOrRe::Re(self.lower_re(ast)),
            AstTyOrRe::Ty(ast) => TyOrRe::Ty(self.lower_ty(ast)),
        }
    }

    fn lower_re(&mut self, ast: &Lifetime) -> Re {
        todo!();
    }

    fn lower_ty(&mut self, ast: &AstTy) -> Ty {
        todo!();
    }
}
