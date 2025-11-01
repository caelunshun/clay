use crate::{
    base::{Diag, ErrorGuaranteed, arena::Obj},
    parse::ast::{
        AstTraitClause, AstTraitClauseKind, AstTraitClauseList, AstTraitParamKind, AstTraitSpec,
        AstTy,
    },
    typeck::{
        lower::entry::IntraItemLowerCtxt,
        syntax::{TraitClause, TraitClauseList, TraitParam, TraitSpec, Ty},
    },
};

impl IntraItemLowerCtxt<'_> {
    fn lower_clauses(&mut self, ast: Option<&AstTraitClauseList>) -> TraitClauseList {
        todo!()
    }

    fn lower_clause(&mut self, ast: &AstTraitClause) -> Result<TraitClause, ErrorGuaranteed> {
        match &ast.kind {
            AstTraitClauseKind::Outlives(lt) => todo!(),
            AstTraitClauseKind::Trait(spec) => Ok(TraitClause::Trait(self.lower_trait_spec(spec)?)),
        }
    }

    fn lower_trait_spec(&mut self, ast: &AstTraitSpec) -> Result<TraitSpec, ErrorGuaranteed> {
        let s = &self.tcx.session;

        let def = self
            .lookup(&ast.path)?
            .as_item()
            .and_then(|v| v.r(s).kind.as_trait())
            .ok_or_else(|| Diag::span_err(ast.path.span, "must be a trait").emit())?;

        let mut params = (0..def.r(s).generics.r(s).generics.len())
            .map(|_| TraitParam::Unspecified(self.tcx.intern_trait_clause_list(&[])))
            .collect::<Vec<_>>();

        for param in &ast.params {
            match &param.kind {
                AstTraitParamKind::PositionalEquals(ast_ty_or_re) => todo!(),
                AstTraitParamKind::NamedEquals(ident, ast_ty_or_re) => todo!(),
                AstTraitParamKind::Unspecified(ident, ast_trait_clause_list) => {
                    todo!()
                }
            }
        }

        Ok(TraitSpec {
            def,
            params: self.tcx.intern_trait_param_list(&params),
        })
    }

    fn lower_ty(&mut self, ast: &AstTy) -> Obj<Ty> {
        todo!();
    }
}
