use crate::{
    base::{
        ErrorGuaranteed,
        arena::{LateInit, Obj},
        syntax::Matcher as _,
    },
    parse::{
        ast::{
            AstAttribute,
            utils::{match_eos, match_str_lit},
        },
        token::TokenParser,
    },
    semantic::{
        lower::{
            entry::IntraItemLowerCtxt,
            modules::{FrozenModuleResolver, PathResolver},
        },
        syntax::{Attribute, AttributeKind, EarlyAttrLang, Item},
    },
    symbol,
};

impl IntraItemLowerCtxt<'_> {
    pub fn lower_item_attributes<'ast>(
        &mut self,
        item: Obj<Item>,
        attrs: impl IntoIterator<Item = &'ast AstAttribute>,
    ) {
        let s = &self.tcx.session;

        let attrs = attrs
            .into_iter()
            .map(|ast| self.lower_attribute(ast))
            .filter_map(Result::ok)
            .collect::<Vec<_>>();

        LateInit::init(&item.r(s).attrs, attrs);
    }

    pub fn lower_attribute(
        &mut self,
        ast: &AstAttribute,
    ) -> Result<Obj<Attribute>, ErrorGuaranteed> {
        let s = &self.tcx.session;

        let mut resolver = FrozenModuleResolver(&self.tcx.session);

        let err = match resolver.try_resolve_bare_path(self.root, self.scope, &ast.path) {
            Ok(item) => {
                todo!()
            }
            Err(err) => err,
        };

        match self.lower_early_attribute(ast) {
            Ok(Some(kind)) => Ok(Obj::new(
                Attribute {
                    span: ast.span,
                    kind,
                },
                s,
            )),
            Ok(None) => Err(err.emit(&resolver)),
            Err(err) => Err(err),
        }
    }

    fn lower_early_attribute(
        &mut self,
        attr: &AstAttribute,
    ) -> Result<Option<AttributeKind>, ErrorGuaranteed> {
        if attr.path.as_symbol() == Some(symbol!("lang")) {
            return self
                .lower_early_attribute_lang(attr)
                .map(AttributeKind::Lang)
                .map(Some);
        }

        Ok(None)
    }

    fn lower_early_attribute_lang(
        &mut self,
        attr: &AstAttribute,
    ) -> Result<EarlyAttrLang, ErrorGuaranteed> {
        let mut p = TokenParser::new(&attr.params);
        let p = &mut p;

        let Some(id) = match_str_lit().expect(p) else {
            return Err(p.stuck().error());
        };

        if !match_eos(p) {
            p.stuck().ignore_not_in_loop();
        }

        Ok(EarlyAttrLang { name: id.value })
    }
}
