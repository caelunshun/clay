use crate::{
    base::{Diag, Session},
    kw,
    parse::{
        ast::{
            AstItemKind, AstItemModuleContents, AstSimplePath, AstUsePath, AstUsePathKind,
            AstVisibility,
        },
        lower::modules::{ModuleId, ModuleTree},
        token::Ident,
    },
};
use std::rc::Rc;

pub fn lower_full_ast(ast: &AstItemModuleContents, s: &Session) {
    let mut tree = ModuleTree::<()>::default();

    lower_initial_tree(&mut tree, ModuleId::ROOT, ast);

    tree.freeze_and_check();
}

fn lower_initial_tree(tree: &mut ModuleTree<()>, mod_id: ModuleId, ast: &AstItemModuleContents) {
    for item in &ast.items {
        match &item.kind {
            AstItemKind::Mod(item_mod) => {
                let item_mod_id = tree.push_module(mod_id, item.vis.clone(), item_mod.name);

                lower_initial_tree(tree, item_mod_id, item_mod.contents.as_ref().unwrap());
            }
            AstItemKind::Use(item_use) => {
                let mut prefix = Vec::new();

                lower_use(tree, mod_id, &item.vis, &mut prefix, &item_use.path);
            }
            AstItemKind::Trait(_) => todo!(),
            AstItemKind::Error(_) => {
                // (ignored)
            }
        }
    }
}

fn lower_use(
    tree: &mut ModuleTree<()>,
    mod_id: ModuleId,
    visibility: &AstVisibility,
    prefix: &mut Vec<Ident>,
    ast: &AstUsePath,
) {
    let old_len = prefix.len();
    prefix.extend_from_slice(&ast.base);

    match &ast.kind {
        AstUsePathKind::Direct(rename) => {
            let name = rename.unwrap_or(prefix.last().copied().unwrap());

            if name.matches_kw(kw!("self"))
                || name.matches_kw(kw!("crate"))
                || name.matches_kw(kw!("super"))
            {
                _ = Diag::span_err(name.span, "invalid name for import").emit();
            } else {
                tree.push_single_use(
                    mod_id,
                    visibility.clone(),
                    name,
                    AstSimplePath {
                        span: ast.span,
                        parts: Rc::from(prefix.as_slice()),
                    },
                );
            }
        }
        AstUsePathKind::Wild(span) => {
            tree.push_glob_use(
                mod_id,
                visibility.clone(),
                AstSimplePath {
                    span: *span,
                    parts: Rc::from(prefix.as_slice()),
                },
            );
        }
        AstUsePathKind::Tree(children) => {
            for child in children.iter() {
                lower_use(tree, mod_id, visibility, prefix, child);
            }
        }
    }

    prefix.truncate(old_len);
}
