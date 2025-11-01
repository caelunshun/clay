use crate::{
    base::{Diag, arena::Obj},
    kw,
    parse::{
        ast::{
            AstItemKind, AstItemModuleContents, AstItemTrait, AstSimplePath, AstUsePath,
            AstUsePathKind, AstVisibility,
        },
        token::Ident,
    },
    typeck::{
        analysis::TyCtxt,
        lower::modules::{BuilderItemId, BuilderModuleId, BuilderModuleTree},
        syntax::{Item, Module},
    },
};
use std::rc::Rc;

enum LowerItemTask<'ast> {
    Trait(BuilderItemId, &'ast AstItemTrait),
}

impl TyCtxt {
    pub fn lower_full_ast(&self, ast: &AstItemModuleContents) -> Obj<Module> {
        // Create the module tree
        let mut tree = BuilderModuleTree::default();
        let mut tasks = Vec::new();
        self.lower_initial_tree(&mut tree, &mut tasks, BuilderModuleId::ROOT, ast);

        let (modules, items) = tree.freeze_and_check(&self.session);
        let root = modules[BuilderModuleId::ROOT];

        // Lower each item.
        for task in tasks {
            match task {
                LowerItemTask::Trait(target, ast) => {
                    self.lower_trait(root, items[target], ast);
                }
            }
        }

        root
    }

    fn lower_initial_tree<'ast>(
        &self,
        tree: &mut BuilderModuleTree,
        tasks: &mut Vec<LowerItemTask<'ast>>,
        parent_id: BuilderModuleId,
        ast: &'ast AstItemModuleContents,
    ) {
        for item in &ast.items {
            match &item.kind {
                AstItemKind::Mod(item_mod) => {
                    let item_mod_id = tree.push_module(parent_id, item.vis.clone(), item_mod.name);

                    self.lower_initial_tree(
                        tree,
                        tasks,
                        item_mod_id,
                        item_mod.contents.as_ref().unwrap(),
                    );
                }
                AstItemKind::Use(item_use) => {
                    let mut prefix = Vec::new();

                    self.lower_use(tree, parent_id, &item.vis, &mut prefix, &item_use.path);
                }
                AstItemKind::Trait(item_trait) => {
                    let item = tree.push_item(parent_id, item.vis.clone(), item_trait.name);
                    tasks.push(LowerItemTask::Trait(item, item_trait));
                }
                AstItemKind::Error(_) => {
                    // (ignored)
                }
            }
        }
    }

    fn lower_use(
        &self,
        tree: &mut BuilderModuleTree,
        mod_id: BuilderModuleId,
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
                    self.lower_use(tree, mod_id, visibility, prefix, child);
                }
            }
        }

        prefix.truncate(old_len);
    }

    fn lower_trait(&self, root: Obj<Module>, target: Obj<Item>, ast: &AstItemTrait) {
        todo!()
    }
}
