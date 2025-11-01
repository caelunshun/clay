use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag,
        arena::{LateInit, Obj},
        syntax::Span,
    },
    kw,
    parse::{
        ast::{
            AstGenericDefKind, AstGenericDefList, AstItem, AstItemKind, AstItemModuleContents,
            AstItemTrait, AstSimplePath, AstTraitClause, AstTraitClauseKind, AstTraitClauseList,
            AstTraitMemberKind, AstUsePath, AstUsePathKind, AstVisibility,
        },
        token::Ident,
    },
    typeck::{
        analysis::TyCtxt,
        lower::modules::{
            BuilderItemId, BuilderModuleId, BuilderModuleTree, EmitErrors, FrozenModuleResolver,
            ModuleResolver,
        },
        syntax::{
            AnyGeneric, AssocType, GenericBinder, Item, ItemKind, Module, RegionGeneric,
            TraitClause, TraitClauseList, TraitDef,
        },
    },
    utils::hash::FxHashMap,
};
use hashbrown::hash_map;
use index_vec::IndexVec;
use std::rc::Rc;

impl TyCtxt {
    pub fn lower_full_ast(&self, ast: &AstItemModuleContents) -> Obj<Module> {
        let s = &self.session;

        // Create the module tree
        let mut ctxt = UseLowerCtxt {
            tree: BuilderModuleTree::default(),
            item_asts: IndexVec::new(),
        };

        ctxt.lower_initial_tree(BuilderModuleId::ROOT, ast);

        let (modules, items) = ctxt.tree.freeze_and_check(&self.session);
        let root = modules[BuilderModuleId::ROOT];
        drop(modules);

        let item_ast_iter = items.iter().copied().zip(ctxt.item_asts.iter().copied());

        // Lower each item.
        let mut ctxt = ItemLowerCtxt { tcx: self, root };

        // Specialize each `Item` to have the appropriate kind.
        for (target, ast) in item_ast_iter.clone() {
            match &ast.kind {
                AstItemKind::Trait(ast) => {
                    ctxt.lower_trait_first_pass(target, ast);
                }
                AstItemKind::Mod(_) | AstItemKind::Use(_) | AstItemKind::Error(_) => {
                    unreachable!()
                }
            }
        }

        // Lower each item's specific fields.
        for (item, ast) in item_ast_iter.clone() {
            match &ast.kind {
                AstItemKind::Trait(ast) => {
                    ctxt.lower_trait_second_pass(item.r(s).kind.as_trait().unwrap(), ast);
                }
                AstItemKind::Mod(_) | AstItemKind::Use(_) | AstItemKind::Error(_) => {
                    unreachable!()
                }
            }
        }

        root
    }
}

struct UseLowerCtxt<'ast> {
    tree: BuilderModuleTree,
    item_asts: IndexVec<BuilderItemId, &'ast AstItem>,
}

impl<'ast> UseLowerCtxt<'ast> {
    fn lower_initial_tree(&mut self, parent_id: BuilderModuleId, ast: &'ast AstItemModuleContents) {
        for item in &ast.items {
            match &item.kind {
                AstItemKind::Mod(item_mod) => {
                    let item_mod_id =
                        self.tree
                            .push_module(parent_id, item.vis.clone(), item_mod.name);

                    self.lower_initial_tree(item_mod_id, item_mod.contents.as_ref().unwrap());
                }
                AstItemKind::Use(item_use) => {
                    let mut prefix = Vec::new();

                    self.lower_use(parent_id, &item.vis, &mut prefix, &item_use.path);
                }
                AstItemKind::Trait(item_trait) => {
                    self.tree
                        .push_item(parent_id, item.vis.clone(), item_trait.name);

                    self.item_asts.push(item);
                }
                AstItemKind::Error(_) => {
                    // (ignored)
                }
            }
        }
    }

    fn lower_use(
        &mut self,
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
                    self.tree.push_single_use(
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
                self.tree.push_glob_use(
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
                    self.lower_use(mod_id, visibility, prefix, child);
                }
            }
        }

        prefix.truncate(old_len);
    }
}

struct ItemLowerCtxt<'a> {
    tcx: &'a TyCtxt,
    root: Obj<Module>,
}

impl ItemLowerCtxt<'_> {
    fn lower_trait_first_pass(&mut self, target: Obj<Item>, ast: &AstItemTrait) {
        let s = &self.tcx.session;

        let regular_generic_count = ast
            .generics
            .as_ref()
            .map_or(0, |v| v.defs.iter().filter(|v| v.is_ok()).count());

        let regular_generic_count = regular_generic_count as u32;

        let mut associated_type_to_index = FxHashMap::default();
        let mut next_idx = regular_generic_count;

        for member in &ast.members {
            match &member.kind {
                AstTraitMemberKind::AssocType(name, _) => {
                    match associated_type_to_index.entry(name.text) {
                        hash_map::Entry::Vacant(entry) => {
                            entry.insert(AssocType {
                                span: name.span,
                                idx: next_idx,
                            });
                            next_idx += 1;
                        }
                        hash_map::Entry::Occupied(entry) => {
                            Diag::span_err(name.span, "name already used")
                                .child(LeafDiag::span_note(
                                    entry.get().span,
                                    "first definition here",
                                ))
                                .emit();
                        }
                    }
                }
            }
        }

        LateInit::init(
            &target.r(s).kind,
            ItemKind::Trait(Obj::new(
                TraitDef {
                    item: target,
                    generics: LateInit::uninit(),
                    regular_generic_count,
                    associated_type_to_index,
                    methods: LateInit::uninit(),
                    impls: LateInit::uninit(),
                },
                s,
            )),
        );
    }

    fn lower_trait_second_pass(&mut self, target: Obj<TraitDef>, ast: &AstItemTrait) {
        // todo!();
        // TODO
    }

    fn lower_generic_def_list(
        &mut self,
        scope: Obj<Module>,
        ast: Option<&AstGenericDefList>,
    ) -> Obj<GenericBinder> {
        let s = &self.tcx.session;

        let Some(ast) = ast else {
            return self.tcx.seal_generic_binder(GenericBinder {
                span: Span::DUMMY,
                generics: Vec::new(),
            });
        };

        let mut binder = GenericBinder {
            span: ast.span,
            generics: Vec::new(),
        };

        for def in &ast.defs {
            let Ok(def) = def else {
                continue;
            };

            match def.kind {
                AstGenericDefKind::Lifetime(lifetime) => {
                    binder.generics.push(AnyGeneric::Re(Obj::new(
                        RegionGeneric {
                            span: def.span,
                            lifetime,
                            binder: LateInit::uninit(),
                            clauses: self.lower_clauses(scope, def.clauses.as_ref()),
                        },
                        s,
                    )));
                }
                AstGenericDefKind::Type(ident) => todo!(),
            }
        }

        self.tcx.seal_generic_binder(binder)
    }

    fn lower_clauses(
        &mut self,
        scope: Obj<Module>,
        ast: Option<&AstTraitClauseList>,
    ) -> TraitClauseList {
        todo!()
    }

    fn lower_clause(
        &mut self,
        scope: Obj<Module>,
        ast: &AstTraitClause,
    ) -> Result<TraitClause, ErrorGuaranteed> {
        let s = &self.tcx.session;

        match &ast.kind {
            AstTraitClauseKind::Outlives(lt) => todo!(),
            AstTraitClauseKind::Trait(target, ast_trait_params) => {
                let target_trait = FrozenModuleResolver(&self.tcx.session)
                    .lookup(self.root, scope, scope, &target.parts, EmitErrors::Yes)
                    .map_err(Option::unwrap)?
                    .as_item()
                    .and_then(|v| v.r(s).kind.as_trait())
                    .ok_or_else(|| Diag::span_err(target.span, "must be a trait").emit())?;

                Ok(TraitClause::Trait(
                    target_trait,
                    self.tcx.intern_trait_param_list(&[]),
                ))
            }
        }
    }

    fn lower_ty(&mut self, scope: Obj<Module>) {
        todo!();
    }
}
