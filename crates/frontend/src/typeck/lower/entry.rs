use crate::{
    base::{
        Diag, ErrorGuaranteed, LeafDiag,
        analysis::NameResolver,
        arena::{LateInit, Obj},
        syntax::Span,
    },
    kw,
    parse::{
        ast::{
            AstGenericDefKind, AstItem, AstItemKind, AstItemModuleContents, AstItemTrait,
            AstSimplePath, AstTraitMemberKind, AstUsePath, AstUsePathKind, AstVisibility,
        },
        token::Ident,
    },
    typeck::{
        analysis::TyCtxt,
        lower::modules::{
            AnyDef, BuilderItemId, BuilderModuleId, BuilderModuleTree, FrozenModuleResolver,
            ModuleResolver,
        },
        syntax::{
            AnyGeneric, GenericBinder, Item, ItemKind, Module, RegionGeneric, TraitDef, TypeGeneric,
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

        // Build the module tree.
        let mut ctxt = UseLowerCtxt {
            tree: BuilderModuleTree::default(),
            item_asts: IndexVec::new(),
        };

        ctxt.lower_initial_tree(BuilderModuleId::ROOT, ast);

        let (modules, items) = ctxt.tree.freeze_and_check(&self.session);
        let root = modules[BuilderModuleId::ROOT];
        drop(modules);

        let item_ast_iter = items.iter().copied().zip(ctxt.item_asts.iter().copied());

        // Lower inter-item properties.
        for (target, ast) in item_ast_iter.clone() {
            match &ast.kind {
                AstItemKind::Trait(ast) => {
                    inter_item_lower_trait(self, target, ast);
                }
                AstItemKind::Mod(_) | AstItemKind::Use(_) | AstItemKind::Error(_) => {
                    unreachable!()
                }
            }
        }

        // Lower intra-item properties.
        for (item, ast) in item_ast_iter.clone() {
            let mut ctxt = IntraItemLowerCtxt {
                tcx: self,
                root,
                scope: item.r(s).parent,
                names: NameResolver::new(),
            };

            match &ast.kind {
                AstItemKind::Trait(ast) => {
                    ctxt.lower_trait(item.r(s).kind.as_trait().unwrap(), ast);
                }
                AstItemKind::Mod(_) | AstItemKind::Use(_) | AstItemKind::Error(_) => {
                    unreachable!()
                }
            }
        }

        root
    }
}

// === First Phase === //

pub struct UseLowerCtxt<'ast> {
    tree: BuilderModuleTree,
    item_asts: IndexVec<BuilderItemId, &'ast AstItem>,
}

impl<'ast> UseLowerCtxt<'ast> {
    pub fn lower_initial_tree(
        &mut self,
        parent_id: BuilderModuleId,
        ast: &'ast AstItemModuleContents,
    ) {
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

    pub fn lower_use(
        &mut self,
        mod_id: BuilderModuleId,
        visibility: &AstVisibility,
        prefix: &mut Vec<Ident>,
        ast: &AstUsePath,
    ) {
        let old_len = prefix.len();
        prefix.extend_from_slice(&ast.base);

        match &ast.kind {
            AstUsePathKind::Direct(rename) => 'direct: {
                let mut name = rename.unwrap_or(prefix.last().copied().unwrap());

                if name.matches_kw(kw!("crate")) {
                    Diag::span_err(name.span, "crate root imports need to be explicitly named")
                        .emit();

                    break 'direct;
                }

                if name.matches_kw(kw!("super")) {
                    Diag::span_err(name.span, "invalid name for import").emit();

                    break 'direct;
                }

                if name.matches_kw(kw!("self")) {
                    let Some(new_name) =
                        prefix[..prefix.len() - 1].last().copied().filter(|name| {
                            !name.matches_kw(kw!("self"))
                                && !name.matches_kw(kw!("crate"))
                                && !name.matches_kw(kw!("super"))
                        })
                    else {
                        Diag::span_err(
                            name.span,
                            "`self` imports are only allowed after an identifier",
                        )
                        .emit();

                        break 'direct;
                    };

                    name = Ident {
                        span: name.span,
                        text: new_name.text,
                        raw: new_name.raw,
                    };
                }

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

// === Second Phase === //

pub fn inter_item_lower_trait(tcx: &TyCtxt, target: Obj<Item>, ast: &AstItemTrait) {
    let s = &tcx.session;

    let mut binder = GenericBinder {
        span: Span::DUMMY,
        generics: Vec::new(),
    };

    if let Some(generics) = &ast.generics {
        for def in &generics.defs {
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
                            clauses: LateInit::uninit(),
                        },
                        s,
                    )));
                }
                AstGenericDefKind::Type(ident) => {
                    binder.generics.push(AnyGeneric::Ty(Obj::new(
                        TypeGeneric {
                            span: def.span,
                            ident,
                            binder: LateInit::uninit(),
                            user_clauses: LateInit::uninit(),
                            instantiated_clauses: LateInit::uninit(),
                            is_synthetic: false,
                        },
                        s,
                    )));
                }
            }
        }
    }

    let regular_generic_count = binder.generics.len() as u32;
    let mut associated_types = FxHashMap::default();

    for member in &ast.members {
        match &member.kind {
            AstTraitMemberKind::AssocType(name, _) => match associated_types.entry(name.text) {
                hash_map::Entry::Vacant(entry) => {
                    entry.insert(Obj::new(
                        TypeGeneric {
                            span: member.span,
                            ident: *name,
                            binder: LateInit::uninit(),
                            user_clauses: LateInit::uninit(),
                            instantiated_clauses: LateInit::uninit(),
                            is_synthetic: false,
                        },
                        s,
                    ));
                }
                hash_map::Entry::Occupied(entry) => {
                    Diag::span_err(name.span, "name already used")
                        .child(LeafDiag::span_note(
                            entry.get().r(s).ident.span,
                            "first definition here",
                        ))
                        .emit();
                }
            },
        }
    }

    LateInit::init(
        &target.r(s).kind,
        ItemKind::Trait(Obj::new(
            TraitDef {
                item: target,
                generics: tcx.seal_generic_binder(binder),
                regular_generic_count,
                associated_types,
                methods: LateInit::uninit(),
                impls: LateInit::uninit(),
            },
            s,
        )),
    );
}

// === Third Phase === //

pub struct IntraItemLowerCtxt<'a> {
    pub tcx: &'a TyCtxt,
    pub root: Obj<Module>,
    pub scope: Obj<Module>,
    pub names: NameResolver<BoundName>,
}

#[derive(Debug, Copy, Clone)]
pub enum BoundName {
    Generic(AnyGeneric),
}

impl IntraItemLowerCtxt<'_> {
    pub fn lookup(
        &self,
        path: &AstSimplePath,
    ) -> Result<AnyDef<Obj<Module>, Obj<Item>>, ErrorGuaranteed> {
        FrozenModuleResolver(&self.tcx.session).lookup_noisy(self.root, self.scope, &path.parts)
    }

    pub fn lower_trait(&mut self, target: Obj<TraitDef>, ast: &AstItemTrait) {
        // Reveal all names.
        // TODO
    }
}
