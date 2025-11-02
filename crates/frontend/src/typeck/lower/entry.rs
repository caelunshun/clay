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
            AstGenericDef, AstItem, AstItemKind, AstItemModuleContents, AstItemTrait,
            AstSimplePath, AstTraitClauseList, AstTraitMemberKind, AstUsePath, AstUsePathKind,
            AstVisibility,
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

// === Driver === //

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

        // Lower inter-item properties.
        let mut tasks = Vec::new();

        for (target, ast) in items.iter().copied().zip(ctxt.item_asts.iter().copied()) {
            let mut ctxt = InterItemLowerCtxt {
                tcx: self,
                item: target,
                tasks: &mut tasks,
            };

            match &ast.kind {
                AstItemKind::Trait(ast) => {
                    ctxt.lower_trait(target, ast);
                }
                AstItemKind::Mod(_) | AstItemKind::Use(_) | AstItemKind::Error(_) => {
                    unreachable!()
                }
            }
        }

        // Lower intra-item properties.
        for (item, task) in tasks {
            let ctxt = IntraItemLowerCtxt {
                tcx: self,
                root,
                scope: item.r(s).parent,
                generic_ty_names: NameResolver::new(),
                generic_re_names: NameResolver::new(),
            };

            match task {
                IntraLowerTask::Trait(clause_lists) => {
                    ctxt.lower_trait(item.r(s).kind.as_trait().unwrap(), clause_lists);
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

pub struct InterItemLowerCtxt<'a, 'ast> {
    tcx: &'a TyCtxt,
    item: Obj<Item>,
    tasks: &'a mut Vec<(Obj<Item>, IntraLowerTask<'ast>)>,
}

pub enum IntraLowerTask<'ast> {
    Trait(Vec<Option<&'ast AstTraitClauseList>>),
}

impl<'ast> InterItemLowerCtxt<'_, 'ast> {
    pub fn push_task(&mut self, task: IntraLowerTask<'ast>) {
        self.tasks.push((self.item, task));
    }

    pub fn lower_trait(&mut self, target: Obj<Item>, ast: &'ast AstItemTrait) {
        let s = &self.tcx.session;

        let mut binder = GenericBinder {
            span: Span::DUMMY,
            generics: Vec::new(),
        };

        let mut generic_clause_lists = Vec::new();

        if let Some(generics) = &ast.generics {
            for def in &generics.list {
                let Some(def_kind) = def.kind.as_generic_def() else {
                    Diag::span_err(def.span, "expected generic parameter definition").emit();
                    continue;
                };

                match def_kind {
                    AstGenericDef::Re(lifetime, clauses) => {
                        binder.generics.push(AnyGeneric::Re(Obj::new(
                            RegionGeneric {
                                span: def.span,
                                lifetime,
                                binder: LateInit::uninit(),
                                clauses: LateInit::uninit(),
                            },
                            s,
                        )));

                        generic_clause_lists.push(clauses);
                    }
                    AstGenericDef::Ty(ident, clauses) => {
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

                        generic_clause_lists.push(clauses);
                    }
                }
            }
        }

        let regular_generic_count = binder.generics.len() as u32;
        let mut associated_types = FxHashMap::default();

        for member in &ast.members {
            match &member.kind {
                AstTraitMemberKind::AssocType(name, clauses) => {
                    match associated_types.entry(name.text) {
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

                            generic_clause_lists.push(Some(clauses));
                        }
                        hash_map::Entry::Occupied(entry) => {
                            Diag::span_err(name.span, "name already used")
                                .child(LeafDiag::span_note(
                                    entry.get().r(s).ident.span,
                                    "first definition here",
                                ))
                                .emit();
                        }
                    }
                }
            }
        }

        let trait_target = Obj::new(
            TraitDef {
                item: target,
                generics: self.tcx.seal_generic_binder(binder),
                regular_generic_count,
                associated_types,
                methods: LateInit::uninit(),
                impls: LateInit::uninit(),
            },
            s,
        );

        LateInit::init(&target.r(s).kind, ItemKind::Trait(trait_target));

        self.push_task(IntraLowerTask::Trait(generic_clause_lists));
    }
}

// === Third Phase === //

pub struct IntraItemLowerCtxt<'a> {
    pub tcx: &'a TyCtxt,
    pub root: Obj<Module>,
    pub scope: Obj<Module>,
    pub generic_ty_names: NameResolver<Obj<TypeGeneric>>,
    pub generic_re_names: NameResolver<Obj<RegionGeneric>>,
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

    pub fn scoped<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.generic_ty_names.push_rib();
        self.generic_re_names.push_rib();
        let ret = f(self);
        self.generic_ty_names.pop_rib();
        self.generic_re_names.pop_rib();

        ret
    }

    pub fn lower_trait(
        mut self,
        item: Obj<TraitDef>,
        clause_lists: Vec<Option<&AstTraitClauseList>>,
    ) {
        let s = &self.tcx.session;

        self.define_generics_in_binder(item.r(s).generics);

        for (&generic, clause_list) in item.r(s).generics.r(s).generics.iter().zip(clause_lists) {
            match generic {
                AnyGeneric::Re(generic) => {
                    LateInit::init(&generic.r(s).clauses, self.lower_clauses(clause_list));
                }
                AnyGeneric::Ty(generic) => {
                    LateInit::init(&generic.r(s).user_clauses, self.lower_clauses(clause_list));
                }
            }
        }
    }
}
