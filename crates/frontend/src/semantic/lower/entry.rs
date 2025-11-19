use crate::{
    base::{
        Diag, ErrorGuaranteed,
        analysis::NameResolver,
        arena::{LateInit, Obj},
    },
    kw,
    parse::{
        ast::{
            AstGenericDef, AstImplLikeMemberKind, AstItem, AstItemImpl, AstItemModuleContents,
            AstItemTrait, AstSimplePath, AstTraitClauseList, AstUsePath, AstUsePathKind,
            AstVisibility, AstVisibilityKind,
        },
        token::Ident,
    },
    semantic::{
        analysis::TyCtxt,
        lower::modules::{
            AnyDef, BuilderItemId, BuilderModuleId, BuilderModuleTree, FrozenModuleResolver,
            ModuleResolver,
        },
        syntax::{
            AnyGeneric, Crate, GenericBinder, ImplDef, Item, ItemKind, Module, RegionGeneric,
            TraitDef, TypeGeneric,
        },
    },
    symbol,
    utils::{hash::FxHashMap, mem::CellVec},
};
use index_vec::IndexVec;
use std::rc::Rc;

// === Driver === //

impl TyCtxt {
    pub fn lower_full_ast(&self, ast: &AstItemModuleContents) -> Obj<Crate> {
        let s = &self.session;

        // Build the module tree.
        let mut ctxt = UseLowerCtxt {
            tree: BuilderModuleTree::default(),
            item_asts: IndexVec::new(),
            impls: Vec::new(),
        };

        ctxt.lower_initial_tree(BuilderModuleId::ROOT, ast);

        let krate = Obj::new(
            Crate {
                name: symbol!("demo"),
                is_local: true,
                root: LateInit::uninit(),
                items: LateInit::uninit(),
                impls: LateInit::uninit(),
            },
            s,
        );
        let (modules, items) = ctxt.tree.freeze_and_check(krate, s);
        let root = modules[BuilderModuleId::ROOT];

        let UseLowerCtxt {
            tree: _,
            item_asts,
            impls,
        } = ctxt;

        // Lower inter-item properties.
        let mut tasks = Vec::new();

        for (target, ast) in items.iter().copied().zip(item_asts.iter().copied()) {
            let mut ctxt = InterItemLowerCtxt {
                tcx: self,
                item: target,
                tasks: &mut tasks,
            };

            match &ast {
                AstItem::Trait(ast) => {
                    ctxt.lower_trait(target, ast);
                }
                AstItem::Mod(_)
                | AstItem::Use(_)
                | AstItem::Impl(_)
                | AstItem::Func(_)
                | AstItem::Adt(_)
                | AstItem::Error(_, _) => {
                    unreachable!()
                }
            }
        }

        // Lower intra-item properties.
        for (scope, kind) in tasks {
            let ctxt = IntraItemLowerCtxt {
                tcx: self,
                root,
                scope,
                generic_ty_names: NameResolver::new(),
                generic_re_names: NameResolver::new(),
            };

            match kind {
                IntraLowerTask::Trait {
                    item,
                    inherits,
                    generic_clause_lists,
                } => {
                    ctxt.lower_trait(item, inherits, generic_clause_lists);
                }
            }
        }

        let impls = impls
            .into_iter()
            .map(|(scope, impl_)| {
                IntraItemLowerCtxt {
                    tcx: self,
                    root,
                    scope: modules[scope],
                    generic_ty_names: NameResolver::new(),
                    generic_re_names: NameResolver::new(),
                }
                .lower_impl(impl_)
            })
            .filter_map(Result::ok)
            .collect::<Vec<_>>();

        LateInit::init(&krate.r(s).items, items.raw);
        LateInit::init(&krate.r(s).impls, impls);

        krate
    }
}

// === First Phase === //

pub struct UseLowerCtxt<'ast> {
    tree: BuilderModuleTree,
    item_asts: IndexVec<BuilderItemId, &'ast AstItem>,
    impls: Vec<(BuilderModuleId, &'ast AstItemImpl)>,
}

impl<'ast> UseLowerCtxt<'ast> {
    pub fn lower_initial_tree(
        &mut self,
        parent_id: BuilderModuleId,
        ast: &'ast AstItemModuleContents,
    ) {
        for item_enum in &ast.items {
            match item_enum {
                AstItem::Mod(item) => {
                    let item_mod_id =
                        self.tree
                            .push_module(parent_id, item.base.vis.clone(), item.name);

                    self.lower_initial_tree(item_mod_id, item.contents.as_ref().unwrap());
                }
                AstItem::Use(item) => {
                    let mut prefix = Vec::new();

                    self.lower_use(parent_id, &item.base.vis, &mut prefix, &item.path);
                }
                AstItem::Trait(item) => {
                    self.tree
                        .push_item(parent_id, item.base.vis.clone(), item.name);

                    self.item_asts.push(item_enum);
                }
                AstItem::Impl(item) => {
                    if !item.base.vis.kind.is_omitted() {
                        Diag::span_err(
                            item.base.vis.span,
                            "`impl` blocks cannot have visibilities",
                        )
                        .emit();
                    }

                    self.impls.push((parent_id, item));
                }
                AstItem::Func(_) => {
                    todo!();
                }
                AstItem::Adt(_) => {
                    todo!();
                }
                AstItem::Error(_, _) => {
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
    tasks: &'a mut Vec<(Obj<Module>, IntraLowerTask<'ast>)>,
}

impl<'ast> InterItemLowerCtxt<'_, 'ast> {
    pub fn push_task(&mut self, kind: IntraLowerTask<'ast>) {
        self.tasks
            .push((self.item.r(&self.tcx.session).parent, kind));
    }

    pub fn lower_trait(&mut self, target: Obj<Item>, ast: &'ast AstItemTrait) {
        let s = &self.tcx.session;

        let mut binder = GenericBinder::default();

        let mut generic_clause_lists = Vec::new();

        if let Some(generics) = &ast.generics {
            for def in &generics.list {
                let Some(def_kind) = def.kind.as_generic_def() else {
                    Diag::span_err(def.span, "expected generic parameter definition").emit();
                    continue;
                };

                match def_kind {
                    AstGenericDef::Re(lifetime, clauses) => {
                        binder.defs.push(AnyGeneric::Re(Obj::new(
                            RegionGeneric {
                                span: def.span,
                                lifetime,
                                binder: LateInit::uninit(),
                                clauses: LateInit::uninit(),
                                is_synthetic: false,
                            },
                            s,
                        )));

                        generic_clause_lists.push(clauses);
                    }
                    AstGenericDef::Ty(ident, clauses) => {
                        binder.defs.push(AnyGeneric::Ty(Obj::new(
                            TypeGeneric {
                                span: def.span,
                                ident,
                                binder: LateInit::uninit(),
                                user_clauses: LateInit::uninit(),
                                elaborated_clauses: LateInit::uninit(),
                                is_synthetic: false,
                            },
                            s,
                        )));

                        generic_clause_lists.push(clauses);
                    }
                }
            }
        }

        let regular_generic_count = binder.defs.len() as u32;
        let mut associated_types = FxHashMap::default();

        for member in &ast.body.members {
            match &member.kind {
                AstImplLikeMemberKind::TypeInherits(name, clauses) => {
                    let generic = Obj::new(
                        TypeGeneric {
                            span: member.span,
                            ident: *name,
                            binder: LateInit::uninit(),
                            user_clauses: LateInit::uninit(),
                            elaborated_clauses: LateInit::uninit(),
                            is_synthetic: false,
                        },
                        s,
                    );

                    binder.defs.push(AnyGeneric::Ty(generic));
                    generic_clause_lists.push(Some(clauses));
                    associated_types.insert(name.text, generic);
                }
                AstImplLikeMemberKind::TypeEquals(..) => {
                    Diag::span_err(member.span, "default associated types are not supported")
                        .emit();
                }
                AstImplLikeMemberKind::Func(..) => {
                    todo!();
                }
                AstImplLikeMemberKind::Error(_) => {
                    // (ignored)
                }
            }
        }

        let trait_target = Obj::new(
            TraitDef {
                item: target,
                generics: self.tcx.seal_generic_binder(binder),
                inherits: LateInit::uninit(),
                regular_generic_count,
                associated_types,
                methods: LateInit::uninit(),
                impls: CellVec::default(),
            },
            s,
        );

        LateInit::init(&target.r(s).kind, ItemKind::Trait(trait_target));

        self.push_task(IntraLowerTask::Trait {
            item: trait_target,
            inherits: ast.inherits.as_ref(),
            generic_clause_lists,
        });
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

pub enum IntraLowerTask<'ast> {
    Trait {
        item: Obj<TraitDef>,
        inherits: Option<&'ast AstTraitClauseList>,
        generic_clause_lists: Vec<Option<&'ast AstTraitClauseList>>,
    },
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
        inherits: Option<&AstTraitClauseList>,
        clause_lists: Vec<Option<&AstTraitClauseList>>,
    ) {
        let s = &self.tcx.session;

        self.define_generics_in_binder(item.r(s).generics);

        for (&generic, clause_list) in item.r(s).generics.r(s).defs.iter().zip(clause_lists) {
            match generic {
                AnyGeneric::Re(generic) => {
                    LateInit::init(&generic.r(s).clauses, self.lower_clauses(clause_list));
                }
                AnyGeneric::Ty(generic) => {
                    LateInit::init(&generic.r(s).user_clauses, self.lower_clauses(clause_list));
                }
            }
        }

        LateInit::init(&item.r(s).inherits, self.lower_clauses(inherits));
    }

    pub fn lower_impl(mut self, ast: &AstItemImpl) -> Result<Obj<ImplDef>, ErrorGuaranteed> {
        let s = &self.tcx.session;

        // Lower generics
        let mut binder = GenericBinder::default();
        let mut generic_clause_lists = Vec::new();

        if let Some(generics) = &ast.generics {
            for def in &generics.list {
                let Some(def_kind) = def.kind.as_generic_def() else {
                    Diag::span_err(def.span, "expected generic parameter definition").emit();
                    continue;
                };

                match def_kind {
                    AstGenericDef::Re(lifetime, clauses) => {
                        binder.defs.push(AnyGeneric::Re(Obj::new(
                            RegionGeneric {
                                span: def.span,
                                lifetime,
                                binder: LateInit::uninit(),
                                clauses: LateInit::uninit(),
                                is_synthetic: false,
                            },
                            s,
                        )));

                        generic_clause_lists.push(clauses);
                    }
                    AstGenericDef::Ty(ident, clauses) => {
                        binder.defs.push(AnyGeneric::Ty(Obj::new(
                            TypeGeneric {
                                span: def.span,
                                ident,
                                binder: LateInit::uninit(),
                                user_clauses: LateInit::uninit(),
                                elaborated_clauses: LateInit::uninit(),
                                is_synthetic: false,
                            },
                            s,
                        )));

                        generic_clause_lists.push(clauses);
                    }
                }
            }
        }

        let binder = self.tcx.seal_generic_binder(binder);
        self.define_generics_in_binder(binder);

        // Lower clauses
        for (&generic, clause_list) in binder.r(s).defs.iter().zip(generic_clause_lists) {
            match generic {
                AnyGeneric::Re(generic) => {
                    LateInit::init(&generic.r(s).clauses, self.lower_clauses(clause_list));
                }
                AnyGeneric::Ty(generic) => {
                    LateInit::init(&generic.r(s).user_clauses, self.lower_clauses(clause_list));
                }
            }
        }

        // Lower source trait
        let impl_ = match (&ast.first_ty, &ast.second_ty) {
            (for_trait, Some(for_ty)) => {
                let for_trait = self.lower_trait_instance(for_trait, &ast.body)?;

                let for_ty = self.lower_ty(for_ty);

                let item = Obj::new(
                    ImplDef {
                        span: ast.base.span,
                        generics: binder,
                        trait_: Some(for_trait),
                        target: for_ty,
                        methods: LateInit::uninit(),
                        generic_solve_order: LateInit::uninit(),
                    },
                    s,
                );

                for_trait.value.def.r(s).impls.mutate(|v| v.push(item));

                item
            }
            (for_ty, None) => {
                todo!()
            }
        };

        // Lower methods
        // TODO

        Ok(impl_)
    }
}
