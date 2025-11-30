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
            AstFnDef, AstGenericDef, AstImplLikeMemberKind, AstItem, AstItemEnum, AstItemFn,
            AstItemImpl, AstItemModuleContents, AstItemStruct, AstItemTrait, AstReturnTy,
            AstSimplePath, AstStructKind, AstTraitClauseList, AstTy, AstUsePath, AstUsePathKind,
            AstVisibility,
        },
        token::{Ident, Lifetime},
    },
    semantic::{
        analysis::TyCtxt,
        lower::modules::{
            AnyDef, BuilderItemId, BuilderModuleId, BuilderModuleTree, FrozenModuleResolver,
            ModuleResolver,
        },
        syntax::{
            AdtDef, AdtEnumVariant, AdtKind, AdtKindEnum, AdtKindStruct, AdtStructField,
            AdtStructFieldSyntax, AnyGeneric, Crate, Expr, FnDef, FnItem, FuncDefOwner,
            GenericBinder, ImplDef, Item, ItemKind, Module, RegionGeneric, SpannedTy, TraitDef,
            TypeGeneric, Visibility,
        },
    },
    symbol,
    utils::hash::FxHashMap,
};
use hashbrown::hash_map;
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
        };

        ctxt.lower_initial_tree(BuilderModuleId::ROOT, ast);

        let krate = Obj::new(
            Crate {
                name: symbol!("demo"),
                is_local: true,
                root: LateInit::uninit(),
                items: LateInit::uninit(),
            },
            s,
        );
        let (modules, items) = ctxt.tree.freeze_and_check(krate, s);
        let root = modules[BuilderModuleId::ROOT];

        let UseLowerCtxt { tree: _, item_asts } = ctxt;

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
                AstItem::Impl(ast) => {
                    ctxt.lower_impl(target, ast);
                }
                AstItem::Func(ast) => {
                    ctxt.lower_fn_item(target, ast);
                }
                AstItem::Struct(ast) => {
                    ctxt.lower_struct(target, ast);
                }
                AstItem::Enum(ast) => {
                    ctxt.lower_enum(target, ast);
                }
                AstItem::Mod(_) | AstItem::Use(_) | AstItem::Error(_, _) => {
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
                block_label_names: NameResolver::new(),
            };

            match kind {
                IntraLowerTask::Trait {
                    item,
                    inherits,
                    generic_clause_lists,
                } => {
                    ctxt.lower_trait(item, inherits, generic_clause_lists);
                }
                IntraLowerTask::Impl { item, ast } => {
                    ctxt.lower_impl(item, ast);
                }
                IntraLowerTask::Adt {
                    item,
                    generic_clause_lists,
                    field_tys_to_extend,
                } => {
                    ctxt.lower_adt(item, generic_clause_lists, field_tys_to_extend);
                }
                IntraLowerTask::FnDef {
                    item,
                    ast,
                    generic_clause_lists,
                } => ctxt.lower_fn_def(item, ast, generic_clause_lists),
            }
        }

        LateInit::init(&krate.r(s).items, items.raw);

        krate
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
                        .push_nameable_item(parent_id, item.base.vis.clone(), item.name);

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

                    self.tree.push_unnamed_item(
                        parent_id,
                        Ident {
                            span: item.base.span,
                            text: symbol!("<impl>"),
                            raw: false,
                        },
                    );

                    self.item_asts.push(item_enum);
                }
                AstItem::Func(item) => {
                    self.tree
                        .push_nameable_item(parent_id, item.base.vis.clone(), item.def.name);

                    self.item_asts.push(item_enum);
                }
                AstItem::Struct(item) => {
                    self.tree
                        .push_nameable_item(parent_id, item.base.vis.clone(), item.name);

                    self.item_asts.push(item_enum);
                }
                AstItem::Enum(item) => {
                    self.tree
                        .push_nameable_item(parent_id, item.base.vis.clone(), item.name);

                    self.item_asts.push(item_enum);
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
    pub tcx: &'a TyCtxt,
    pub item: Obj<Item>,
    pub tasks: &'a mut Vec<(Obj<Module>, IntraLowerTask<'ast>)>,
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
            self.lower_generic_defs(&mut binder, generics, &mut generic_clause_lists);
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

    pub fn lower_struct(&mut self, target: Obj<Item>, ast: &'ast AstItemStruct) {
        let s = &self.tcx.session;

        let mut generics = GenericBinder::default();
        let mut generic_clause_lists = Vec::new();
        let mut field_tys_to_extend = Vec::new();

        if let Some(ast) = &ast.generics {
            self.lower_generic_defs(&mut generics, ast, &mut generic_clause_lists);
        }

        let kind = self.lower_struct_kind(
            &ast.kind,
            &mut field_tys_to_extend,
            /* allow_visibilities */ true,
        );

        let target_def = Obj::new(
            AdtDef {
                item: target,
                generics: self.tcx.seal_generic_binder(generics),
                kind: AdtKind::Struct(kind),
            },
            s,
        );

        LateInit::init(&target.r(s).kind, ItemKind::Adt(target_def));

        self.push_task(IntraLowerTask::Adt {
            item: target_def,
            generic_clause_lists,
            field_tys_to_extend,
        });
    }

    pub fn lower_enum(&mut self, target: Obj<Item>, ast: &'ast AstItemEnum) {
        let s = &self.tcx.session;

        let mut generics = GenericBinder::default();
        let mut generic_clause_lists = Vec::new();
        let mut field_tys_to_extend = Vec::new();

        if let Some(ast) = &ast.generics {
            self.lower_generic_defs(&mut generics, ast, &mut generic_clause_lists);
        }

        let mut by_name = FxHashMap::default();
        let variants = ast
            .variants
            .iter()
            .enumerate()
            .map(|(idx, variant)| {
                match by_name.entry(variant.name.text) {
                    hash_map::Entry::Occupied(entry) => {
                        Diag::span_err(variant.span, "duplicate variant name")
                            .child(LeafDiag::span_note(
                                ast.variants[*entry.get() as usize].name.span,
                                "name first used here",
                            ))
                            .emit();
                    }
                    hash_map::Entry::Vacant(entry) => {
                        entry.insert(idx as u32);
                    }
                }

                AdtEnumVariant {
                    idx: idx as u32,
                    span: variant.span,
                    ident: variant.name,
                    kind: self.lower_struct_kind(
                        &variant.kind,
                        &mut field_tys_to_extend,
                        /* allow_visibilities */ false,
                    ),
                }
            })
            .collect::<Vec<_>>();

        let target_def = Obj::new(
            AdtDef {
                item: target,
                generics: self.tcx.seal_generic_binder(generics),
                kind: AdtKind::Enum(Obj::new(AdtKindEnum { variants, by_name }, s)),
            },
            s,
        );

        LateInit::init(&target.r(s).kind, ItemKind::Adt(target_def));

        self.push_task(IntraLowerTask::Adt {
            item: target_def,
            generic_clause_lists,
            field_tys_to_extend,
        });
    }

    pub fn lower_struct_kind(
        &mut self,
        ast: &'ast AstStructKind,
        field_tys_to_extend: &mut Vec<(&'ast AstTy, Obj<LateInit<SpannedTy>>)>,
        allow_visibilities: bool,
    ) -> Obj<AdtKindStruct> {
        let s = &self.tcx.session;

        let resolve_vis = move |this: &mut Self, vis: &AstVisibility| -> Visibility {
            if !allow_visibilities {
                if !vis.kind.is_omitted() {
                    Diag::span_err(vis.span, "enum fields are all implicitly public").emit();
                }

                return Visibility::Pub;
            }

            // TODO: Resolve this
            Visibility::Pub
        };

        match ast {
            AstStructKind::Unit => Obj::new(
                AdtKindStruct {
                    syntax: AdtStructFieldSyntax::Unit,
                    fields: Vec::new(),
                },
                s,
            ),
            AstStructKind::Tuple(ast) => {
                let fields = ast
                    .iter()
                    .enumerate()
                    .map(|(idx, field)| AdtStructField {
                        span: field.span,
                        idx: idx as u32,
                        vis: resolve_vis(self, &field.vis),
                        ident: None,
                        ty: LateInit::uninit(),
                    })
                    .collect::<Vec<_>>();

                let kind = Obj::new(
                    AdtKindStruct {
                        syntax: AdtStructFieldSyntax::Tuple,
                        fields,
                    },
                    s,
                );

                field_tys_to_extend.extend(ast.iter().enumerate().map(|(idx, ast)| {
                    (&ast.ty, Obj::map(kind, move |kind| &kind.fields[idx].ty, s))
                }));

                kind
            }
            AstStructKind::Struct(ast) => {
                let mut by_name = FxHashMap::default();

                let fields = ast
                    .iter()
                    .enumerate()
                    .map(|(idx, field)| {
                        match by_name.entry(field.name.text) {
                            hash_map::Entry::Occupied(entry) => {
                                Diag::span_err(field.span, "duplicate field name")
                                    .child(LeafDiag::span_note(
                                        ast[*entry.get() as usize].name.span,
                                        "name first used here",
                                    ))
                                    .emit();
                            }
                            hash_map::Entry::Vacant(entry) => {
                                entry.insert(idx as u32);
                            }
                        }

                        AdtStructField {
                            span: field.span,
                            idx: idx as u32,
                            vis: resolve_vis(self, &field.vis),
                            ident: Some(field.name),
                            ty: LateInit::uninit(),
                        }
                    })
                    .collect::<Vec<_>>();

                let kind = Obj::new(
                    AdtKindStruct {
                        syntax: AdtStructFieldSyntax::Named(by_name),
                        fields,
                    },
                    s,
                );

                field_tys_to_extend.extend(ast.iter().enumerate().map(|(idx, ast)| {
                    (&ast.ty, Obj::map(kind, move |kind| &kind.fields[idx].ty, s))
                }));

                kind
            }
        }
    }

    pub fn lower_impl(&mut self, target: Obj<Item>, ast: &'ast AstItemImpl) {
        self.push_task(IntraLowerTask::Impl { item: target, ast });
    }

    pub fn lower_fn_item(&mut self, target: Obj<Item>, ast: &'ast AstItemFn) {
        let s = &self.tcx.session;

        let target_def = Obj::new(
            FnItem {
                item: target,
                def: LateInit::uninit(),
            },
            s,
        );

        LateInit::init(
            &target_def.r(s).def,
            self.lower_fn_def(FuncDefOwner::Func(target_def), &ast.def),
        );

        LateInit::init(&target.r(s).kind, ItemKind::Func(target_def));
    }

    pub fn lower_fn_def(&mut self, owner: FuncDefOwner, ast: &'ast AstFnDef) -> Obj<FnDef> {
        let s = &self.tcx.session;
        let mut generics = GenericBinder::default();
        let mut generic_clause_lists = Vec::new();

        if let Some(ast) = &ast.generics {
            self.lower_generic_defs(&mut generics, ast, &mut generic_clause_lists);
        }

        let def = Obj::new(
            FnDef {
                span: ast.span,
                owner,
                name: ast.name,
                generics: self.tcx.seal_generic_binder(generics),
                self_param: LateInit::uninit(),
                args: LateInit::uninit(),
                ret_ty: LateInit::uninit(),
                body: LateInit::uninit(),
            },
            s,
        );

        self.push_task(IntraLowerTask::FnDef {
            item: def,
            ast,
            generic_clause_lists,
        });

        def
    }
}

// === Third Phase === //

pub struct IntraItemLowerCtxt<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub root: Obj<Module>,
    pub scope: Obj<Module>,
    pub generic_ty_names: NameResolver<Obj<TypeGeneric>>,
    pub generic_re_names: NameResolver<Obj<RegionGeneric>>,
    pub block_label_names: NameResolver<(Span, Obj<Expr>)>,
}

pub enum IntraLowerTask<'ast> {
    Trait {
        item: Obj<TraitDef>,
        inherits: Option<&'ast AstTraitClauseList>,
        generic_clause_lists: Vec<Option<&'ast AstTraitClauseList>>,
    },
    Impl {
        item: Obj<Item>,
        ast: &'ast AstItemImpl,
    },
    Adt {
        item: Obj<AdtDef>,
        generic_clause_lists: Vec<Option<&'ast AstTraitClauseList>>,
        field_tys_to_extend: Vec<(&'ast AstTy, Obj<LateInit<SpannedTy>>)>,
    },
    FnDef {
        item: Obj<FnDef>,
        ast: &'ast AstFnDef,
        generic_clause_lists: Vec<Option<&'ast AstTraitClauseList>>,
    },
}

impl IntraItemLowerCtxt<'_> {
    pub fn lookup_path(
        &self,
        path: &AstSimplePath,
    ) -> Result<AnyDef<Obj<Module>, Obj<Item>>, ErrorGuaranteed> {
        FrozenModuleResolver(&self.tcx.session).lookup_noisy(self.root, self.scope, &path.parts)
    }

    pub fn lookup_label(&mut self, label: Option<Lifetime>) -> Option<Obj<Expr>> {
        let label = label?;
        let resolved = self.block_label_names.lookup(label.name).map(|v| v.1);

        if resolved.is_none() {
            Diag::span_err(label.span, "block label not found").emit();
        }

        resolved
    }

    pub fn scoped<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.generic_ty_names.push_rib();
        self.generic_re_names.push_rib();
        self.block_label_names.push_rib();
        let ret = f(self);
        self.generic_ty_names.pop_rib();
        self.generic_re_names.pop_rib();
        self.block_label_names.pop_rib();

        ret
    }

    pub fn lower_trait(
        mut self,
        item: Obj<TraitDef>,
        inherits: Option<&AstTraitClauseList>,
        generic_clause_lists: Vec<Option<&AstTraitClauseList>>,
    ) {
        let s = &self.tcx.session;

        self.define_generics_in_binder(item.r(s).generics);
        self.lower_generic_def_clauses(item.r(s).generics, &generic_clause_lists);

        LateInit::init(&item.r(s).inherits, self.lower_clauses(inherits));
    }

    pub fn lower_impl(mut self, item: Obj<Item>, ast: &AstItemImpl) {
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
        match (&ast.first_ty, &ast.second_ty) {
            (for_trait, Some(for_ty)) => {
                let Ok(for_trait) = self.lower_trait_instance(for_trait, &ast.body) else {
                    return;
                };

                let for_ty = self.lower_ty(for_ty);

                let item_spec = Obj::new(
                    ImplDef {
                        item,
                        generics: binder,
                        trait_: Some(for_trait),
                        target: for_ty,
                        methods: LateInit::uninit(),
                        generic_solve_order: LateInit::uninit(),
                    },
                    s,
                );

                LateInit::init(&item.r(s).kind, ItemKind::Impl(item_spec));
            }
            (for_ty, None) => {
                todo!()
            }
        }

        // Lower methods
        // TODO
    }

    pub fn lower_adt(
        mut self,
        item: Obj<AdtDef>,
        generic_clause_lists: Vec<Option<&AstTraitClauseList>>,
        field_tys_to_extend: Vec<(&AstTy, Obj<LateInit<SpannedTy>>)>,
    ) {
        let s = &self.tcx.session;

        self.define_generics_in_binder(item.r(s).generics);
        self.lower_generic_def_clauses(item.r(s).generics, &generic_clause_lists);

        for (ast, to_init) in field_tys_to_extend {
            LateInit::init(to_init.r(s), self.lower_ty(ast));
        }
    }

    pub fn lower_fn_def(
        mut self,
        item: Obj<FnDef>,
        ast: &AstFnDef,
        generic_clause_lists: Vec<Option<&AstTraitClauseList>>,
    ) {
        let s = &self.tcx.session;

        self.define_generics_in_binder(item.r(s).generics);
        self.lower_generic_def_clauses(item.r(s).generics, &generic_clause_lists);

        // TODO: Lower signature

        LateInit::init(
            &item.r(s).ret_ty,
            match &ast.ret_ty {
                AstReturnTy::Omitted => None,
                AstReturnTy::Present(ty) => Some(self.lower_ty(ty)),
            },
        );

        LateInit::init(
            &item.r(s).body,
            ast.body.as_ref().map(|body| self.lower_block(body)),
        );
    }
}
