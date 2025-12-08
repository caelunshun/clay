use crate::{
    base::{
        Diag, LeafDiag,
        analysis::NameResolver,
        arena::{LateInit, Obj},
        syntax::{HasSpan as _, Span},
    },
    parse::{
        ast::{
            AstBarePath, AstFnDef, AstGenericDef, AstImplLikeMemberKind, AstItem, AstItemEnum,
            AstItemFn, AstItemImpl, AstItemModuleContents, AstItemStruct, AstItemTrait,
            AstPathPart, AstPathPartKind, AstPathPartKw, AstReturnTy, AstStructKind,
            AstTraitClauseList, AstTreePath, AstTreePathKind, AstTy, AstVisibility,
            AstVisibilityKind,
        },
        token::{Ident, Lifetime},
    },
    semantic::{
        analysis::TyCtxt,
        lower::modules::{
            BuilderItemId, BuilderModuleTree, FrozenVisibilityResolver, ItemCategory,
            VisibilityResolver,
        },
        syntax::{
            AdtCtorDef, AdtCtorField, AdtCtorOwner, AdtCtorSyntax, AdtEnumVariant, AdtItem,
            AdtKind, AdtKindEnum, AdtKindStruct, AnyGeneric, Crate, EnumVariantItem, Expr, FnDef,
            FnItem, FuncDefOwner, FuncLocal, GenericBinder, ImplItem, Item, ItemKind, ModuleItem,
            RegionGeneric, SpannedTy, TraitItem, TypeGeneric, Visibility,
        },
    },
    symbol,
    utils::hash::FxHashMap,
};
use hashbrown::hash_map;
use index_vec::IndexSlice;
use std::rc::Rc;

// === Driver === //

impl TyCtxt {
    pub fn lower_full_ast(&self, ast: &AstItemModuleContents) -> Obj<Crate> {
        let s = &self.session;

        let _delay_and_sort_guard = s.diag.delay_and_sort(s.clone());

        // Build the module tree.
        let mut ctxt = UseLowerCtxt {
            tree: BuilderModuleTree::default(),
            inter_tasks: Vec::new(),
        };

        ctxt.lower_initial_tree(BuilderItemId::ROOT, ast);

        let krate = Obj::new(
            Crate {
                name: symbol!("demo"),
                is_local: true,
                root: LateInit::uninit(),
                items: LateInit::uninit(),
            },
            s,
        );
        let index_to_item = ctxt.tree.freeze_and_check(krate, s);
        let root = index_to_item[BuilderItemId::ROOT];

        let UseLowerCtxt {
            tree: _,
            inter_tasks,
        } = ctxt;

        // Lower inter-item properties.
        let mut intra_tasks = Vec::new();

        InterItemLowerCtxt {
            tcx: self,
            root,
            scope: root,
            target: root,
            intra_tasks: &mut intra_tasks,
            index_to_item: &index_to_item,
        }
        .lower_module(ast);

        for InterTask {
            target,
            scope,
            mut handler,
        } in inter_tasks
        {
            handler(&mut InterItemLowerCtxt {
                tcx: self,
                root,
                scope: index_to_item[scope],
                target: index_to_item[target],
                intra_tasks: &mut intra_tasks,
                index_to_item: &index_to_item,
            });
        }

        // Lower intra-item properties.
        for IntraLowerTask {
            scope,
            target,
            mut handler,
        } in intra_tasks
        {
            handler(IntraItemLowerCtxt {
                tcx: self,
                root,
                scope,
                target,
                generic_ty_names: NameResolver::new(),
                generic_re_names: NameResolver::new(),
                block_label_names: NameResolver::new(),
                func_local_names: NameResolver::new(),
            });
        }

        LateInit::init(&krate.r(s).items, index_to_item.raw);

        krate
    }
}

// === First Phase === //

pub struct UseLowerCtxt<'ast> {
    tree: BuilderModuleTree,
    inter_tasks: Vec<InterTask<'ast>>,
}

struct InterTask<'ast> {
    scope: BuilderItemId,
    target: BuilderItemId,
    handler: Box<dyn 'ast + FnMut(&mut InterItemLowerCtxt<'_, 'ast>)>,
}

impl<'ast> UseLowerCtxt<'ast> {
    pub fn queue_task(
        &mut self,
        scope: BuilderItemId,
        target: BuilderItemId,
        task: impl 'ast + FnOnce(&mut InterItemLowerCtxt<'_, 'ast>),
    ) {
        let mut task = Some(task);

        self.inter_tasks.push(InterTask {
            scope,
            target,
            handler: Box::new(move |cx| task.take().unwrap()(cx)),
        });
    }

    pub fn lower_initial_tree(
        &mut self,
        parent_id: BuilderItemId,
        ast: &'ast AstItemModuleContents,
    ) {
        for item in &ast.items {
            match item {
                AstItem::Mod(item) => {
                    let item_id = self.tree.push_named_item(
                        parent_id,
                        item.base.vis.clone(),
                        ItemCategory::Module,
                        item.name,
                    );

                    self.queue_task(item_id, item_id, |cx| {
                        cx.lower_module(item.contents.as_ref().unwrap())
                    });

                    self.lower_initial_tree(item_id, item.contents.as_ref().unwrap());
                }
                AstItem::Use(item) => {
                    let mut prefix = Vec::new();

                    self.lower_use(parent_id, &item.base.vis, &mut prefix, &item.path);
                }
                AstItem::Trait(item) => {
                    let item_id = self.tree.push_named_item(
                        parent_id,
                        item.base.vis.clone(),
                        ItemCategory::Trait,
                        item.name,
                    );

                    self.queue_task(parent_id, item_id, |cx| {
                        cx.lower_trait(item);
                    });
                }
                AstItem::Impl(item) => {
                    if !item.base.vis.kind.is_omitted() {
                        Diag::span_err(
                            item.base.vis.span,
                            "`impl` blocks cannot have visibilities",
                        )
                        .emit();
                    }

                    let item_id = self
                        .tree
                        .push_unnamed_item(parent_id, ItemCategory::Impl, None);

                    self.queue_task(parent_id, item_id, |cx| {
                        cx.lower_impl(item);
                    });
                }
                AstItem::Func(item) => {
                    let item_id = self.tree.push_named_item(
                        parent_id,
                        item.base.vis.clone(),
                        ItemCategory::Func,
                        item.def.name,
                    );

                    self.queue_task(parent_id, item_id, |cx| {
                        cx.lower_fn_item(item);
                    });
                }
                AstItem::Struct(item) => {
                    let item_id = self.tree.push_named_item(
                        parent_id,
                        item.base.vis.clone(),
                        ItemCategory::Struct,
                        item.name,
                    );

                    self.queue_task(parent_id, item_id, |cx| {
                        cx.lower_struct(item);
                    });
                }
                AstItem::Enum(item) => {
                    let item_id = self.tree.push_named_item(
                        parent_id,
                        item.base.vis.clone(),
                        ItemCategory::Enum,
                        item.name,
                    );

                    self.queue_task(parent_id, item_id, |cx| {
                        cx.lower_enum(item);
                    });

                    for (idx, variant) in item.variants.iter().enumerate() {
                        let variant_id = self.tree.push_named_item(
                            item_id,
                            AstVisibility {
                                span: Span::DUMMY,
                                kind: AstVisibilityKind::Pub,
                            },
                            ItemCategory::EnumVariant,
                            variant.name,
                        );

                        self.queue_task(parent_id, variant_id, move |cx| {
                            cx.lower_variant(cx.index_to_item[item_id], idx as u32);
                        });
                    }
                }
                AstItem::Error(_, _) => {
                    // (ignored)
                }
            }
        }
    }

    pub fn lower_use(
        &mut self,
        mod_id: BuilderItemId,
        visibility: &AstVisibility,
        prefix: &mut Vec<AstPathPart>,
        ast: &AstTreePath,
    ) {
        let old_len = prefix.len();
        prefix.extend_from_slice(&ast.base);

        match &ast.kind {
            AstTreePathKind::Direct(rename) => 'direct: {
                let name = rename
                    .map(AstPathPart::new_ident)
                    .unwrap_or(prefix.last().copied().unwrap());

                let name = match name.kind() {
                    AstPathPartKind::Keyword(_, AstPathPartKw::Crate) => {
                        Diag::span_err(
                            name.span(),
                            "crate root imports need to be explicitly named",
                        )
                        .emit();

                        break 'direct;
                    }
                    AstPathPartKind::Keyword(_, AstPathPartKw::Super) => {
                        Diag::span_err(name.span(), "invalid name for import").emit();

                        break 'direct;
                    }
                    AstPathPartKind::Keyword(_, AstPathPartKw::Self_) => {
                        let Some(new_name) = prefix[..prefix.len() - 1]
                            .last()
                            .copied()
                            .and_then(|name| name.ident())
                        else {
                            Diag::span_err(
                                name.span(),
                                "`self` imports are only allowed after an identifier",
                            )
                            .emit();

                            break 'direct;
                        };

                        Ident {
                            span: name.span(),
                            text: new_name.text,
                            raw: new_name.raw,
                        }
                    }
                    AstPathPartKind::Regular(ident) => ident,
                };

                self.tree.push_single_use(
                    mod_id,
                    visibility.clone(),
                    name,
                    AstBarePath {
                        span: ast.span,
                        parts: Rc::from(prefix.as_slice()),
                    },
                );
            }
            AstTreePathKind::Wild(span) => {
                self.tree.push_glob_use(
                    mod_id,
                    visibility.clone(),
                    AstBarePath {
                        span: *span,
                        parts: Rc::from(prefix.as_slice()),
                    },
                );
            }
            AstTreePathKind::Tree(children) => {
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
    pub root: Obj<Item>,
    pub scope: Obj<Item>,
    pub target: Obj<Item>,
    pub intra_tasks: &'a mut Vec<IntraLowerTask<'ast>>,
    pub index_to_item: &'a IndexSlice<BuilderItemId, [Obj<Item>]>,
}

pub struct IntraLowerTask<'ast> {
    scope: Obj<Item>,
    target: Obj<Item>,
    handler: Box<dyn 'ast + FnMut(IntraItemLowerCtxt<'_>)>,
}

impl<'ast> InterItemLowerCtxt<'_, 'ast> {
    pub fn queue_task(&mut self, task: impl 'ast + FnOnce(IntraItemLowerCtxt<'_>)) {
        let mut task = Some(task);

        self.intra_tasks.push(IntraLowerTask {
            scope: self.scope,
            target: self.target,
            handler: Box::new(move |cx| task.take().unwrap()(cx)),
        });
    }

    pub fn resolve_visibility(&self, vis: &AstVisibility) -> Visibility {
        match &vis.kind {
            AstVisibilityKind::Implicit | AstVisibilityKind::Priv => Visibility::PubIn(self.scope),
            AstVisibilityKind::Pub => Visibility::Pub,
            AstVisibilityKind::PubIn(path) => {
                match FrozenVisibilityResolver(&self.tcx.session)
                    .resolve_visibility_target(self.root, self.scope, path)
                {
                    Ok(target) => Visibility::PubIn(target),
                    Err(_) => Visibility::Pub,
                }
            }
        }
    }

    pub fn lower_module(&mut self, _ast: &'ast AstItemModuleContents) {
        let s = &self.tcx.session;

        LateInit::init(
            &self.target.r(s).kind,
            ItemKind::Module(Obj::new(ModuleItem { item: self.target }, s)),
        );
    }

    pub fn lower_trait(&mut self, ast: &'ast AstItemTrait) {
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
            TraitItem {
                item: self.target,
                generics: self.tcx.seal_generic_binder(binder),
                inherits: LateInit::uninit(),
                regular_generic_count,
                associated_types,
                methods: LateInit::uninit(),
            },
            s,
        );

        LateInit::init(&self.target.r(s).kind, ItemKind::Trait(trait_target));

        self.queue_task(move |cx| {
            cx.lower_trait(trait_target, ast.inherits.as_ref(), generic_clause_lists);
        });
    }

    pub fn lower_struct(&mut self, ast: &'ast AstItemStruct) {
        let s = &self.tcx.session;

        let mut generics = GenericBinder::default();
        let mut generic_clause_lists = Vec::new();
        let mut field_tys_to_extend = Vec::new();

        if let Some(ast) = &ast.generics {
            self.lower_generic_defs(&mut generics, ast, &mut generic_clause_lists);
        }

        let target_adt = Obj::new(
            AdtItem {
                item: self.target,
                generics: self.tcx.seal_generic_binder(generics),
                kind: LateInit::uninit(),
            },
            s,
        );

        LateInit::init(&self.target.r(s).kind, ItemKind::Adt(target_adt));

        let target_struct = Obj::new(
            AdtKindStruct {
                adt: target_adt,
                ctor: LateInit::uninit(),
            },
            s,
        );

        LateInit::init(&target_adt.r(s).kind, AdtKind::Struct(target_struct));

        let ctor = self.lower_struct_ctor(
            AdtCtorOwner::Struct(target_struct),
            &ast.kind,
            &mut field_tys_to_extend,
            /* allow_visibilities */ true,
        );

        LateInit::init(&target_struct.r(s).ctor, ctor);

        self.queue_task(move |cx| {
            cx.lower_adt(target_adt, generic_clause_lists, field_tys_to_extend);
        });
    }

    pub fn lower_enum(&mut self, ast: &'ast AstItemEnum) {
        let s = &self.tcx.session;

        let mut generics = GenericBinder::default();
        let mut generic_clause_lists = Vec::new();
        let mut field_tys_to_extend = Vec::new();

        if let Some(ast) = &ast.generics {
            self.lower_generic_defs(&mut generics, ast, &mut generic_clause_lists);
        }

        let target_adt = Obj::new(
            AdtItem {
                item: self.target,
                generics: self.tcx.seal_generic_binder(generics),
                kind: LateInit::uninit(),
            },
            s,
        );

        LateInit::init(&self.target.r(s).kind, ItemKind::Adt(target_adt));

        let target_enum = Obj::new(
            AdtKindEnum {
                adt: target_adt,
                variants: LateInit::uninit(),
                by_name: LateInit::uninit(),
            },
            s,
        );

        LateInit::init(&target_adt.r(s).kind, AdtKind::Enum(target_enum));

        let mut by_name = FxHashMap::default();
        let variants = ast
            .variants
            .iter()
            .enumerate()
            .map(|(idx, variant_ast)| {
                // Enums already have their variant names checked by the module resolution engine.
                //
                // Rust does this too:
                //
                // ```rust
                // pub enum Whee {
                //     Foo,
                //     Foo,
                // }
                //
                // pub struct Woo {
                //     foo: (),
                //     foo: (),
                // }
                // ```
                //
                // ```
                // error[E0428]: the name `Foo` is defined multiple times
                //  --> src/lib.rs:3:5
                //   |
                // 2 |     Foo,
                //   |     --- previous definition of the type `Foo` here
                // 3 |     Foo,
                //   |     ^^^ `Foo` redefined here
                //   |
                //   = note: `Foo` must be defined only once in the type namespace of this enum
                //
                // error[E0124]: field `foo` is already declared
                //  --> src/lib.rs:8:5
                //   |
                // 7 |     foo: (),
                //   |     ------- `foo` first declared here
                // 8 |     foo: (),
                //   |     ^^^^^^^ field already declared
                // ```
                by_name.entry(variant_ast.name.text).or_insert(idx as u32);

                let variant = Obj::new(
                    AdtEnumVariant {
                        owner: target_enum,
                        idx: idx as u32,
                        span: variant_ast.span,
                        ident: variant_ast.name,
                        ctor: LateInit::uninit(),
                    },
                    s,
                );

                let ctor = self.lower_struct_ctor(
                    AdtCtorOwner::EnumVariant(variant),
                    &variant_ast.kind,
                    &mut field_tys_to_extend,
                    false,
                );

                LateInit::init(&variant.r(s).ctor, ctor);

                variant
            })
            .collect::<Vec<_>>();

        LateInit::init(&target_enum.r(s).variants, variants);
        LateInit::init(&target_enum.r(s).by_name, by_name);

        self.queue_task(move |cx| {
            cx.lower_adt(target_adt, generic_clause_lists, field_tys_to_extend);
        });
    }

    pub fn lower_variant(&mut self, owner: Obj<Item>, idx: u32) {
        let s = &self.tcx.session;

        LateInit::init(
            &self.target.r(s).kind,
            ItemKind::EnumVariant(Obj::new(
                EnumVariantItem {
                    item: self.target,
                    owner,
                    idx,
                },
                s,
            )),
        );
    }

    pub fn lower_struct_ctor(
        &mut self,
        owner: AdtCtorOwner,
        ast: &'ast AstStructKind,
        field_tys_to_extend: &mut Vec<(&'ast AstTy, Obj<LateInit<SpannedTy>>)>,
        allow_visibilities: bool,
    ) -> Obj<AdtCtorDef> {
        let s = &self.tcx.session;

        let resolve_vis = move |this: &mut Self, vis: &AstVisibility| -> Visibility {
            if !allow_visibilities {
                if !vis.kind.is_omitted() {
                    Diag::span_err(vis.span, "enum fields are all implicitly public").emit();
                }

                return Visibility::Pub;
            }

            this.resolve_visibility(vis)
        };

        match ast {
            AstStructKind::Unit => Obj::new(
                AdtCtorDef {
                    owner,
                    syntax: AdtCtorSyntax::Unit,
                    fields: Vec::new(),
                },
                s,
            ),
            AstStructKind::Tuple(ast) => {
                let fields = ast
                    .iter()
                    .enumerate()
                    .map(|(idx, field)| AdtCtorField {
                        span: field.span,
                        idx: idx as u32,
                        vis: resolve_vis(self, &field.vis),
                        ident: None,
                        ty: LateInit::uninit(),
                    })
                    .collect::<Vec<_>>();

                let kind = Obj::new(
                    AdtCtorDef {
                        owner,
                        syntax: AdtCtorSyntax::Tuple,
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

                        AdtCtorField {
                            span: field.span,
                            idx: idx as u32,
                            vis: resolve_vis(self, &field.vis),
                            ident: Some(field.name),
                            ty: LateInit::uninit(),
                        }
                    })
                    .collect::<Vec<_>>();

                let kind = Obj::new(
                    AdtCtorDef {
                        owner,
                        syntax: AdtCtorSyntax::Named(by_name),
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

    pub fn lower_impl(&mut self, ast: &'ast AstItemImpl) {
        let target = self.target;

        self.queue_task(move |cx| {
            cx.lower_impl(target, ast);
        });
    }

    pub fn lower_fn_item(&mut self, ast: &'ast AstItemFn) {
        let s = &self.tcx.session;

        let target_def = Obj::new(
            FnItem {
                item: self.target,
                def: LateInit::uninit(),
            },
            s,
        );

        LateInit::init(
            &target_def.r(s).def,
            self.lower_fn_def(FuncDefOwner::Func(target_def), &ast.def),
        );

        LateInit::init(&self.target.r(s).kind, ItemKind::Func(target_def));
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

        self.queue_task(move |cx| {
            cx.lower_fn_def(def, ast, generic_clause_lists);
        });

        def
    }
}

// === Third Phase === //

pub struct IntraItemLowerCtxt<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub root: Obj<Item>,
    pub scope: Obj<Item>,
    pub target: Obj<Item>,
    pub generic_ty_names: NameResolver<Obj<TypeGeneric>>,
    pub generic_re_names: NameResolver<Obj<RegionGeneric>>,
    pub block_label_names: NameResolver<(Span, Obj<Expr>)>,
    pub func_local_names: NameResolver<Obj<FuncLocal>>,
}

impl IntraItemLowerCtxt<'_> {
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
        self.func_local_names.push_rib();
        let ret = f(self);
        self.generic_ty_names.pop_rib();
        self.generic_re_names.pop_rib();
        self.block_label_names.pop_rib();
        self.func_local_names.pop_rib();

        ret
    }

    pub fn lower_trait(
        mut self,
        item: Obj<TraitItem>,
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
                let for_ty = self.lower_ty(for_ty);
                let Ok(for_trait) = self.lower_trait_instance_of_impl_block(for_trait, &ast.body)
                else {
                    // TODO: don't early return
                    return;
                };

                let item_spec = Obj::new(
                    ImplItem {
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
    }

    pub fn lower_adt(
        mut self,
        item: Obj<AdtItem>,
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
