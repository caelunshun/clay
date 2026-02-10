use crate::{
    base::{
        Diag, LeafDiag,
        analysis::NameResolver,
        arena::{HasInterner, HasListInterner, LateInit, Obj},
        syntax::{HasSpan as _, Span, Symbol},
    },
    parse::{
        ast::{
            AstAttribute, AstBarePath, AstFnDef, AstImplLikeMemberKind, AstItem, AstItemEnum,
            AstItemFn, AstItemImpl, AstItemModuleContents, AstItemStruct, AstItemTrait,
            AstItemTypeAlias, AstPathPart, AstPathPartKind, AstPathPartKw, AstReturnTy,
            AstStructKind, AstTraitClauseList, AstTreePath, AstTreePathKind, AstTy, AstVisibility,
            AstVisibilityKind,
        },
        token::{Ident, Lifetime},
    },
    semantic::{
        analysis::TyCtxt,
        lower::modules::{
            BuilderItemId, BuilderModuleTree, FrozenModuleResolver, FrozenVisibilityResolver,
            ItemCategory, PathResolver, VisibilityResolver,
        },
        syntax::{
            AdtCtor, AdtCtorField, AdtCtorFieldIdx, AdtCtorOwner, AdtCtorSyntax, AdtEnumVariant,
            AdtEnumVariantIdx, AdtItem, AdtKind, AdtKindEnum, AdtKindStruct, AnyGeneric, Crate,
            EnumVariantItem, Expr, FnDef, FuncArg, FuncDefOwner, FuncItem, FuncLocal,
            GenericBinder, ImplItem, Item, ItemKind, LangItems, ModuleItem, RegionGeneric,
            SpannedTy, TraitItem, TyKind, TypeAliasItem, TypeGeneric, Visibility,
        },
    },
    symbol,
    utils::{
        hash::FxHashMap,
        lang::{AND_LIST_GLUE, format_list},
    },
};
use hashbrown::hash_map;
use index_vec::{IndexSlice, IndexVec};
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
                lang_items: LangItems::default(),
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
        .lower_module(ast, None);

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
                        cx.lower_module(
                            item.contents.as_ref().unwrap(),
                            Some(&item.base.outer_attrs),
                        )
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
                AstItem::TypeAlias(item) => {
                    let item_id = self.tree.push_named_item(
                        parent_id,
                        item.base.vis.clone(),
                        ItemCategory::TypeAlias,
                        item.name,
                    );

                    self.queue_task(parent_id, item_id, |cx| {
                        cx.lower_type_alias(item);
                    });
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

    pub fn queue_lower_item_attributes(
        &mut self,
        attrs: impl 'ast + IntoIterator<Item = &'ast AstAttribute>,
    ) {
        let target = self.target;

        self.queue_task(move |mut cx| cx.lower_item_attributes(target, attrs));
    }

    pub fn lower_module(
        &mut self,
        ast: &'ast AstItemModuleContents,
        outer_attrs: Option<&'ast [AstAttribute]>,
    ) {
        let s = &self.tcx.session;

        self.queue_lower_item_attributes(
            ast.inner_attrs
                .iter()
                .chain(outer_attrs.into_iter().flatten()),
        );

        LateInit::init(
            &self.target.r(s).kind,
            ItemKind::Module(Obj::new(ModuleItem { item: self.target }, s)),
        );
    }

    pub fn lower_trait(&mut self, ast: &'ast AstItemTrait) {
        let s = &self.tcx.session;

        self.queue_lower_item_attributes(&ast.base.outer_attrs);

        let trait_target = Obj::new(
            TraitItem {
                item: self.target,
                generics: LateInit::uninit(),
                inherits: LateInit::uninit(),
                regular_generic_count: LateInit::uninit(),
                associated_types: LateInit::uninit(),
                methods: LateInit::uninit(),
                name_to_method: LateInit::uninit(),
            },
            s,
        );

        LateInit::init(&self.target.r(s).kind, ItemKind::Trait(trait_target));

        // Lower regular generics
        let mut binder = GenericBinder::default();
        let mut generic_clause_lists = Vec::new();

        if let Some(generics) = &ast.generics {
            self.lower_generic_defs(&mut binder, generics, &mut generic_clause_lists);
        }

        let regular_generic_count = binder.defs.len() as u32;

        // Lower members
        let mut associated_types = FxHashMap::default();
        let mut methods = Vec::<Obj<FnDef>>::new();
        let mut name_to_method = FxHashMap::<Symbol, u32>::default();

        for member in &ast.body.members {
            match &member.kind {
                AstImplLikeMemberKind::TypeInherits(name, clauses) => {
                    let generic = Obj::new(
                        TypeGeneric {
                            span: member.span,
                            ident: *name,
                            binder: LateInit::uninit(),
                            clauses: LateInit::uninit(),
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
                AstImplLikeMemberKind::Func(ast) => {
                    let method = self.lower_fn_def(ast);
                    LateInit::init(
                        &method.r(s).owner,
                        FuncDefOwner::TraitMethod(trait_target, methods.len() as u32),
                    );

                    match name_to_method.entry(method.r(s).name.text) {
                        hash_map::Entry::Occupied(entry) => {
                            let prev = methods[*entry.get() as usize];

                            Diag::span_err(
                                method.r(s).name.span,
                                format_args!(
                                    "method name `{}` used more than once",
                                    method.r(s).name.text,
                                ),
                            )
                            .child(LeafDiag::span_note(
                                prev.r(s).name.span,
                                "previously defined here",
                            ))
                            .emit();
                        }
                        hash_map::Entry::Vacant(entry) => {
                            entry.insert(methods.len() as u32);
                        }
                    }

                    methods.push(method);
                }
                AstImplLikeMemberKind::Error(_) => {
                    // (ignored)
                }
            }
        }

        LateInit::init(
            &trait_target.r(s).generics,
            self.tcx.seal_generic_binder(binder),
        );

        LateInit::init(
            &trait_target.r(s).regular_generic_count,
            regular_generic_count,
        );

        LateInit::init(&trait_target.r(s).associated_types, associated_types);
        LateInit::init(&trait_target.r(s).methods, methods);
        LateInit::init(&trait_target.r(s).name_to_method, name_to_method);

        self.queue_task(move |cx| {
            cx.lower_trait(trait_target, ast.inherits.as_ref(), generic_clause_lists);
        });
    }

    pub fn lower_struct(&mut self, ast: &'ast AstItemStruct) {
        let s = &self.tcx.session;

        self.queue_lower_item_attributes(&ast.base.outer_attrs);

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

        self.queue_lower_item_attributes(&ast.base.outer_attrs);

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
                let idx = AdtEnumVariantIdx::from_usize(idx);

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
                by_name.entry(variant_ast.name.text).or_insert(idx);

                let variant = Obj::new(
                    AdtEnumVariant {
                        owner: target_enum,
                        idx,
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
            .collect::<IndexVec<_, _>>();

        LateInit::init(&target_enum.r(s).variants, variants);
        LateInit::init(&target_enum.r(s).by_name, by_name);

        self.queue_task(move |cx| {
            cx.lower_adt(target_adt, generic_clause_lists, field_tys_to_extend);
        });
    }

    pub fn lower_variant(&mut self, owner: Obj<Item>, idx: u32) {
        let s = &self.tcx.session;

        LateInit::init(&self.target.r(s).attrs, Vec::new());
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
    ) -> Obj<AdtCtor> {
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
                AdtCtor {
                    owner,
                    syntax: AdtCtorSyntax::Unit,
                    fields: IndexVec::new(),
                },
                s,
            ),
            AstStructKind::Tuple(ast) => {
                let fields = ast
                    .iter()
                    .enumerate()
                    .map(|(idx, field)| AdtCtorField {
                        span: field.span,
                        idx: AdtCtorFieldIdx::from_usize(idx),
                        vis: resolve_vis(self, &field.vis),
                        ident: None,
                        ty: LateInit::uninit(),
                    })
                    .collect::<IndexVec<_, _>>();

                let kind = Obj::new(
                    AdtCtor {
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
                let mut by_name = FxHashMap::<Symbol, AdtCtorFieldIdx>::default();

                let fields = ast
                    .iter()
                    .enumerate()
                    .map(|(idx, field)| {
                        let idx = AdtCtorFieldIdx::from_usize(idx);

                        match by_name.entry(field.name.text) {
                            hash_map::Entry::Occupied(entry) => {
                                Diag::span_err(field.span, "duplicate field name")
                                    .child(LeafDiag::span_note(
                                        ast[entry.get().index()].name.span,
                                        "name first used here",
                                    ))
                                    .emit();
                            }
                            hash_map::Entry::Vacant(entry) => {
                                entry.insert(idx);
                            }
                        }

                        AdtCtorField {
                            span: field.span,
                            idx,
                            vis: resolve_vis(self, &field.vis),
                            ident: Some(field.name),
                            ty: LateInit::uninit(),
                        }
                    })
                    .collect::<IndexVec<_, _>>();

                let kind = Obj::new(
                    AdtCtor {
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
        let tcx = self.tcx;
        let s = &self.tcx.session;

        let mut generics = GenericBinder::default();
        let mut generic_clause_lists = Vec::new();

        if let Some(ast) = &ast.generics {
            self.lower_generic_defs(&mut generics, ast, &mut generic_clause_lists);
        }

        let target_impl = Obj::new(
            ImplItem {
                item: self.target,
                generics: tcx.seal_generic_binder(generics),
                trait_: LateInit::uninit(),
                target: LateInit::uninit(),
                methods: LateInit::uninit(),
            },
            s,
        );

        LateInit::init(&self.target.r(s).kind, ItemKind::Impl(target_impl));

        let mut method_defs = Vec::new();

        for member in &ast.body.members {
            let AstImplLikeMemberKind::Func(def) = &member.kind else {
                continue;
            };

            // Keep `owner` uninit until later.
            method_defs.push(self.lower_fn_def(def));
        }

        self.queue_lower_item_attributes(&ast.base.outer_attrs);
        self.queue_task(move |cx| {
            cx.lower_impl(target_impl, ast, generic_clause_lists, method_defs)
        });
    }

    pub fn lower_fn_item(&mut self, ast: &'ast AstItemFn) {
        let s = &self.tcx.session;

        self.queue_lower_item_attributes(&ast.base.outer_attrs);

        let target_def = Obj::new(
            FuncItem {
                item: self.target,
                def: LateInit::uninit(),
            },
            s,
        );

        let def = self.lower_fn_def(&ast.def);
        LateInit::init(&def.r(s).owner, FuncDefOwner::Func(target_def));
        LateInit::init(&target_def.r(s).def, def);

        LateInit::init(&self.target.r(s).kind, ItemKind::Func(target_def));
    }

    pub fn lower_fn_def(&mut self, ast: &'ast AstFnDef) -> Obj<FnDef> {
        let s = &self.tcx.session;
        let mut generics = GenericBinder::default();
        let mut generic_clause_lists = Vec::new();

        if let Some(ast) = &ast.generics {
            self.lower_generic_defs(&mut generics, ast, &mut generic_clause_lists);
        }

        let def = Obj::new(
            FnDef {
                span: ast.span,
                owner: LateInit::uninit(),
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

    pub fn lower_type_alias(&mut self, ast: &'ast AstItemTypeAlias) {
        let s = &self.tcx.session;
        let mut generics = GenericBinder::default();
        let mut generic_clause_lists = Vec::new();

        if let Some(ast) = &ast.generics {
            self.lower_generic_defs(&mut generics, ast, &mut generic_clause_lists);
        }

        let def = Obj::new(
            TypeAliasItem {
                item: self.target,
                generics: self.tcx.seal_generic_binder(generics),
                body: LateInit::uninit(),
            },
            s,
        );

        LateInit::init(&self.target.r(s).kind, ItemKind::TypeAlias(def));

        self.queue_lower_item_attributes(&ast.base.outer_attrs);

        self.queue_task(move |cx| {
            cx.lower_type_alias(def, ast, generic_clause_lists);
        });
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

        self.define_generics_in_binder(*item.r(s).generics);
        self.lower_generic_def_clauses(*item.r(s).generics, &generic_clause_lists);

        LateInit::init(&item.r(s).inherits, self.lower_clauses(inherits));
    }

    pub fn lower_impl(
        mut self,
        item: Obj<ImplItem>,
        ast: &AstItemImpl,
        generic_clause_lists: Vec<Option<&AstTraitClauseList>>,
        method_defs: Vec<Obj<FnDef>>,
    ) {
        let s = &self.tcx.session;

        self.define_generics_in_binder(item.r(s).generics);
        self.lower_generic_def_clauses(item.r(s).generics, &generic_clause_lists);

        // Lower source trait
        let (for_ty, for_trait) = match (&ast.first_ty, &ast.second_ty) {
            (for_trait, Some(for_ty)) => {
                let for_ty = self.lower_ty(for_ty);

                // Validate members
                for member in &ast.body.members {
                    if !member.vis.kind.is_omitted() {
                        Diag::span_err(
                            member.vis.span,
                            "trait `impl` block members cannot have visibilities",
                        )
                        .emit();
                    }

                    match &member.kind {
                        AstImplLikeMemberKind::TypeEquals(_, _) => {
                            // (verified in `lower_trait_instance_of_impl_block`)
                        }
                        AstImplLikeMemberKind::TypeInherits(name, _) => {
                            Diag::span_err(name.span, "all associated type parameters must be specified in an `impl` block").emit();
                        }
                        AstImplLikeMemberKind::Func(def) => {
                            if def.body.is_none() {
                                Diag::span_err(def.name.span, "missing method body").emit();
                            }
                        }
                        AstImplLikeMemberKind::Error(_) => {
                            // (trivially accepted)
                        }
                    }
                }

                // Lower signature
                if let Ok(for_trait) = self.lower_trait_instance_of_impl_block(for_trait, &ast.body)
                {
                    (for_ty, Some(for_trait))
                } else {
                    (for_ty, None)
                }
            }
            (for_ty, None) => {
                let for_ty = self.lower_ty(for_ty);

                // Validate members
                for member in &ast.body.members {
                    match &member.kind {
                        AstImplLikeMemberKind::TypeEquals(ident, _)
                        | AstImplLikeMemberKind::TypeInherits(ident, _) => {
                            Diag::span_err(
                                ident.span,
                                "associated types cannot be specified in inherent `impl` blocks",
                            )
                            .emit();
                        }
                        AstImplLikeMemberKind::Func(def) => {
                            if def.body.is_none() {
                                Diag::span_err(def.name.span, "missing method body").emit();
                            }
                        }
                        AstImplLikeMemberKind::Error(_) => {
                            // (accepted)
                        }
                    }
                }

                (for_ty, None)
            }
        };

        LateInit::init(&item.r(s).target, for_ty);
        LateInit::init(&item.r(s).trait_, for_trait);

        // Establish a method order.
        let method_defs = if let Some(for_trait) = for_trait {
            let for_trait = for_trait.value.def;
            let mut new_method_defs = (0..for_trait.r(s).methods.len())
                .map(|_| None::<Obj<FnDef>>)
                .collect::<Vec<_>>();

            for method in method_defs {
                let Some(&idx) = for_trait.r(s).name_to_method.get(&method.r(s).name.text) else {
                    Diag::span_err(
                        method.r(s).name.span,
                        format_args!(
                            "trait `{}` does not have method `{}`",
                            FrozenModuleResolver(s).path(for_trait.r(s).item),
                            method.r(s).name.text
                        ),
                    )
                    .emit();

                    continue;
                };

                let idx = idx as usize;

                if let Some(prev) = new_method_defs[idx] {
                    Diag::span_err(
                        method.r(s).name.span,
                        format_args!(
                            "implementation of method `{}` provided more than once",
                            prev.r(s).name.text,
                        ),
                    )
                    .child(LeafDiag::span_note(
                        prev.r(s).name.span,
                        "previously implemented here",
                    ))
                    .emit();

                    continue;
                }

                new_method_defs[idx] = Some(method);
            }

            let mut missing_names = Vec::new();

            for (base, def) in for_trait.r(s).methods.iter().zip(&new_method_defs) {
                if def.is_some() {
                    continue;
                }

                if base.r(s).body.is_some() {
                    continue;
                }

                missing_names.push(base.r(s).name.text);
            }

            if !missing_names.is_empty() {
                Diag::span_err(
                    ast.first_ty.span,
                    format_args!(
                        "missing definition{} for required method{} {}",
                        if missing_names.len() == 1 { "" } else { "s" },
                        if missing_names.len() == 1 { "" } else { "s" },
                        format_list(
                            missing_names.iter().map(|v| format!("`{v}`")),
                            AND_LIST_GLUE
                        ),
                    ),
                )
                .emit();
            }

            new_method_defs
        } else {
            // Just use the user-defined order.
            method_defs.into_iter().map(Some).collect::<Vec<_>>()
        };

        for (i, method) in method_defs.iter().enumerate() {
            let Some(method) = method else {
                continue;
            };

            LateInit::init(&method.r(s).owner, FuncDefOwner::ImplMethod(item, i as u32));
        }

        LateInit::init(&item.r(s).methods, method_defs);
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

        LateInit::init(
            &item.r(s).args,
            Obj::new_iter(
                ast.args.iter().map(|arg| FuncArg {
                    span: arg.span,
                    pat: self.lower_pat(&arg.pat),
                    ty: self.lower_ty(&arg.ty),
                }),
                s,
            ),
        );

        LateInit::init(
            &item.r(s).ret_ty,
            match &ast.ret_ty {
                AstReturnTy::Omitted => SpannedTy::new_unspanned(
                    self.tcx.intern(TyKind::Tuple(self.tcx.intern_list(&[]))),
                ),
                AstReturnTy::Present(ty) => self.lower_ty(ty),
            },
        );

        LateInit::init(
            &item.r(s).body,
            ast.body.as_ref().map(|body| self.lower_block(body)),
        );
    }

    pub fn lower_type_alias(
        mut self,
        item: Obj<TypeAliasItem>,
        ast: &AstItemTypeAlias,
        generic_clause_lists: Vec<Option<&AstTraitClauseList>>,
    ) {
        let s = &self.tcx.session;

        self.define_generics_in_binder(item.r(s).generics);
        self.lower_generic_def_clauses(item.r(s).generics, &generic_clause_lists);

        LateInit::init(&item.r(s).body, self.lower_ty(&ast.body));
    }
}
