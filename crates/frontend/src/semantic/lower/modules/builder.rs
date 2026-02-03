use crate::{
    base::{
        Diag, LeafDiag, Session,
        arena::{LateInit, Obj},
        syntax::{Span, Symbol},
    },
    parse::{
        ast::{AstBarePath, AstVisibility, AstVisibilityKind},
        token::Ident,
    },
    semantic::{
        lower::modules::{
            ItemCategory, ItemCategoryUse, ItemPathFmt, ParentRef, ParentResolver, PathResolver,
            StepLookupError, VisibilityResolver,
        },
        syntax::{Crate, DirectUse, GlobUse, Item, Visibility},
    },
    symbol,
    utils::hash::FxIndexMap,
};
use index_vec::{IndexVec, define_index_type};
use std::mem;

// === Handles === //

define_index_type! {
    pub struct BuilderItemId = u32;
}

impl BuilderItemId {
    pub const ROOT: Self = BuilderItemId { _raw: 0 };
}

// === BuilderModuleTree === //

pub struct BuilderModuleTree {
    items: IndexVec<BuilderItemId, BuilderItem>,
}

struct BuilderItem {
    direct_parent: ParentRef<BuilderItemId>,
    category: ItemCategory,
    name: Option<Ident>,
    public_path: Option<Symbol>,
    glob_uses: Vec<BuilderGlobUse>,
    direct_uses: FxIndexMap<Symbol, BuilderDirectUse>,
}

struct BuilderGlobUse {
    span: Span,
    visibility: BuilderVisibility,
    target: CachedPath,
}

struct BuilderDirectUse {
    name: Ident,
    visibility: BuilderVisibility,
    target: CachedPath,
    is_direct_child: bool,
}

enum CachedPath {
    Ignore,
    Unresolved(AstBarePath),
    Resolved(BuilderItemId),
}

#[derive(Clone)]
enum BuilderVisibility {
    Pub,
    PubInResolved(BuilderItemId),
    PubInUnresolved(AstBarePath),
}

impl Default for BuilderModuleTree {
    fn default() -> Self {
        Self {
            items: IndexVec::from_iter([BuilderItem {
                direct_parent: ParentRef::Real(None),
                category: ItemCategory::Module,
                name: None,
                public_path: None,
                glob_uses: Vec::new(),
                direct_uses: FxIndexMap::default(),
            }]),
        }
    }
}

impl BuilderModuleTree {
    fn push_direct_use(&mut self, target: BuilderItemId, direct: BuilderDirectUse) {
        let target_category = self.categorize(target);

        match self.items[target].direct_uses.entry(direct.name.text) {
            indexmap::map::Entry::Vacant(entry) => {
                entry.insert(direct);
            }
            indexmap::map::Entry::Occupied(entry) => {
                Diag::span_err(
                    direct.name.span,
                    format_args!(
                        "name `{}` used more than once in {}",
                        direct.name.text,
                        target_category.bare_what(),
                    ),
                )
                .child(LeafDiag::span_note(
                    entry.get().name.span,
                    "name previously used here",
                ))
                .emit();
            }
        }
    }

    pub fn push_named_item(
        &mut self,
        parent: BuilderItemId,
        visibility: AstVisibility,
        category: ItemCategory,
        name: Ident,
    ) -> BuilderItemId {
        let child = self.items.push(BuilderItem {
            direct_parent: ParentRef::Real(Some(parent)),
            category,
            name: Some(name),
            public_path: None,
            glob_uses: Vec::new(),
            direct_uses: FxIndexMap::default(),
        });

        self.push_direct_use(
            parent,
            BuilderDirectUse {
                name,
                visibility: convert_visibility(parent, visibility),
                target: CachedPath::Resolved(child),
                is_direct_child: true,
            },
        );

        child
    }

    pub fn push_unnamed_item(
        &mut self,
        parent: BuilderItemId,
        category: ItemCategory,
        name: Option<Ident>,
    ) -> BuilderItemId {
        self.items.push(BuilderItem {
            direct_parent: ParentRef::Real(Some(parent)),
            category,
            name,
            public_path: None,
            glob_uses: Vec::new(),
            direct_uses: FxIndexMap::default(),
        })
    }

    pub fn push_glob_use(
        &mut self,
        parent: BuilderItemId,
        visibility: AstVisibility,
        path: AstBarePath,
    ) {
        self.items[parent].glob_uses.push(BuilderGlobUse {
            span: path.span,
            visibility: convert_visibility(parent, visibility),
            target: CachedPath::Unresolved(path),
        });
    }

    pub fn push_single_use(
        &mut self,
        parent: BuilderItemId,
        visibility: AstVisibility,
        name: Ident,
        path: AstBarePath,
    ) {
        self.push_direct_use(
            parent,
            BuilderDirectUse {
                name,
                visibility: convert_visibility(parent, visibility),
                target: CachedPath::Unresolved(path),
                is_direct_child: false,
            },
        )
    }

    pub fn freeze_and_check(
        mut self,
        krate: Obj<Crate>,
        s: &Session,
    ) -> IndexVec<BuilderItemId, Obj<Item>> {
        // Determine public paths for each module.
        // TODO: improve this algorithm.
        for item_id in self.items.indices() {
            match self.items[item_id].direct_parent.as_option() {
                Some(parent) => {
                    let parent_name = self.items[parent].public_path.unwrap();

                    if let Some(own_name) = self.items[item_id].name {
                        if parent_name.as_str(s).is_empty() {
                            self.items[item_id].public_path = Some(own_name.text);
                        } else {
                            self.items[item_id].public_path =
                                Some(Symbol::new(&format!("{parent_name}::{}", own_name.text)));
                        }
                    } else {
                        self.items[item_id].public_path = Some(parent_name);
                    }
                }
                None => {
                    self.items[item_id].public_path = Some(symbol!(""));
                }
            }
        }

        // Normalize all visibilities.
        for item_id in self.items.indices() {
            fn resolve_visibility(
                tree: &mut BuilderModuleTree,
                within: BuilderItemId,
                fetch: impl Fn(&mut BuilderModuleTree) -> &mut BuilderVisibility,
            ) {
                let vis = fetch(tree);

                if !matches!(vis, BuilderVisibility::PubInUnresolved(_)) {
                    return;
                }

                let BuilderVisibility::PubInUnresolved(path) =
                    mem::replace(vis, BuilderVisibility::Pub)
                else {
                    return;
                };

                let Ok(target) = ModuleTreeVisibilityCx(tree).resolve_visibility_target(
                    BuilderItemId::ROOT,
                    within,
                    &path,
                ) else {
                    // (leave the visibility as `pub`)
                    return;
                };

                *fetch(tree) = BuilderVisibility::PubInResolved(target);
            }

            for use_idx in 0..self.items[item_id].direct_uses.len() {
                resolve_visibility(&mut self, item_id, |tree| {
                    &mut tree.items[item_id].direct_uses[use_idx].visibility
                });
            }

            for use_idx in 0..self.items[item_id].glob_uses.len() {
                resolve_visibility(&mut self, item_id, |tree| {
                    &mut tree.items[item_id].glob_uses[use_idx].visibility
                });
            }
        }

        // Resolve each item's use paths.
        for item_id in self.items.indices() {
            for use_idx in 0..self.items[item_id].direct_uses.len() {
                _ = ModuleTreeSolverCx(&mut self).stash_path(
                    item_id,
                    |tree| &mut tree.0.items[item_id].direct_uses[use_idx].target,
                    None,
                );
            }

            for use_idx in 0..self.items[item_id].glob_uses.len() {
                _ = ModuleTreeSolverCx(&mut self).stash_path(
                    item_id,
                    |tree| &mut tree.0.items[item_id].glob_uses[use_idx].target,
                    Some(ItemCategoryUse::GlobUseTarget),
                );
            }
        }

        // Create a graph of frozen items.
        let mut out_items = IndexVec::new();

        for item in &self.items {
            out_items.push(Obj::new(
                Item {
                    krate,
                    direct_parent: item.direct_parent.map(|idx| out_items[idx]),
                    category: item.category,
                    name: item.name,
                    path: item.public_path.unwrap(),
                    direct_uses: LateInit::uninit(),
                    glob_uses: LateInit::uninit(),
                    attrs: LateInit::uninit(),
                    kind: LateInit::uninit(),
                },
                s,
            ));
        }

        for (idx, in_module) in self.items.iter().enumerate() {
            let direct_uses = in_module
                .direct_uses
                .iter()
                .filter_map(|(name, item)| {
                    Some((
                        *name,
                        DirectUse {
                            visibility: match item.visibility {
                                BuilderVisibility::Pub => Visibility::Pub,
                                BuilderVisibility::PubInResolved(module) => {
                                    Visibility::PubIn(out_items[module])
                                }
                                BuilderVisibility::PubInUnresolved(_) => unreachable!(),
                            },
                            target: match item.target {
                                CachedPath::Ignore => return None,
                                CachedPath::Unresolved(_) => unreachable!(),
                                CachedPath::Resolved(target) => out_items[target],
                            },
                            is_direct_child: item.is_direct_child,
                        },
                    ))
                })
                .collect();

            let glob_uses = in_module
                .glob_uses
                .iter()
                .filter_map(|item| {
                    Some(GlobUse {
                        span: item.span,
                        visibility: match item.visibility {
                            BuilderVisibility::Pub => Visibility::Pub,
                            BuilderVisibility::PubInResolved(target) => {
                                Visibility::PubIn(out_items[target])
                            }
                            BuilderVisibility::PubInUnresolved(_) => unreachable!(),
                        },
                        target: match item.target {
                            CachedPath::Ignore => return None,
                            CachedPath::Unresolved(_) => unreachable!(),
                            CachedPath::Resolved(target) => out_items[target],
                        },
                    })
                })
                .collect();

            LateInit::init(&out_items[idx].r(s).direct_uses, direct_uses);
            LateInit::init(&out_items[idx].r(s).glob_uses, glob_uses);
        }

        LateInit::init(&krate.r(s).root, out_items[BuilderItemId::ROOT]);

        out_items
    }

    fn path(&self, prefix: Symbol, target: BuilderItemId) -> ItemPathFmt {
        ItemPathFmt {
            prefix,
            main_part: self.items[target].public_path.unwrap(),
        }
    }
}

impl ParentResolver for BuilderModuleTree {
    type Item = BuilderItemId;

    fn categorize(&self, def: Self::Item) -> ItemCategory {
        self.items[def].category
    }

    fn direct_parent(&self, def: Self::Item) -> ParentRef<Self::Item> {
        self.items[def].direct_parent
    }
}

fn convert_visibility(self_mod: BuilderItemId, ast: AstVisibility) -> BuilderVisibility {
    match ast.kind {
        AstVisibilityKind::Implicit | AstVisibilityKind::Priv => {
            BuilderVisibility::PubInResolved(self_mod)
        }
        AstVisibilityKind::Pub => BuilderVisibility::Pub,
        AstVisibilityKind::PubIn(path) => BuilderVisibility::PubInUnresolved(path),
    }
}

#[derive(Copy, Clone)]
struct ModuleTreeVisibilityCx<'a>(&'a BuilderModuleTree);

impl ParentResolver for ModuleTreeVisibilityCx<'_> {
    type Item = BuilderItemId;

    fn categorize(&self, def: Self::Item) -> ItemCategory {
        self.0.items[def].category
    }

    fn direct_parent(&self, def: Self::Item) -> ParentRef<Self::Item> {
        self.0.items[def].direct_parent
    }
}

impl VisibilityResolver for ModuleTreeVisibilityCx<'_> {}

impl PathResolver for ModuleTreeVisibilityCx<'_> {
    fn path(&self, def: Self::Item) -> ItemPathFmt {
        self.0.path(symbol!("crate"), def)
    }

    fn global_use_count(&mut self, _curr: Self::Item) -> u32 {
        0
    }

    fn global_use_span(&mut self, _curr: Self::Item, _use_idx: u32) -> Span {
        unreachable!()
    }

    fn global_use_target(
        &mut self,
        _vis_ctxt: Self::Item,
        _curr: Self::Item,
        _use_idx: u32,
    ) -> Result<Self::Item, StepLookupError> {
        unreachable!()
    }

    fn lookup_direct(
        &mut self,
        _vis_ctxt: Self::Item,
        curr: Self::Item,
        name: Symbol,
    ) -> Result<Self::Item, StepLookupError> {
        match self.0.items[curr].direct_uses[&name].target {
            CachedPath::Resolved(target) => Ok(target),
            _ => Err(StepLookupError::NotFound),
        }
    }
}

struct ModuleTreeSolverCx<'a>(&'a mut BuilderModuleTree);

impl ParentResolver for ModuleTreeSolverCx<'_> {
    type Item = BuilderItemId;

    fn categorize(&self, def: Self::Item) -> ItemCategory {
        self.0.items[def].category
    }

    fn direct_parent(&self, def: Self::Item) -> ParentRef<Self::Item> {
        self.0.items[def].direct_parent
    }
}

impl PathResolver for ModuleTreeSolverCx<'_> {
    fn path(&self, def: Self::Item) -> ItemPathFmt {
        self.0.path(symbol!("crate"), def)
    }

    fn global_use_count(&mut self, curr: Self::Item) -> u32 {
        self.0.items[curr].glob_uses.len() as u32
    }

    fn global_use_span(&mut self, curr: Self::Item, use_idx: u32) -> Span {
        self.0.items[curr].glob_uses[use_idx as usize].span
    }

    fn global_use_target(
        &mut self,
        vis_ctxt: Self::Item,
        curr: Self::Item,
        use_idx: u32,
    ) -> Result<Self::Item, StepLookupError> {
        let glob = &self.0.items[curr].glob_uses[use_idx as usize];

        match glob.visibility {
            BuilderVisibility::Pub => {
                // (fallthrough)
            }
            BuilderVisibility::PubInResolved(within) => {
                if !self.is_descendant(vis_ctxt, within) {
                    return Err(StepLookupError::NotVisible);
                }
            }
            BuilderVisibility::PubInUnresolved(_) => unreachable!(),
        }

        let Some(target) = self.stash_path(
            curr,
            |tree| &mut tree.0.items[curr].glob_uses[use_idx as usize].target,
            Some(ItemCategoryUse::GlobUseTarget),
        ) else {
            return Err(StepLookupError::NotFound);
        };

        Ok(target)
    }

    fn lookup_direct(
        &mut self,
        vis_ctxt: Self::Item,
        curr: Self::Item,
        name: Symbol,
    ) -> Result<Self::Item, StepLookupError> {
        let Some(target_idx) = self.0.items[curr].direct_uses.get_index_of(&name) else {
            return Err(StepLookupError::NotFound);
        };

        let target = &self.0.items[curr].direct_uses[target_idx];

        match target.visibility {
            BuilderVisibility::Pub => {
                // (fallthrough)
            }
            BuilderVisibility::PubInResolved(within) => {
                if !self.is_descendant(vis_ctxt, within) {
                    return Err(StepLookupError::NotVisible);
                }
            }
            BuilderVisibility::PubInUnresolved(_) => unreachable!(),
        }

        let target = self.stash_path(
            curr,
            |tree| &mut tree.0.items[curr].direct_uses[target_idx].target,
            None,
        );

        match target {
            Some(target) => Ok(target),
            None => Err(StepLookupError::NotFound),
        }
    }
}

impl ModuleTreeSolverCx<'_> {
    fn stash_path(
        &mut self,
        path_owner: BuilderItemId,
        fetch: impl Fn(&mut Self) -> &mut CachedPath,
        for_use: Option<ItemCategoryUse>,
    ) -> Option<BuilderItemId> {
        let path = fetch(self);

        match path {
            CachedPath::Ignore => return None,
            CachedPath::Unresolved(_) => {
                // (fallthrough)
            }
            CachedPath::Resolved(resolved) => return Some(*resolved),
        }

        let CachedPath::Unresolved(path) = mem::replace(path, CachedPath::Ignore) else {
            unreachable!()
        };

        let Ok(target) =
            self.resolve_bare_path_for_use(BuilderItemId::ROOT, path_owner, &path, for_use)
        else {
            // (leave the path as `Ignore`)
            return None;
        };

        *fetch(self) = CachedPath::Resolved(target);

        Some(target)
    }
}
