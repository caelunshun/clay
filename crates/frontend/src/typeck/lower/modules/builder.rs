use crate::{
    base::{
        Diag, LeafDiag, Session,
        arena::{LateInit, Obj},
        syntax::{Span, Symbol},
    },
    parse::{
        ast::{AstSimplePath, AstVisibility, AstVisibilityKind},
        token::Ident,
    },
    symbol,
    typeck::{
        lower::modules::{
            AnyDef, EmitErrors, ModuleResolver, ParentKind, ParentResolver, StepLookupError,
        },
        syntax::{DirectUse, GlobUse, Item, Module, Visibility},
    },
    utils::hash::FxIndexMap,
};
use index_vec::{IndexVec, define_index_type};
use std::{fmt, mem};

// === Handles === //

type BuilderAnyDef = AnyDef<BuilderModuleId, BuilderItemId>;

define_index_type! {
    pub struct BuilderModuleId = u32;
}

impl BuilderModuleId {
    pub const ROOT: Self = BuilderModuleId { _raw: 0 };
}

define_index_type! {
    pub struct BuilderItemId = u32;
}

// === BuilderModuleTree === //

pub struct BuilderModuleTree {
    modules: IndexVec<BuilderModuleId, BuilderModule>,
    items: IndexVec<BuilderItemId, BuilderItem>,
}

struct BuilderModule {
    parent: ParentKind<BuilderModuleId>,
    name: Option<Ident>,
    public_path: Option<Symbol>,
    glob_uses: Vec<BuilderGlobUse>,
    direct_uses: FxIndexMap<Symbol, BuilderDirectUse>,
}

struct BuilderItem {
    parent: BuilderModuleId,
    name: Ident,
    public_path: Option<Symbol>,
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
}

enum CachedPath {
    Ignore,
    Unresolved(AstSimplePath),
    Resolved(BuilderAnyDef),
}

#[derive(Clone)]
enum BuilderVisibility {
    Pub,
    PubInResolved(BuilderModuleId),
    PubInUnresolved(AstSimplePath),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
enum MustBeModule {
    Yes,
    No,
}

impl Default for BuilderModuleTree {
    fn default() -> Self {
        Self {
            modules: IndexVec::from_iter([BuilderModule {
                parent: ParentKind::Real(None),
                name: None,
                public_path: None,
                glob_uses: Vec::new(),
                direct_uses: FxIndexMap::default(),
            }]),
            items: IndexVec::new(),
        }
    }
}

impl BuilderModuleTree {
    fn push_direct(&mut self, target: BuilderModuleId, direct: BuilderDirectUse) {
        match self.modules[target].direct_uses.entry(direct.name.text) {
            indexmap::map::Entry::Vacant(entry) => {
                entry.insert(direct);
            }
            indexmap::map::Entry::Occupied(entry) => {
                Diag::span_err(
                    direct.name.span,
                    format_args!("name `{}` used more than once in module", direct.name.text),
                )
                .child(LeafDiag::span_note(
                    entry.get().name.span,
                    "name previously used here",
                ))
                .emit();
            }
        }
    }

    pub fn push_module(
        &mut self,
        parent: BuilderModuleId,
        visibility: AstVisibility,
        name: Ident,
    ) -> BuilderModuleId {
        let child = self.modules.push(BuilderModule {
            parent: ParentKind::Real(Some(parent)),
            name: Some(name),
            public_path: None,
            glob_uses: Vec::new(),
            direct_uses: FxIndexMap::default(),
        });

        self.push_direct(
            parent,
            BuilderDirectUse {
                name,
                visibility: convert_visibility(parent, visibility),
                target: CachedPath::Resolved(AnyDef::Module(child)),
            },
        );

        child
    }

    pub fn push_glob_use(
        &mut self,
        parent: BuilderModuleId,
        visibility: AstVisibility,
        path: AstSimplePath,
    ) {
        self.modules[parent].glob_uses.push(BuilderGlobUse {
            span: path.span,
            visibility: convert_visibility(parent, visibility),
            target: CachedPath::Unresolved(path),
        });
    }

    pub fn push_single_use(
        &mut self,
        parent: BuilderModuleId,
        visibility: AstVisibility,
        name: Ident,
        path: AstSimplePath,
    ) {
        self.push_direct(
            parent,
            BuilderDirectUse {
                name,
                visibility: convert_visibility(parent, visibility),
                target: CachedPath::Unresolved(path),
            },
        )
    }

    pub fn push_item(
        &mut self,
        parent: BuilderModuleId,
        visibility: AstVisibility,
        name: Ident,
    ) -> BuilderItemId {
        let item = self.items.push(BuilderItem {
            parent,
            name,
            public_path: None,
        });

        self.push_direct(
            parent,
            BuilderDirectUse {
                name,
                visibility: convert_visibility(parent, visibility),
                target: CachedPath::Resolved(AnyDef::Item(item)),
            },
        );

        item
    }

    pub fn freeze_and_check(
        mut self,
        s: &Session,
    ) -> (
        IndexVec<BuilderModuleId, Obj<Module>>,
        IndexVec<BuilderItemId, Obj<Item>>,
    ) {
        // Determine public paths for each module.
        // TODO: improve this algorithm.
        for module_id in self.modules.indices() {
            match self.modules[module_id].parent.as_option() {
                Some(parent) => {
                    let parent_name = self.modules[parent].public_path.unwrap().as_str(s);

                    if parent_name.is_empty() {
                        self.modules[module_id].public_path =
                            Some(self.modules[module_id].name.unwrap().text);
                    } else {
                        self.modules[module_id].public_path = Some(Symbol::new(&format!(
                            "{parent_name}::{}",
                            self.modules[module_id].name.unwrap().text,
                        )));
                    }
                }
                None => {
                    self.modules[module_id].public_path = Some(symbol!(""));
                }
            }
        }

        for item_id in self.items.indices() {
            let parent = self.items[item_id].parent;
            let parent_name = self.modules[parent].public_path.unwrap().as_str(s);

            if parent_name.is_empty() {
                self.items[item_id].public_path = Some(self.items[item_id].name.text);
            } else {
                self.items[item_id].public_path = Some(Symbol::new(&format!(
                    "{parent_name}::{}",
                    self.items[item_id].name.text,
                )));
            }
        }

        // Normalize all visibilities.
        for module_id in self.modules.indices() {
            fn resolve_visibility(
                tree: &mut BuilderModuleTree,
                within: BuilderModuleId,
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

                let target = match ModuleTreeVisibilityCx(tree).lookup(
                    /* root */ BuilderModuleId::ROOT,
                    /* vis_ctxt */ within,
                    /* origin */ within,
                    &path.parts,
                    EmitErrors::Yes,
                ) {
                    Ok(AnyDef::Module(target)) => target,
                    Ok(AnyDef::Item(_)) => {
                        _ = Diag::span_err(
                            path.parts.last().unwrap().span,
                            "must refer to a module",
                        )
                        .emit();

                        // (leave the visibility as `pub`)
                        return;
                    }
                    Err(_) => {
                        // (leave the visibility as `pub`)
                        return;
                    }
                };

                if target == BuilderModuleId::ROOT {
                    // (leave the visibility as `pub`)
                    return;
                }

                if !ModuleTreeVisibilityCx(tree).is_descendant(within, target) {
                    _ = Diag::span_err(path.span, "not an ancestor of the current module").emit();

                    // (leave the visibility as `pub`)
                    return;
                }

                *fetch(tree) = BuilderVisibility::PubInResolved(target);
            }

            for use_idx in 0..self.modules[module_id].direct_uses.len() {
                resolve_visibility(&mut self, module_id, |tree| {
                    &mut tree.modules[module_id].direct_uses[use_idx].visibility
                });
            }

            for use_idx in 0..self.modules[module_id].glob_uses.len() {
                resolve_visibility(&mut self, module_id, |tree| {
                    &mut tree.modules[module_id].glob_uses[use_idx].visibility
                });
            }
        }

        // Resolve each module's use paths.
        for module_id in self.modules.indices() {
            for use_idx in 0..self.modules[module_id].direct_uses.len() {
                _ = ModuleTreeSolverCx(&mut self).resolve_path(
                    module_id,
                    |tree| &mut tree.0.modules[module_id].direct_uses[use_idx].target,
                    MustBeModule::No,
                );
            }

            for use_idx in 0..self.modules[module_id].glob_uses.len() {
                _ = ModuleTreeSolverCx(&mut self).resolve_path(
                    module_id,
                    |tree| &mut tree.0.modules[module_id].glob_uses[use_idx].target,
                    MustBeModule::Yes,
                );
            }
        }

        // Construct a frozen graph.
        let mut out_modules = IndexVec::new();

        for in_module in &self.modules {
            out_modules.push(Obj::new(
                Module {
                    parent: in_module.parent.map(|v| out_modules[v]),
                    name: in_module.name,
                    path: in_module.public_path.unwrap(),
                    direct_uses: LateInit::uninit(),
                    glob_uses: LateInit::uninit(),
                },
                s,
            ));
        }

        let out_items = self
            .items
            .iter()
            .map(|item| {
                Obj::new(
                    Item {
                        parent: out_modules[item.parent],
                        name: item.name,
                        path: item.public_path.unwrap(),
                        kind: LateInit::uninit(),
                    },
                    s,
                )
            })
            .collect::<IndexVec<BuilderItemId, _>>();

        for (idx, in_module) in self.modules.iter().enumerate() {
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
                                    Visibility::PubIn(out_modules[module])
                                }
                                BuilderVisibility::PubInUnresolved(_) => unreachable!(),
                            },
                            target: match item.target {
                                CachedPath::Ignore => return None,
                                CachedPath::Unresolved(_) => unreachable!(),
                                CachedPath::Resolved(target) => match target {
                                    AnyDef::Item(item) => AnyDef::Item(out_items[item]),
                                    AnyDef::Module(module) => AnyDef::Module(out_modules[module]),
                                },
                            },
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
                            BuilderVisibility::PubInResolved(module) => {
                                Visibility::PubIn(out_modules[module])
                            }
                            BuilderVisibility::PubInUnresolved(_) => unreachable!(),
                        },
                        target: match item.target {
                            CachedPath::Ignore => return None,
                            CachedPath::Unresolved(_) => unreachable!(),
                            CachedPath::Resolved(target) => match target {
                                AnyDef::Module(module) => out_modules[module],
                                AnyDef::Item(_) => unreachable!(),
                            },
                        },
                    })
                })
                .collect();

            LateInit::init(&out_modules[idx].r(s).direct_uses, direct_uses);
            LateInit::init(&out_modules[idx].r(s).glob_uses, glob_uses);
        }

        (out_modules, out_items)
    }

    fn path(&self, prefix: Symbol, target: BuilderAnyDef) -> impl 'static + Copy + fmt::Display {
        #[derive(Copy, Clone)]
        struct ModulePathFmt {
            prefix: Symbol,
            main_part: Symbol,
        }

        impl fmt::Display for ModulePathFmt {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let s = &Session::fetch();

                f.write_str(self.prefix.as_str(s))?;

                let main_part = self.main_part.as_str(s);
                if !main_part.is_empty() {
                    f.write_str("::")?;
                    f.write_str(main_part)?;
                }

                Ok(())
            }
        }

        ModulePathFmt {
            prefix,
            main_part: match target {
                AnyDef::Module(module) => self.modules[module].public_path.unwrap(),
                AnyDef::Item(item) => self.items[item].public_path.unwrap(),
            },
        }
    }
}

impl ParentResolver for BuilderModuleTree {
    type Module = BuilderModuleId;

    fn direct_parent(&self, def: Self::Module) -> ParentKind<Self::Module> {
        self.modules[def].parent
    }
}

fn convert_visibility(self_mod: BuilderModuleId, ast: AstVisibility) -> BuilderVisibility {
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
    type Module = BuilderModuleId;

    fn direct_parent(&self, def: Self::Module) -> ParentKind<Self::Module> {
        self.0.modules[def].parent
    }
}

impl ModuleResolver for ModuleTreeVisibilityCx<'_> {
    type Item = BuilderItemId;

    fn path(&self, def: BuilderAnyDef) -> impl 'static + Copy + fmt::Display {
        self.0.path(symbol!("crate"), def)
    }

    fn global_use_count(&mut self, _curr: Self::Module) -> u32 {
        0
    }

    fn global_use_span(&mut self, _curr: Self::Module, _use_idx: u32) -> Span {
        unreachable!()
    }

    fn global_use_target(
        &mut self,
        _vis_ctxt: Self::Module,
        _curr: Self::Module,
        _use_idx: u32,
    ) -> Result<Self::Module, StepLookupError> {
        unreachable!()
    }

    fn lookup_direct(
        &mut self,
        _vis_ctxt: Self::Module,
        curr: Self::Module,
        name: Symbol,
    ) -> Result<AnyDef<Self::Module, Self::Item>, StepLookupError> {
        match self.0.modules[curr].direct_uses[&name].target {
            CachedPath::Resolved(target) => Ok(target),
            _ => Err(StepLookupError::NotFound),
        }
    }
}

struct ModuleTreeSolverCx<'a>(&'a mut BuilderModuleTree);

impl ParentResolver for ModuleTreeSolverCx<'_> {
    type Module = BuilderModuleId;

    fn direct_parent(&self, def: Self::Module) -> ParentKind<Self::Module> {
        self.0.modules[def].parent
    }
}

impl ModuleResolver for ModuleTreeSolverCx<'_> {
    type Item = BuilderItemId;

    fn path(&self, def: AnyDef<Self::Module, Self::Item>) -> impl 'static + Copy + fmt::Display {
        self.0.path(symbol!("crate"), def)
    }

    fn global_use_count(&mut self, curr: Self::Module) -> u32 {
        self.0.modules[curr].glob_uses.len() as u32
    }

    fn global_use_span(&mut self, curr: Self::Module, use_idx: u32) -> Span {
        self.0.modules[curr].glob_uses[use_idx as usize].span
    }

    fn global_use_target(
        &mut self,
        vis_ctxt: Self::Module,
        curr: Self::Module,
        use_idx: u32,
    ) -> Result<Self::Module, StepLookupError> {
        let glob = &self.0.modules[curr].glob_uses[use_idx as usize];

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

        let Some(target) = self.resolve_path(
            curr,
            |tree| &mut tree.0.modules[curr].glob_uses[use_idx as usize].target,
            MustBeModule::Yes,
        ) else {
            return Err(StepLookupError::NotFound);
        };

        let AnyDef::Module(target) = target else {
            unreachable!();
        };

        Ok(target)
    }

    fn lookup_direct(
        &mut self,
        vis_ctxt: Self::Module,
        curr: Self::Module,
        name: Symbol,
    ) -> Result<AnyDef<Self::Module, Self::Item>, StepLookupError> {
        let Some(target_idx) = self.0.modules[curr].direct_uses.get_index_of(&name) else {
            return Err(StepLookupError::NotFound);
        };

        let target = &self.0.modules[curr].direct_uses[target_idx];

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

        let target = self.resolve_path(
            curr,
            |tree| &mut tree.0.modules[curr].direct_uses[target_idx].target,
            MustBeModule::No,
        );

        match target {
            Some(target) => Ok(target),
            None => Err(StepLookupError::NotFound),
        }
    }
}

impl ModuleTreeSolverCx<'_> {
    fn resolve_path(
        &mut self,
        path_owner: BuilderModuleId,
        fetch: impl Fn(&mut Self) -> &mut CachedPath,
        must_be_module: MustBeModule,
    ) -> Option<BuilderAnyDef> {
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

        let Ok(target) = self.lookup(
            BuilderModuleId::ROOT,
            path_owner,
            path_owner,
            &path.parts,
            EmitErrors::Yes,
        ) else {
            // (leave the path as `Ignore`)
            return None;
        };

        match (must_be_module, &target) {
            (MustBeModule::Yes, AnyDef::Item(_)) => {
                Diag::span_err(path.span, "path must resolve to a module");

                // (leave the path as `Ignore`)
                return None;
            }
            (MustBeModule::Yes, AnyDef::Module(_)) | (MustBeModule::No, _) => {
                // (fallthrough)
            }
        }

        *fetch(self) = CachedPath::Resolved(target);

        Some(target)
    }
}
