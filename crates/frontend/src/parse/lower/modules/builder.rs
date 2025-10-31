use crate::{
    base::{
        Diag, LeafDiag, Session,
        syntax::{Span, Symbol},
    },
    parse::{
        ast::{AstSimplePath, AstVisibility, AstVisibilityKind},
        lower::modules::{AnyDef, EmitErrors, ModuleResolver, ParentKind, StepLookupError},
        token::Ident,
    },
    symbol,
    utils::{hash::FxIndexMap, mem::Handle},
};
use derive_where::derive_where;
use index_vec::{IndexVec, define_index_type};
use std::{fmt, mem};

// === Handles === //

pub type BuilderAnyDef<I> = AnyDef<BuilderModuleId, ItemAndOwner<I>>;

define_index_type! {
    pub struct BuilderModuleId = u32;
}

impl BuilderModuleId {
    pub const ROOT: Self = BuilderModuleId { _raw: 0 };
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct ItemAndOwner<I> {
    pub parent: BuilderModuleId,
    pub name: Symbol,
    pub item: I,
}

// === BuilderModuleTree === //

pub struct BuilderModuleTree<I> {
    modules: IndexVec<BuilderModuleId, Module<I>>,
    frozen: bool,
}

struct Module<T> {
    parent: Option<BuilderModuleId>,
    name: Option<Ident>,
    public_path: Option<Symbol>,
    glob_imports: Vec<GlobImport<T>>,
    direct_items: FxIndexMap<Symbol, DirectItem<T>>,
}

struct GlobImport<T> {
    span: Span,
    visibility: Visibility,
    path: CachedPath<T>,
}

struct DirectItem<T> {
    name: Ident,
    visibility: Visibility,
    kind: DirectItemKind<T>,
}

enum DirectItemKind<T> {
    Link(CachedPath<T>),
    Item(T),
}

enum CachedPath<T> {
    Ignore,
    Unresolved(AstSimplePath),
    Resolved(BuilderAnyDef<T>),
}

#[derive(Clone)]
struct Visibility {
    span: Span,
    kind: VisibilityKind,
}

#[derive(Clone)]
enum VisibilityKind {
    Pub,
    PubInResolved(BuilderModuleId),
    PubInUnresolved(AstSimplePath),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
enum MustBeModule {
    Yes,
    No,
}

impl<T> Default for BuilderModuleTree<T> {
    fn default() -> Self {
        Self {
            modules: IndexVec::from_iter([Module {
                parent: None,
                name: None,
                public_path: None,
                glob_imports: Vec::new(),
                direct_items: FxIndexMap::default(),
            }]),
            frozen: false,
        }
    }
}

impl<I: Handle> BuilderModuleTree<I> {
    fn push_direct(&mut self, target: BuilderModuleId, direct: DirectItem<I>) {
        debug_assert!(!self.frozen);

        match self.modules[target].direct_items.entry(direct.name.text) {
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
        debug_assert!(!self.frozen);

        let child = self.modules.push(Module {
            parent: Some(parent),
            name: Some(name),
            public_path: None,
            glob_imports: Vec::new(),
            direct_items: FxIndexMap::default(),
        });

        self.push_direct(
            parent,
            DirectItem {
                name,
                visibility: convert_visibility(parent, visibility),
                kind: DirectItemKind::Link(CachedPath::Resolved(AnyDef::Module(child))),
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
        debug_assert!(!self.frozen);

        self.modules[parent].glob_imports.push(GlobImport {
            span: path.span,
            visibility: convert_visibility(parent, visibility),
            path: CachedPath::Unresolved(path),
        });
    }

    pub fn push_single_use(
        &mut self,
        parent: BuilderModuleId,
        visibility: AstVisibility,
        name: Ident,
        path: AstSimplePath,
    ) {
        debug_assert!(!self.frozen);

        self.push_direct(
            parent,
            DirectItem {
                name,
                visibility: convert_visibility(parent, visibility),
                kind: DirectItemKind::Link(CachedPath::Unresolved(path)),
            },
        )
    }

    pub fn push_item(
        &mut self,
        parent: BuilderModuleId,
        visibility: AstVisibility,
        name: Ident,
        data: I,
    ) {
        debug_assert!(!self.frozen);

        self.push_direct(
            parent,
            DirectItem {
                name,
                visibility: convert_visibility(parent, visibility),
                kind: DirectItemKind::Item(data),
            },
        );
    }

    pub fn module_path(
        &self,
        prefix: Symbol,
        target: BuilderAnyDef<I>,
    ) -> impl 'static + Copy + fmt::Display {
        #[derive(Copy, Clone)]
        struct ModulePathFmt {
            prefix: Symbol,
            main_part: Symbol,
            suffix: Option<Symbol>,
        }

        impl fmt::Display for ModulePathFmt {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let s = &Session::fetch();

                let parts = [
                    self.prefix.as_str(s),
                    self.main_part.as_str(s),
                    self.suffix.map_or("", |sym| sym.as_str(s)),
                ];

                let mut wrote_something = false;

                for part in parts {
                    if part.is_empty() {
                        continue;
                    }

                    if wrote_something {
                        f.write_str("::")?;
                    }

                    f.write_str(part)?;
                    wrote_something = true;
                }

                Ok(())
            }
        }

        let (main_part, suffix) = match target {
            AnyDef::Module(module) => (module, None),
            AnyDef::Item(ItemAndOwner {
                parent,
                name,
                item: _,
            }) => (parent, Some(name)),
        };

        ModulePathFmt {
            prefix,
            main_part: self.modules[main_part].public_path.unwrap(),
            suffix,
        }
    }

    pub fn freeze_and_check(&mut self) {
        debug_assert!(!self.frozen);
        self.frozen = true;

        // Begin by determining public paths for each module.
        // TODO: improve this algorithm.
        for module_id in self.modules.indices() {
            let s = &Session::fetch();

            let mut parts = Vec::new();
            let mut finger = Some(module_id);

            while let Some(curr) = finger {
                let curr = &self.modules[curr];

                if let Some(name) = curr.name {
                    parts.push(name.text.as_str(s));
                } else {
                    debug_assert!(curr.parent.is_none());
                }

                finger = curr.parent;
            }

            parts.reverse();

            self.modules[module_id].public_path = Some(Symbol::new(&parts.join("::")));
        }

        // Next, normalize all visibilities.
        for module_id in self.modules.indices() {
            fn resolve_visibility<I: Handle>(
                tree: &mut BuilderModuleTree<I>,
                within: BuilderModuleId,
                fetch: impl Fn(&mut BuilderModuleTree<I>) -> &mut Visibility,
            ) {
                let vis = &mut fetch(tree).kind;

                if !matches!(vis, VisibilityKind::PubInUnresolved(_)) {
                    return;
                }

                let VisibilityKind::PubInUnresolved(path) = mem::replace(vis, VisibilityKind::Pub)
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

                fetch(tree).kind = VisibilityKind::PubInResolved(target);
            }

            for use_idx in 0..self.modules[module_id].direct_items.len() {
                resolve_visibility(self, module_id, |tree| {
                    &mut tree.modules[module_id].direct_items[use_idx].visibility
                });
            }

            for use_idx in 0..self.modules[module_id].glob_imports.len() {
                resolve_visibility(self, module_id, |tree| {
                    &mut tree.modules[module_id].glob_imports[use_idx].visibility
                });
            }
        }

        // Finally, resolve each module's use paths.
        for module_id in self.modules.indices() {
            for use_idx in 0..self.modules[module_id].direct_items.len() {
                if !matches!(
                    self.modules[module_id].direct_items[use_idx].kind,
                    DirectItemKind::Link(_)
                ) {
                    continue;
                }

                _ = ModuleTreeSolverCx(self).resolve_path(
                    module_id,
                    |tree| {
                        let DirectItemKind::Link(v) =
                            &mut tree.0.modules[module_id].direct_items[use_idx].kind
                        else {
                            unreachable!()
                        };

                        v
                    },
                    MustBeModule::No,
                );
            }

            for use_idx in 0..self.modules[module_id].glob_imports.len() {
                _ = ModuleTreeSolverCx(self).resolve_path(
                    module_id,
                    |tree| &mut tree.0.modules[module_id].glob_imports[use_idx].path,
                    MustBeModule::Yes,
                );
            }
        }
    }
}

fn convert_visibility(self_mod: BuilderModuleId, ast: AstVisibility) -> Visibility {
    let kind = match ast.kind {
        AstVisibilityKind::Implicit | AstVisibilityKind::Priv => {
            VisibilityKind::PubInResolved(self_mod)
        }
        AstVisibilityKind::Pub => VisibilityKind::Pub,
        AstVisibilityKind::PubIn(path) => VisibilityKind::PubInUnresolved(path),
    };

    Visibility {
        span: ast.span,
        kind,
    }
}

#[derive_where(Copy, Clone)]
struct ModuleTreeVisibilityCx<'a, I: Handle>(&'a BuilderModuleTree<I>);

impl<I: Handle> ModuleResolver for ModuleTreeVisibilityCx<'_, I> {
    type Module = BuilderModuleId;
    type Item = ItemAndOwner<I>;

    fn direct_parent(&self, def: Self::Module) -> ParentKind<Self::Module> {
        ParentKind::Real(self.0.modules[def].parent)
    }

    fn path(&self, def: BuilderAnyDef<I>) -> impl 'static + Copy + fmt::Display {
        self.0.module_path(symbol!("crate"), def)
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
        match self.0.modules[curr].direct_items[&name].kind {
            DirectItemKind::Link(CachedPath::Resolved(target)) => Ok(target),
            DirectItemKind::Item(item) => Ok(AnyDef::Item(ItemAndOwner {
                parent: curr,
                name,
                item,
            })),
            _ => Err(StepLookupError::NotFound),
        }
    }
}

struct ModuleTreeSolverCx<'a, I: Handle>(&'a mut BuilderModuleTree<I>);

impl<I: Handle> ModuleResolver for ModuleTreeSolverCx<'_, I> {
    type Module = BuilderModuleId;
    type Item = ItemAndOwner<I>;

    fn direct_parent(&self, def: Self::Module) -> ParentKind<Self::Module> {
        ParentKind::Real(self.0.modules[def].parent)
    }

    fn path(&self, def: AnyDef<Self::Module, Self::Item>) -> impl 'static + Copy + fmt::Display {
        self.0.module_path(symbol!("crate"), def)
    }

    fn global_use_count(&mut self, curr: Self::Module) -> u32 {
        self.0.modules[curr].glob_imports.len() as u32
    }

    fn global_use_target(
        &mut self,
        vis_ctxt: Self::Module,
        curr: Self::Module,
        use_idx: u32,
    ) -> Result<Self::Module, StepLookupError> {
        let glob = &self.0.modules[curr].glob_imports[use_idx as usize];

        match glob.visibility.kind {
            VisibilityKind::Pub => {
                // (fallthrough)
            }
            VisibilityKind::PubInResolved(within) => {
                if !self.is_descendant(vis_ctxt, within) {
                    return Err(StepLookupError::NotVisible);
                }
            }
            VisibilityKind::PubInUnresolved(_) => unreachable!(),
        }

        let Some(target) = self.resolve_path(
            curr,
            |tree| &mut tree.0.modules[curr].glob_imports[use_idx as usize].path,
            MustBeModule::Yes,
        ) else {
            return Err(StepLookupError::NotFound);
        };

        let AnyDef::Module(target) = target else {
            unreachable!();
        };

        Ok(target)
    }

    fn global_use_span(&mut self, curr: Self::Module, use_idx: u32) -> Span {
        self.0.modules[curr].glob_imports[use_idx as usize].span
    }

    fn lookup_direct(
        &mut self,
        vis_ctxt: Self::Module,
        curr: Self::Module,
        name: Symbol,
    ) -> Result<AnyDef<Self::Module, Self::Item>, StepLookupError> {
        let Some(target_idx) = self.0.modules[curr].direct_items.get_index_of(&name) else {
            return Err(StepLookupError::NotFound);
        };

        let target = &self.0.modules[curr].direct_items[target_idx];

        match target.visibility.kind {
            VisibilityKind::Pub => {
                // (fallthrough)
            }
            VisibilityKind::PubInResolved(within) => {
                if !self.is_descendant(vis_ctxt, within) {
                    return Err(StepLookupError::NotVisible);
                }
            }
            VisibilityKind::PubInUnresolved(_) => unreachable!(),
        }

        let target = match target.kind {
            DirectItemKind::Link(_) => self.resolve_path(
                curr,
                |tree| {
                    let DirectItemKind::Link(path) =
                        &mut tree.0.modules[curr].direct_items[target_idx].kind
                    else {
                        unreachable!()
                    };

                    path
                },
                MustBeModule::No,
            ),
            DirectItemKind::Item(item) => Some(AnyDef::Item(ItemAndOwner {
                parent: curr,
                name,
                item,
            })),
        };

        match target {
            Some(target) => Ok(target),
            None => Err(StepLookupError::NotFound),
        }
    }
}

impl<I: Handle> ModuleTreeSolverCx<'_, I> {
    fn resolve_path(
        &mut self,
        path_owner: BuilderModuleId,
        fetch: impl Fn(&mut Self) -> &mut CachedPath<I>,
        must_be_module: MustBeModule,
    ) -> Option<BuilderAnyDef<I>> {
        let path = fetch(self);

        match path {
            CachedPath::Ignore => return None,
            CachedPath::Unresolved(_) => {
                // (fallthrough)
            }
            CachedPath::Resolved(resolved) => return Some(resolved.clone()),
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
