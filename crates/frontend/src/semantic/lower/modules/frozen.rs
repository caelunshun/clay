use crate::{
    base::{
        Session,
        arena::{LateInit, Obj},
        syntax::{Span, Symbol},
    },
    semantic::{
        lower::modules::{
            ItemCategory, ItemPathFmt, ParentResolver, PathResolver, StepLookupError,
            VisibilityResolver,
        },
        syntax::{Item, TraitItem},
    },
    utils::hash::FxHashSet,
};

// === Visibility Resolver === //

#[derive(Debug, Clone)]
pub struct FrozenVisibilityResolver<'a>(pub &'a Session);

impl VisibilityResolver for FrozenVisibilityResolver<'_> {}

impl ParentResolver for FrozenVisibilityResolver<'_> {
    type Item = Obj<Item>;

    fn categorize(&self, def: Self::Item) -> super::ItemCategory {
        def.r(self.0).category
    }

    fn direct_parent(&self, def: Self::Item) -> Option<Self::Item> {
        def.r(self.0).direct_parent
    }

    fn scope_prelude(&self, def: Self::Item) -> Option<Self::Item> {
        Some(*def.r(self.0).krate.r(self.0).prelude)
    }
}

impl PathResolver for FrozenVisibilityResolver<'_> {
    fn path(&self, def: Self::Item) -> ItemPathFmt {
        let s = self.0;

        def.r(s).display_path(s)
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
        match curr.r(self.0).direct_uses.get(&name) {
            Some(child) if child.is_direct_child => Ok(child.target),
            _ => Err(StepLookupError::NotFound),
        }
    }
}

// === Module Resolver === //

#[derive(Debug, Clone)]
pub struct FrozenModuleResolver<'a>(pub &'a Session);

impl ParentResolver for FrozenModuleResolver<'_> {
    type Item = Obj<Item>;

    fn categorize(&self, def: Self::Item) -> ItemCategory {
        def.r(self.0).category
    }

    fn direct_parent(&self, def: Self::Item) -> Option<Self::Item> {
        def.r(self.0).direct_parent
    }

    fn scope_prelude(&self, def: Self::Item) -> Option<Self::Item> {
        Some(*def.r(self.0).krate.r(self.0).prelude)
    }
}

impl PathResolver for FrozenModuleResolver<'_> {
    fn path(&self, def: Self::Item) -> ItemPathFmt {
        let s = self.0;
        def.r(s).display_path(s)
    }

    fn global_use_count(&mut self, curr: Self::Item) -> u32 {
        curr.r(self.0).glob_uses.len() as u32
    }

    fn global_use_span(&mut self, curr: Self::Item, use_idx: u32) -> Span {
        curr.r(self.0).glob_uses[use_idx as usize].span
    }

    fn global_use_target(
        &mut self,
        vis_ctxt: Self::Item,
        curr: Self::Item,
        use_idx: u32,
    ) -> Result<Self::Item, StepLookupError> {
        let glob_use = &curr.r(self.0).glob_uses[use_idx as usize];

        if !glob_use.visibility.is_visible_to(vis_ctxt, self.0) {
            return Err(StepLookupError::NotVisible);
        }

        Ok(glob_use.target)
    }

    fn lookup_direct(
        &mut self,
        vis_ctxt: Self::Item,
        curr: Self::Item,
        name: Symbol,
    ) -> Result<Self::Item, StepLookupError> {
        let Some(direct_use) = &curr.r(self.0).direct_uses.get(&name) else {
            return Err(StepLookupError::NotFound);
        };

        if !direct_use.visibility.is_visible_to(vis_ctxt, self.0) {
            return Err(StepLookupError::NotVisible);
        }

        Ok(direct_use.target)
    }
}

// === Trait Enumeration === //

pub fn traits_in_single_scope(root: Obj<Item>, s: &Session) -> &FxHashSet<Obj<TraitItem>> {
    if let Some(cached) = LateInit::get(&root.r(s).traits_in_scope) {
        return cached;
    }

    let mut visited_modules = FxHashSet::from_iter([root]);
    let mut discovered_traits = FxHashSet::default();
    let mut stack = vec![root];

    while let Some(top) = stack.pop() {
        for direct in top.r(s).direct_uses.values() {
            if !direct.visibility.is_visible_to(root, s) {
                continue;
            }

            if let Some(trait_) = direct.target.r(s).kind.as_trait() {
                discovered_traits.insert(trait_);
            }
        }

        for glob in &**top.r(s).glob_uses {
            if !glob.visibility.is_visible_to(root, s) {
                continue;
            }

            if !visited_modules.insert(glob.target) {
                continue;
            }

            stack.push(glob.target);
        }
    }

    LateInit::init(&root.r(s).traits_in_scope, discovered_traits)
}
