use crate::{
    base::{
        Session,
        arena::Obj,
        syntax::{Span, Symbol},
    },
    semantic::{
        lower::modules::{
            ItemCategory, ItemPathFmt, ParentResolver, PathResolver, StepLookupError,
            VisibilityResolver,
        },
        syntax::Item,
    },
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

    fn parent(&self, def: Self::Item) -> Option<Self::Item> {
        def.r(self.0).parent
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

    fn parent(&self, def: Self::Item) -> Option<Self::Item> {
        def.r(self.0).parent
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
