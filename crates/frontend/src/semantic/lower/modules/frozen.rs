use crate::{
    base::{
        Session,
        arena::Obj,
        syntax::{Span, Symbol},
    },
    semantic::{
        lower::modules::{
            AnyDef, ModulePathFmt, ModuleResolver, ParentKind, ParentResolver, StepLookupError,
            VisibilityResolver,
        },
        syntax::{Item, Module, Visibility},
    },
    symbol,
};

// === Common === //

fn def_display_path(
    def: AnyDef<Obj<Module>, Obj<Item>>,
    s: &Session,
) -> impl 'static + Copy + std::fmt::Display {
    let (krate, main_part) = match def {
        AnyDef::Module(v) => (v.r(s).krate, v.r(s).path),
        AnyDef::Item(v) => (v.r(s).krate, v.r(s).path),
    };

    ModulePathFmt {
        prefix: if krate.r(s).is_local {
            symbol!("crate")
        } else {
            krate.r(s).name
        },
        main_part,
    }
}

// === Visibility Resolver === //

#[derive(Debug, Clone)]
pub struct FrozenVisibilityResolver<'a>(pub &'a Session);

impl VisibilityResolver for FrozenVisibilityResolver<'_> {}

impl ParentResolver for FrozenVisibilityResolver<'_> {
    type Module = Obj<Module>;

    fn direct_parent(&self, def: Self::Module) -> ParentKind<Self::Module> {
        def.r(self.0).parent
    }
}

impl ModuleResolver for FrozenVisibilityResolver<'_> {
    type Item = Obj<Item>;

    fn path(
        &self,
        def: super::AnyDef<Self::Module, Self::Item>,
    ) -> impl 'static + Copy + std::fmt::Display {
        def_display_path(def, self.0)
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
    type Module = Obj<Module>;

    fn direct_parent(&self, def: Self::Module) -> ParentKind<Self::Module> {
        def.r(self.0).parent
    }
}

impl ModuleResolver for FrozenModuleResolver<'_> {
    type Item = Obj<Item>;

    fn path(
        &self,
        def: super::AnyDef<Self::Module, Self::Item>,
    ) -> impl 'static + Copy + std::fmt::Display {
        def_display_path(def, self.0)
    }

    fn global_use_count(&mut self, curr: Self::Module) -> u32 {
        curr.r(self.0).glob_uses.len() as u32
    }

    fn global_use_span(&mut self, curr: Self::Module, use_idx: u32) -> Span {
        curr.r(self.0).glob_uses[use_idx as usize].span
    }

    fn global_use_target(
        &mut self,
        vis_ctxt: Self::Module,
        curr: Self::Module,
        use_idx: u32,
    ) -> Result<Self::Module, StepLookupError> {
        let glob_use = &curr.r(self.0).glob_uses[use_idx as usize];

        match glob_use.visibility {
            Visibility::Pub => {
                // (fallthrough)
            }
            Visibility::PubIn(vis) => {
                if !self.is_descendant(vis_ctxt, vis) {
                    return Err(StepLookupError::NotVisible);
                }
            }
        }

        Ok(glob_use.target)
    }

    fn lookup_direct(
        &mut self,
        vis_ctxt: Self::Module,
        curr: Self::Module,
        name: Symbol,
    ) -> Result<AnyDef<Self::Module, Self::Item>, StepLookupError> {
        let Some(direct_use) = &curr.r(self.0).direct_uses.get(&name) else {
            return Err(StepLookupError::NotFound);
        };

        match direct_use.visibility {
            Visibility::Pub => {
                // (fallthrough)
            }
            Visibility::PubIn(vis) => {
                if !self.is_descendant(vis_ctxt, vis) {
                    return Err(StepLookupError::NotVisible);
                }
            }
        }

        Ok(direct_use.target)
    }
}
