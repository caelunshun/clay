use crate::{
    semantic::{
        lower::modules::{
            AnyDef, ModulePathFmt, ModuleResolver, ParentKind, ParentResolver, StepLookupError,
        },
        syntax::{Item, Module, Visibility},
    },
    base::{
        Session,
        arena::Obj,
        syntax::{Span, Symbol},
    },
    symbol,
};

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
        let s = &self.0;

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
