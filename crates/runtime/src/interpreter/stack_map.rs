use crate::{interpreter::stack::Stack, Engine, Module};
use bytecode::{module::FuncData, Local};
use cranelift_entity::SecondaryMap;
use std::alloc::Layout;

/// Cached stack map for a function, mapping `Local`
/// indices to their offset from the start of the stack frame.
#[derive(Debug, Clone)]
pub struct FunctionStackMap {
    pub layout: Layout,
    pub local_offsets: SecondaryMap<Local, u32>,
    pub local_sizes: SecondaryMap<Local, u32>,
}

impl FunctionStackMap {
    pub fn new(func: &FuncData, module: Module, engine: &Engine) -> Self {
        let mut layout = Layout::new::<()>();
        let mut local_offsets = SecondaryMap::default();
        let mut local_sizes = SecondaryMap::default();

        for (local, local_data) in &func.locals {
            let local_type = engine.type_registry.module_mapping[module][local_data.typ];
            let local_layout = engine.type_registry.layouts[local_type].unwrap();

            let (new_layout, offset) = layout.extend(local_layout).unwrap();
            local_offsets[local] = offset.try_into().unwrap();
            local_sizes[local] = local_layout.size().try_into().unwrap();

            layout = new_layout;
        }

        const FRAME_ALIGNMENT: usize = Stack::MAX_ALIGN;

        assert!(
            layout.align() <= FRAME_ALIGNMENT,
            "alignment > {FRAME_ALIGNMENT} for stack-allocated values not yet supported"
        );
        // Size gets rounded up to a multiple of FRAME_ALIGNMENT.
        let layout = Layout::from_size_align(
            layout.size().div_ceil(FRAME_ALIGNMENT) * FRAME_ALIGNMENT,
            layout.align(),
        )
        .unwrap();

        Self {
            layout,
            local_offsets,
            local_sizes,
        }
    }
}
