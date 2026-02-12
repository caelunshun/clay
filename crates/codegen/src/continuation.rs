use mir::{BasicBlockId, TypeArgs};
use salsa::Database;
use std::alloc::Layout;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContLayout {
    overall: Layout,
    variants: Vec<ContVariant>,
}

impl ContLayout {
    pub fn overall_layout(&self) -> Layout {
        self.overall
    }

    pub fn variants(&self) -> impl Iterator<Item = &ContVariant> {
        self.variants.iter()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContVariant {
    tag: u32,
    bb: BasicBlockId,
    param_offsets: Vec<usize>,
}

impl ContVariant {
    pub fn tag(&self) -> u32 {
        self.tag
    }

    pub fn target_block(&self) -> BasicBlockId {
        self.bb
    }

    pub fn param_offset(&self, i: usize) -> usize {
        self.param_offsets[i]
    }
}

#[salsa::tracked]
pub fn compute_cont_layout<'db>(
    db: &'db dyn Database,
    mir_cx: mir::Context<'db>,
    func_id: mir::FuncId,
    type_args: TypeArgs<'db>,
) -> ContLayout {
    let func_data = func_id.data(db, mir_cx);

    let mut size = 0;
    let mut align = 1;
    let mut variants = Vec::new();

    for (block_id, block_data) in &func_data.basic_blocks {
        let mut variant_layout = Layout::new::<()>();
        let mut param_offsets = Vec::new();
        for &param_val in block_data.params.as_slice(&func_data.val_lists) {
            let param_ty = func_data.vals[param_val].typ;
            let param_layout = crate::layout::layout_of(db, mir_cx, param_ty, type_args.clone());

            let (new_layout, offset) = variant_layout.extend(param_layout).unwrap();
            variant_layout = new_layout;
            param_offsets.push(offset);
        }

        let i = variants.len().try_into().unwrap();
        variants.push(ContVariant {
            tag: i,
            bb: block_id,
            param_offsets,
        });

        size = size.max(variant_layout.size());
        align = align.max(variant_layout.align());
    }

    ContLayout {
        overall: Layout::from_size_align(size, align).unwrap(),
        variants,
    }
}
