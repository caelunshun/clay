use crate::semantic::syntax::{MirBlockIdx, MirBody, MirLocalIdx, MirScopeIdx};
use clay_core::FastHashMap;
use index_vec::{IndexSlice, IndexVec, define_index_type};

pub struct DropScheduler {
    nodes: IndexVec<DropNodeIdx, DropNode>,
    unwind_routines: FastHashMap<DropNodeIdx, MirBlockIdx>,
    jump_routines: FastHashMap<JumpKey, MirBlockIdx>,
    unwind_fallthrough_bb: MirBlockIdx,
}

define_index_type! {
    pub struct DropNodeIdx = u32;
}

enum DropNode {
    Scope {
        scope: MirScopeIdx,
        next: Option<DropNodeIdx>,
    },
    Local {
        local: MirLocalIdx,
        needs_drop: bool,
        next: Option<DropNodeIdx>,
    },
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
struct JumpKey {
    to_block: MirBlockIdx,
    all_after: DropNodeIdx,
    until_scope: MirScopeIdx,
}

impl DropScheduler {
    pub fn new(unwind_fallthrough_bb: MirBlockIdx) -> Self {
        Self {
            nodes: IndexVec::new(),
            unwind_routines: FastHashMap::default(),
            jump_routines: FastHashMap::default(),
            unwind_fallthrough_bb,
        }
    }

    pub fn push_scope(&mut self, scope: MirScopeIdx, next: Option<DropNodeIdx>) -> DropNodeIdx {
        self.nodes.push(DropNode::Scope { scope, next })
    }

    pub fn push_local_top(
        &mut self,
        local: MirLocalIdx,
        needs_drop: bool,
        next: Option<DropNodeIdx>,
    ) -> DropNodeIdx {
        self.nodes.push(DropNode::Local {
            local,
            needs_drop,
            next,
        })
    }

    pub fn push_local_after(
        &mut self,
        target: DropNodeIdx,
        local: MirLocalIdx,
        needs_drop: bool,
    ) -> DropNodeIdx {
        let DropNode::Scope { next, .. } = self.nodes[target] else {
            panic!("target must be a scope");
        };

        let new = self.nodes.push(DropNode::Local {
            local,
            needs_drop,
            next,
        });

        let DropNode::Scope { next, .. } = &mut self.nodes[target] else {
            unreachable!()
        };

        *next = Some(new);

        new
    }

    pub fn request_unwind(&mut self, all_after: DropNodeIdx, body: &mut MirBody) -> MirBlockIdx {
        Self::request_unwind_inner(&self.nodes, &mut self.unwind_routines, all_after, body)
    }

    fn request_unwind_inner(
        nodes: &IndexSlice<DropNodeIdx, [DropNode]>,
        unwind_routines: &mut FastHashMap<DropNodeIdx, MirBlockIdx>,
        mut all_after: DropNodeIdx,
        body: &mut MirBody,
    ) -> MirBlockIdx {
        // Values which don't need drop should not result in the creation of a new basic block.
        while let DropNode::Local {
            needs_drop: false,
            next: Some(next),
            ..
        } = nodes[all_after]
        {
            all_after = next;
        }

        *unwind_routines
            .entry(all_after)
            .or_insert_with(|| body.cfg.create_block())
    }

    pub fn request_jump(
        &mut self,
        to_block: MirBlockIdx,
        all_after: DropNodeIdx,
        until_scope: MirScopeIdx,
        body: &mut MirBody,
    ) -> MirBlockIdx {
        *self
            .jump_routines
            .entry(JumpKey {
                to_block,
                // N.B. cannot normalize `all_after` because we have to insert storage dead
                // statements.
                all_after,
                until_scope,
            })
            .or_insert_with(|| body.cfg.create_block())
    }
}
