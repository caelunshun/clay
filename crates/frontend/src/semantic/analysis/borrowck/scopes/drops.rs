use crate::{
    bool_enum,
    semantic::{
        analysis::borrowck::scopes::CanOmitDrop,
        syntax::{
            MirBlockIdx, MirBody, MirLocalIdx, MirPlace, MirScopeIdx, MirSourceInfo, MirStmt,
            MirStmtKind, MirTerminator, MirTerminatorKind, MirUnwindBehavior, TyCtxt,
        },
    },
};
use clay_core::FastHashMap;
use index_vec::{IndexVec, define_index_type};

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum JumpTarget {
    Return,
    Goto(MirBlockIdx),
}

bool_enum! {
    pub enum CanPreinsertLocals {
        true => Yes;
        false => No;
    }
}

pub struct DropScheduler {
    nodes: IndexVec<DropNodeIdx, DropNode>,
    unwind_routines: FastHashMap<DropNodeIdx, MirBlockIdx>,
    jump_routines: FastHashMap<JumpKey, MirBlockIdx>,
    unwind_fallthrough_bb: Option<MirBlockIdx>,
}

define_index_type! {
    pub struct DropNodeIdx = u32;
}

impl DropNodeIdx {
    pub const ROOT: Self = Self { _raw: 0 };
}

enum DropNode {
    Scope {
        scope: MirScopeIdx,
        extensible: CanPreinsertLocals,
        next: Option<DropNodeIdx>,
    },
    Local {
        local: MirLocalIdx,
        can_omit_drop: CanOmitDrop,
        next: DropNodeIdx,
    },
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
struct JumpKey {
    to_block: JumpTarget,
    all_after: DropNodeIdx,
    until_scope: MirScopeIdx,
}

impl Default for DropScheduler {
    fn default() -> Self {
        Self {
            nodes: IndexVec::from_iter([DropNode::Scope {
                scope: MirScopeIdx::ENTRY,
                extensible: CanPreinsertLocals::No,
                next: None,
            }]),
            unwind_routines: FastHashMap::default(),
            jump_routines: FastHashMap::default(),
            unwind_fallthrough_bb: None,
        }
    }
}

impl DropScheduler {
    pub fn push_scope(
        &mut self,
        scope: MirScopeIdx,
        extensible: CanPreinsertLocals,
        next: DropNodeIdx,
    ) -> DropNodeIdx {
        self.nodes.push(DropNode::Scope {
            scope,
            extensible,
            next: Some(next),
        })
    }

    pub fn push_local_top(
        &mut self,
        local: MirLocalIdx,
        can_omit_drop: CanOmitDrop,
        next: DropNodeIdx,
    ) -> DropNodeIdx {
        self.nodes.push(DropNode::Local {
            local,
            can_omit_drop,
            next,
        })
    }

    pub fn push_local_after(
        &mut self,
        target: DropNodeIdx,
        local: MirLocalIdx,
        can_omit_drop: CanOmitDrop,
    ) -> DropNodeIdx {
        let DropNode::Scope {
            next: Some(next),
            extensible: CanPreinsertLocals::Yes,
            ..
        } = self.nodes[target]
        else {
            panic!("target must be an extensible scope");
        };

        let new = self.nodes.push(DropNode::Local {
            local,
            can_omit_drop,
            next,
        });

        let DropNode::Scope { next, .. } = &mut self.nodes[target] else {
            unreachable!()
        };

        *next = Some(new);

        new
    }

    pub fn scope_successor(&self, node: DropNodeIdx) -> DropNodeIdx {
        let DropNode::Scope {
            next: Some(next), ..
        } = self.nodes[node]
        else {
            panic!("node must be a non-root scope");
        };

        next
    }

    pub fn request_unwind(
        &mut self,
        mut all_after: DropNodeIdx,
        body: &mut MirBody,
    ) -> MirBlockIdx {
        // Values which don't need drop should not result in the creation of a new basic block.
        loop {
            match self.nodes[all_after] {
                DropNode::Scope {
                    next, extensible, ..
                } => {
                    match extensible {
                        CanPreinsertLocals::No => {
                            match next {
                                Some(next) => {
                                    all_after = next;
                                }
                                None => {
                                    // There is nothing we could possibly need to drop.
                                    return *self
                                        .unwind_fallthrough_bb
                                        .get_or_insert_with(|| body.cfg.create_block());
                                }
                            }
                        }
                        CanPreinsertLocals::Yes => {
                            // Scopes could have drop requests pushed after them.
                            break;
                        }
                    }
                }
                DropNode::Local {
                    can_omit_drop: CanOmitDrop::No,
                    ..
                } => {
                    // We need a drop!
                    break;
                }
                DropNode::Local {
                    can_omit_drop: CanOmitDrop::Yes,
                    next,
                    ..
                } => {
                    all_after = next;
                }
            }
        }

        *self
            .unwind_routines
            .entry(all_after)
            .or_insert_with(|| body.cfg.create_block())
    }

    pub fn request_jump(
        &mut self,
        to_block: JumpTarget,
        all_after: DropNodeIdx,
        until_scope: MirScopeIdx,
        body: &mut MirBody,
    ) -> MirBlockIdx {
        *self
            .jump_routines
            .entry(JumpKey {
                to_block,
                // N.B. cannot normalize `all_after` because we have to insert `StorageDead` stmts.
                all_after,
                until_scope,
            })
            .or_insert_with(|| body.cfg.create_block())
    }

    pub fn unwind_fallthrough_bb(&self) -> Option<MirBlockIdx> {
        self.unwind_fallthrough_bb
    }

    pub fn finish_drop_routines(mut self, tcx: &TyCtxt, body: &mut MirBody) {
        // Freeze all scopes.
        for node in &mut self.nodes {
            match node {
                DropNode::Scope { extensible, .. } => {
                    *extensible = CanPreinsertLocals::No;
                }
                DropNode::Local { .. } => {
                    // (nothing to do)
                }
            }
        }

        // Process jump routines first since they can contribute to requested unwinds.
        for (entry_key, entry_bb) in self.jump_routines.clone() {
            let JumpKey {
                to_block,
                all_after: mut curr_node,
                until_scope,
            } = entry_key;

            let mut curr_bb = entry_bb;

            'build_chain: loop {
                // Process non-dropping operations in a single basic block without registering
                // deduplication breadcrumbs.
                let (local_needing_drop, next_drop_node) = 'build_simple: loop {
                    match self.nodes[curr_node] {
                        DropNode::Scope { scope, next, .. } => {
                            if scope == until_scope {
                                body.cfg.init_terminator(
                                    curr_bb,
                                    MirTerminator {
                                        debug_scope: MirScopeIdx::UNCATEGORIZED,
                                        source_info: MirSourceInfo::Todo,
                                        kind: match to_block {
                                            JumpTarget::Return => MirTerminatorKind::Return,
                                            JumpTarget::Goto(bb) => MirTerminatorKind::Goto(bb),
                                        },
                                    },
                                );

                                break 'build_chain;
                            }

                            curr_node = next.expect("jump never reached the destination scope");
                        }
                        DropNode::Local {
                            local,
                            can_omit_drop,
                            next,
                        } => {
                            if can_omit_drop == CanOmitDrop::No {
                                break 'build_simple (local, next);
                            }

                            body.cfg.push_stmt(
                                curr_bb,
                                MirStmt {
                                    source_info: MirSourceInfo::Todo,
                                    kind: MirStmtKind::StorageDead(local),
                                },
                            );

                            curr_node = next;
                        }
                    }
                };

                // Deduplicate shared jump routines
                let curr_key = JumpKey {
                    to_block,
                    all_after: curr_node,
                    until_scope,
                };

                if curr_key != entry_key {
                    // Did a prior iteration of `finish` or a `request_jump` already create this
                    // jump slide?
                    if let Some(&dedup_entry_bb) = self.jump_routines.get(&curr_key) {
                        body.cfg.init_terminator(
                            curr_bb,
                            MirTerminator {
                                debug_scope: MirScopeIdx::UNCATEGORIZED,
                                source_info: MirSourceInfo::Todo,
                                kind: MirTerminatorKind::Goto(dedup_entry_bb),
                            },
                        );

                        break;
                    }

                    // Otherwise, lay claim to it!
                    self.jump_routines.insert(curr_key, curr_bb);
                }

                // If we're the first to attempt to drop this local, create our drop edge and move
                // forwards.
                let next_bb = body.cfg.create_block();

                let unwind_bb = self.request_unwind(next_drop_node, body);

                body.cfg.init_terminator(
                    curr_bb,
                    MirTerminator {
                        debug_scope: MirScopeIdx::UNCATEGORIZED,
                        source_info: MirSourceInfo::Todo,
                        kind: MirTerminatorKind::EnsureDropped {
                            place: MirPlace::new(tcx, local_needing_drop, []),
                            target: next_bb,
                            unwind: MirUnwindBehavior::Continue(unwind_bb),
                        },
                    },
                );

                curr_node = next_drop_node;
                curr_bb = next_bb;
            }
        }

        // Now, create unwinding operations.
        for (entry_node, mut curr_bb) in self.unwind_routines.clone() {
            let mut curr_node = entry_node;

            'build_chain: loop {
                let (local_needing_drop, next_drop_node) = 'build_simple: loop {
                    match self.nodes[curr_node] {
                        DropNode::Scope {
                            next: Some(next), ..
                        }
                        | DropNode::Local {
                            can_omit_drop: CanOmitDrop::Yes,
                            next,
                            ..
                        } => {
                            curr_node = next;
                        }
                        DropNode::Scope { next: None, .. } => {
                            break 'build_chain;
                        }
                        DropNode::Local {
                            local,
                            can_omit_drop: CanOmitDrop::No,
                            next,
                        } => {
                            break 'build_simple (local, next);
                        }
                    }
                };

                // Deduplicate shared jump routines
                if curr_node != entry_node {
                    if let Some(&dedup_entry_bb) = self.unwind_routines.get(&curr_node) {
                        body.cfg.init_terminator(
                            curr_bb,
                            MirTerminator {
                                debug_scope: MirScopeIdx::UNCATEGORIZED,
                                source_info: MirSourceInfo::Todo,
                                kind: MirTerminatorKind::Goto(dedup_entry_bb),
                            },
                        );

                        break;
                    }

                    // Otherwise, lay claim to it!
                    self.unwind_routines.insert(curr_node, curr_bb);
                }

                // If we're the first to attempt to drop this local, create our drop edge and move
                // forwards.
                let next_bb = body.cfg.create_block();

                body.cfg.init_terminator(
                    curr_bb,
                    MirTerminator {
                        debug_scope: MirScopeIdx::UNCATEGORIZED,
                        source_info: MirSourceInfo::Todo,
                        kind: MirTerminatorKind::EnsureDropped {
                            place: MirPlace::new(tcx, local_needing_drop, []),
                            target: next_bb,
                            unwind: MirUnwindBehavior::DoublePanic,
                        },
                    },
                );

                curr_node = next_drop_node;
                curr_bb = next_bb;
            }
        }
    }
}
