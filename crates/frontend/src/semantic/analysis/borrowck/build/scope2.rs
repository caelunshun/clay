use crate::{
    base::arena::Obj,
    semantic::syntax::{
        Divergence, FnDef, MirBlockIdx, MirBody, MirLocal, MirLocalIdx, MirOperand, MirPlace,
        MirRvalue, MirStmt, MirStmtKind, MirStmtSourceInfo, MirTerminator, MirUnwindBehavior,
        TyCtxt,
    },
    utils::mem::ArenaRc,
};
use bumpalo::Bump;
use index_vec::{IndexVec, define_index_type};
use std::{fmt, rc::Rc};

// === MirScopedBuilder === //

define_index_type! {
    pub struct MirScopeIdx = u32;
}

impl fmt::Display for MirScopeIdx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'scope_{}", self.index())
    }
}

impl MirScopeIdx {
    pub const ENTRY: MirScopeIdx = MirScopeIdx { _raw: 0 };
}

#[derive(Clone)]
pub struct MirScopedBuilder {
    arena: Rc<Bump>,
    scopes: IndexVec<MirScopeIdx, BuilderScope>,
    locals: IndexVec<MirLocalIdx, MirLocal>,
    arg_count: u32,
    debug_comments: bool,
}

#[derive(Clone)]
struct BuilderScope {
    parent: Option<BuilderScopeParent>,
    entries: Vec<BuilderScopeEntry>,
}

#[derive(Copy, Clone)]
struct BuilderScopeParent {
    created_at_sort_idx: u32,
    target: MirScopeIdx,
}

#[derive(Clone)]
struct BuilderScopeEntry {
    sort_idx: u32,
    kind: BuilderScopeKind,
}

#[derive(Clone)]
enum BuilderScopeKind {
    DebugComment(String),
    PushSrcHint(MirStmtSourceInfo),
    PopSrcHint,
    CreateLocal(MirLocalIdx),
    Assign(ArenaRc<ScopeEntryAssign>),
    Break(MirScopeIdx),
    Continue(MirScopeIdx),
    Call(ArenaRc<ScopeEntryCall>),
    Scope(MirScopeIdx),
    If(ArenaRc<ScopeEntryIf>),
    Unreachable,
}

#[derive(Clone)]
struct ScopeEntryAssign {
    lhs: MirPlace,
    rhs: MirRvalue,
}

#[derive(Clone)]
struct ScopeEntryCall {
    callee: MirOperand,
    args: Box<[MirOperand]>,
    destination: MirPlace,
}

#[derive(Clone)]
struct ScopeEntryIf {
    discr: MirOperand,
    truthy: Option<MirScopeIdx>,
    falsy: Option<MirScopeIdx>,
}

impl MirScopedBuilder {
    pub fn new(tcx: &TyCtxt, def: Obj<FnDef>) -> Self {
        todo!()
    }

    fn push_entry(&mut self, scope: MirScopeIdx, entry: BuilderScopeKind) {
        let entries = &mut self.scopes[scope].entries;
        let sort_idx = entries.len() as u32;

        entries.push(BuilderScopeEntry {
            sort_idx,
            kind: entry,
        });
    }

    pub fn push_debug_comment(&mut self, scope: MirScopeIdx, text: impl FnOnce() -> String) {
        if self.debug_comments {
            self.push_entry(scope, BuilderScopeKind::DebugComment(text()));
        }
    }

    pub fn push_src_hint(&mut self, scope: MirScopeIdx, info: MirStmtSourceInfo) {
        self.push_entry(scope, BuilderScopeKind::PushSrcHint(info));
    }

    pub fn pop_src_hint(&mut self, scope: MirScopeIdx) {
        self.push_entry(scope, BuilderScopeKind::PopSrcHint);
    }

    #[must_use]
    pub fn push_local(
        &mut self,
        scope: MirScopeIdx,
        in_scope: MirScopeIdx,
        descriptor: MirLocal,
    ) -> MirLocalIdx {
        // Figure out the hoisting index.
        let sort_idx = 'create: {
            if scope == in_scope {
                break 'create self.scopes[scope].entries.len() as u32;
            }

            let mut curr = scope;

            loop {
                let Some(parent) = self.scopes[curr].parent else {
                    panic!("can only push locals to ancestor scopes");
                };

                if parent.target == in_scope {
                    break 'create parent.created_at_sort_idx;
                }

                curr = parent.target;
            }
        };

        let local = self.locals.push(descriptor);

        self.scopes[in_scope].entries.push(BuilderScopeEntry {
            sort_idx,
            kind: BuilderScopeKind::CreateLocal(local),
        });

        local
    }

    pub fn push_assign(&mut self, scope: MirScopeIdx, lhs: MirPlace, rhs: MirRvalue) {
        self.push_entry(
            scope,
            BuilderScopeKind::Assign(ArenaRc::new(
                self.arena.clone(),
                ScopeEntryAssign { lhs, rhs },
            )),
        );
    }

    pub fn push_break(&mut self, scope: MirScopeIdx, destination: MirScopeIdx) {
        self.push_entry(scope, BuilderScopeKind::Break(destination));
    }

    pub fn push_continue(&mut self, scope: MirScopeIdx, destination: MirScopeIdx) {
        self.push_entry(scope, BuilderScopeKind::Continue(destination));
    }

    pub fn push_return(&mut self, scope: MirScopeIdx) {
        self.push_break(scope, MirScopeIdx::ENTRY);
    }

    pub fn push_call(
        &mut self,
        scope: MirScopeIdx,
        destination: MirPlace,
        callee: MirOperand,
        args: impl IntoIterator<Item = MirOperand>,
    ) {
        let args = args.into_iter().collect();

        self.push_entry(
            scope,
            BuilderScopeKind::Call(ArenaRc::new(
                self.arena.clone(),
                ScopeEntryCall {
                    callee,
                    args,
                    destination,
                },
            )),
        );
    }

    #[must_use]
    fn create_child_scope(&mut self, scope: MirScopeIdx) -> MirScopeIdx {
        let created_at_sort_idx = self.scopes[scope].entries.len() as u32;

        self.scopes.push(BuilderScope {
            parent: Some(BuilderScopeParent {
                created_at_sort_idx,
                target: scope,
            }),
            entries: Vec::new(),
        })
    }

    #[must_use]
    pub fn push_scope(&mut self, scope: MirScopeIdx) -> MirScopeIdx {
        let child = self.create_child_scope(scope);
        self.push_entry(scope, BuilderScopeKind::Scope(child));
        child
    }

    #[must_use]
    pub fn push_if_true(&mut self, scope: MirScopeIdx, discr: MirOperand) -> MirScopeIdx {
        let truthy = self.create_child_scope(scope);

        self.push_entry(
            scope,
            BuilderScopeKind::If(ArenaRc::new(
                self.arena.clone(),
                ScopeEntryIf {
                    discr,
                    truthy: Some(truthy),
                    falsy: None,
                },
            )),
        );

        truthy
    }

    #[must_use]
    pub fn push_if_false(&mut self, scope: MirScopeIdx, discr: MirOperand) -> MirScopeIdx {
        let falsy = self.create_child_scope(scope);

        self.push_entry(
            scope,
            BuilderScopeKind::If(ArenaRc::new(
                self.arena.clone(),
                ScopeEntryIf {
                    discr,
                    truthy: None,
                    falsy: Some(falsy),
                },
            )),
        );

        falsy
    }

    #[must_use]
    pub fn push_if_else(&mut self, scope: MirScopeIdx, discr: MirOperand) -> [MirScopeIdx; 2] {
        let truthy = self.create_child_scope(scope);
        let falsy = self.create_child_scope(scope);

        self.push_entry(
            scope,
            BuilderScopeKind::If(ArenaRc::new(
                self.arena.clone(),
                ScopeEntryIf {
                    discr,
                    truthy: Some(truthy),
                    falsy: Some(falsy),
                },
            )),
        );

        [truthy, falsy]
    }

    pub fn push_unreachable(&mut self, scope: MirScopeIdx) {
        self.push_entry(scope, BuilderScopeKind::Unreachable);
    }
}

// === MIR lowering === //

impl MirScopedBuilder {
    pub fn finish(self) {
        todo!()
    }
}

struct LowerCtxt<'a> {
    tcx: &'a TyCtxt,
    body: MirBody,
    scope_stack: Vec<LowerScope>,
    live_locals: Vec<LiveLocal>,
}

struct LiveLocal {
    drop_unwind_target: Option<MirBlockIdx>,
    idx: MirLocalIdx,
}

struct LowerScope {
    /// The scope in the `MirScopedBuilder` to which this low-level builder scope corresponds.
    id: MirScopeIdx,

    /// The index of the first local owned by this scope.
    first_live_local: usize,

    /// The latest unwind target we'll be chaining against when creating additional local drop
    /// targets.
    unwind_bb: MirBlockIdx,

    /// The entrypoint basic-block for this scope. Used for performing `continue` jumps.
    entry_bb: MirBlockIdx,

    /// The current-most basic block of logic for this scope. May be `None` if branching and we
    /// haven't yet proven that this scope is non-divergent.
    curr_bb: Option<MirBlockIdx>,

    /// The basic block to be initialized with our branching terminator or `None` if we're not
    /// actively creating branch sub-scopes.
    branch_bb: Option<MirBlockIdx>,
}

// Branch management
impl LowerCtxt<'_> {
    fn get_code_head(&mut self, expected_top: MirScopeIdx) -> MirBlockIdx {
        let top = self.scope_stack.last_mut().expect("no active scope");
        assert_eq!(top.id, expected_top);
        assert!(
            top.branch_bb.is_none(),
            "cannot write code to a scope onto which branches are actively being pushed"
        );

        // Unwrap OK: only branching scopes may lack a successor
        top.curr_bb.unwrap()
    }

    fn pop_scope_stack(&mut self) {
        let top = self.scope_stack.pop().unwrap();
        self.live_locals.truncate(top.first_live_local);
    }

    fn begin_branch(&mut self, expected_top: MirScopeIdx) {
        let curr_bb = self.get_code_head(expected_top);

        let top = self.scope_stack.last_mut().unwrap();
        top.curr_bb = None;
        top.branch_bb = Some(curr_bb);
    }

    #[must_use]
    fn add_branch_scope(&mut self, expected_top: MirScopeIdx, id: MirScopeIdx) -> MirBlockIdx {
        let top = self.scope_stack.last().expect("no active scope");
        assert_eq!(top.id, expected_top);
        assert!(
            top.branch_bb.is_some(),
            "must call `begin_branch` before `add_branch_scope`"
        );

        let sub_entry = self.body.cfg.create_block();
        self.scope_stack.push(LowerScope {
            id,
            first_live_local: self.live_locals.len(),
            unwind_bb: top.unwind_bb,
            entry_bb: sub_entry,
            curr_bb: Some(sub_entry),
            branch_bb: None,
        });

        sub_entry
    }

    #[must_use]
    fn end_branch(&mut self, expected_top: MirScopeIdx, terminator: MirTerminator) -> Divergence {
        let top = self.scope_stack.last_mut().expect("no active scope");
        assert_eq!(top.id, expected_top);

        let branch_bb = top
            .branch_bb
            .take()
            .expect("must call `begin_branch` before `end_branch`");

        self.body.cfg.init_terminator(branch_bb, terminator);

        if top.curr_bb.is_some() {
            Divergence::MayDiverge
        } else {
            self.pop_scope_stack();
            Divergence::MustDiverge
        }
    }
}

// Code pushing
impl LowerCtxt<'_> {
    fn finish_unreachable(&mut self, expected_top: MirScopeIdx) {
        let block = self.get_code_head(expected_top);
        self.body
            .cfg
            .init_terminator(block, MirTerminator::Unreachable);

        self.pop_scope_stack();
    }

    fn finish_break_common(
        &mut self,
        expected_top: MirScopeIdx,
        target: MirScopeIdx,
        is_continue: bool,
    ) {
        let mut curr_bb = self.get_code_head(expected_top);

        let mut scope_iter = self.scope_stack.iter_mut().rev();
        let mut local_iter = self.live_locals.iter().enumerate().rev().peekable();

        while let Some(top) = scope_iter.next() {
            let top = &*top;

            // Push drops.
            while let Some(&(live_local_idx, _)) = local_iter.peek()
                && live_local_idx >= top.first_live_local
            {
                let (_, local) = local_iter.next().unwrap();

                if let Some(unwind_if_drop_fails) = local.drop_unwind_target {
                    let successor = self.body.cfg.create_block();

                    self.body.cfg.init_terminator(
                        curr_bb,
                        MirTerminator::EnsureDropped {
                            place: MirPlace::new(self.tcx, local.idx, []),
                            target: successor,
                            unwind: MirUnwindBehavior::Continue(unwind_if_drop_fails),
                        },
                    );

                    curr_bb = successor;
                }

                self.body.cfg.push_stmt(
                    curr_bb,
                    MirStmt {
                        source_info: MirStmtSourceInfo::Break,
                        kind: MirStmtKind::StorageDead(local.idx),
                    },
                );
            }

            // If we've reached our target block, initialize the terminator.
            if top.id != target {
                continue;
            }

            match is_continue {
                true => {
                    // This is a `continue`. Jump back to the target's entrypoint.
                    let next_bb = top.entry_bb;

                    if curr_bb == next_bb {
                        // Terminators can never branch directly to themselves. To handle this special case—
                        // which should only happen for truly infinite loops (e.g. `loop {}`)!—we introduce a
                        // dummy block.
                        let spacer_block = self.body.cfg.create_block();

                        self.body
                            .cfg
                            .init_terminator(curr_bb, MirTerminator::Goto(spacer_block));

                        curr_bb = spacer_block;
                    }

                    self.body
                        .cfg
                        .init_terminator(curr_bb, MirTerminator::Goto(next_bb));
                }
                false => {
                    // This is a `break`. Jump to our parent's successor or return from the body.
                    match scope_iter.next() {
                        Some(successor) => {
                            let next_bb = *successor
                                .curr_bb
                                .get_or_insert_with(|| self.body.cfg.create_block());

                            self.body
                                .cfg
                                .init_terminator(curr_bb, MirTerminator::Goto(next_bb));
                        }
                        None => {
                            self.body
                                .cfg
                                .init_terminator(curr_bb, MirTerminator::Return);
                        }
                    }
                }
            }

            self.pop_scope_stack();
            return;
        }

        unreachable!("must break to ancestor");
    }

    fn finish_break(&mut self, expected_top: MirScopeIdx, target: MirScopeIdx) {
        self.finish_break_common(expected_top, target, false);
    }

    fn finish_continue(&mut self, expected_top: MirScopeIdx, target: MirScopeIdx) {
        self.finish_break_common(expected_top, target, true);
    }

    fn push_local(&mut self, expected_top: MirScopeIdx, local: MirLocal, can_omit_drop: bool) {
        todo!()
    }

    fn push_assign(&mut self, expected_top: MirScopeIdx, lhs: MirPlace, rhs: MirRvalue) {
        todo!()
    }

    fn push_call(
        &mut self,
        expected_top: MirScopeIdx,
        destination: MirPlace,
        callee: MirOperand,
        args: Box<[MirOperand]>,
    ) {
        todo!()
    }
}
