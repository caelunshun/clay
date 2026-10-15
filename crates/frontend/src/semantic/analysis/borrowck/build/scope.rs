use crate::{
    base::{Session, arena::Obj},
    flags,
    semantic::syntax::{
        FnDef, MirBlockIdx, MirBody, MirLocal, MirLocalIdx, MirOperand, MirOperandMode, MirPlace,
        MirPrettyFmtCx, MirStmt, MirStmtKind, MirStmtSourceInfo, MirTerminator, MirUnwindBehavior,
        SigTy, TyCtxt,
    },
    utils::format::{IndentedFmt, SimpleListFormatGlue, format_list},
};
use index_vec::{IndexSlice, IndexVec, define_index_type};
use smallvec::SmallVec;
use std::fmt::{self, Write as _};

// === Building === //

define_index_type! {
    pub struct MirBuilderScopeIdx = u32;
}

impl fmt::Display for MirBuilderScopeIdx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'scope_{}", self.index())
    }
}

impl MirBuilderScopeIdx {
    // The actual root scope. Does not have locals of its own and never exposed to the user to
    // ensure that returns can be represented as regular breaks.
    const BOOTSTRAP_ENTRY: MirBuilderScopeIdx = MirBuilderScopeIdx { _raw: 0 };

    pub const ENTRY: MirBuilderScopeIdx = MirBuilderScopeIdx { _raw: 1 };
}

define_index_type! {
    struct BranchIdx = u32;
}

pub struct MirScopedBuilder<'tcx> {
    tcx: &'tcx TyCtxt,
    def: Obj<FnDef>,
    body: MirBody,
    scopes: IndexVec<MirBuilderScopeIdx, Scope>,
    debug: Option<MirScopeBodyDebug>,
}

#[derive(Clone)]
pub struct MirScopedOutput {
    pub body: MirBody,
    pub debug: Option<MirScopeBodyDebug>,
}

struct Scope {
    parent: Option<ScopeParent>,
    locals: Vec<ScopeLocal>,
    first_block: MirBlockIdx,
    curr_block: MirBlockIdx,
    curr_unwind_block: MirBlockIdx,
}

#[derive(Copy, Clone)]
struct ScopeLocal {
    mir_idx: MirLocalIdx,
    unwind_on_scope_drop_panic: Option<MirBlockIdx>,
}

#[derive(Copy, Clone)]
struct ScopeParent {
    target: MirBuilderScopeIdx,
    returns_to: MirBlockIdx,
    last_local: usize,
}

/// Machinery
impl<'tcx> MirScopedBuilder<'tcx> {
    pub fn new(tcx: &'tcx TyCtxt, def: Obj<FnDef>) -> Self {
        let s = &tcx.session;

        let body = {
            let mut body = MirBody::default();

            body.locals.push(MirLocal {
                ty: *def.r(s).ret_ty,
            });

            for arg in def.r(s).args.r(s) {
                body.locals.push(MirLocal { ty: arg.ty });
            }

            body
        };

        let mut this = Self {
            tcx,
            def,
            body,
            scopes: IndexVec::new(),
            debug: flags::should_print_mir_scopes().then(MirScopeBodyDebug::default),
        };

        let last_unwind_block = this
            .body
            .cfg
            .create_block_with_terminator(MirTerminator::UnwindResume);

        assert_eq!(
            this.scopes.push(Scope {
                parent: None,
                locals: Vec::new(),
                first_block: this.body.entry,
                curr_block: this.body.entry,
                curr_unwind_block: last_unwind_block,
            }),
            MirBuilderScopeIdx::BOOTSTRAP_ENTRY
        );

        assert_eq!(
            this.push_scope(MirBuilderScopeIdx::BOOTSTRAP_ENTRY),
            MirBuilderScopeIdx::ENTRY
        );

        this
    }

    pub fn session(&self) -> &'tcx Session {
        &self.tcx.session
    }

    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    pub fn def(&self) -> Obj<FnDef> {
        self.def
    }

    pub fn body(&self) -> &MirBody {
        &self.body
    }

    pub fn body_pretty(&self) -> MirPrettyFmtCx<'_> {
        MirPrettyFmtCx::new(self.tcx, &self.body)
    }

    fn push_debug_ext(
        &mut self,
        f: impl FnOnce(
            &mut MirScopeBodyDebug,
            &IndexSlice<MirBuilderScopeIdx, [Scope]>,
            MirPrettyFmtCx<'_>,
        ),
    ) {
        if let Some(debug) = &mut self.debug {
            f(
                debug,
                &self.scopes,
                MirPrettyFmtCx::new(self.tcx, &self.body),
            );
        }
    }

    fn push_debug(&mut self, f: impl FnOnce(&mut MirScopeBodyDebug, MirPrettyFmtCx<'_>)) {
        self.push_debug_ext(|debug, _scopes, cx| f(debug, cx));
    }

    fn push_debug_bb_indicator(&mut self, scope: MirBuilderScopeIdx) {
        self.push_debug_ext(|debug, scopes, cx| {
            debug.push_indent(scope, -2);
            debug.push_prose(
                scope,
                format_args!("{}:", cx.wrap(scopes[scope].curr_block)),
            );
            debug.push_indent(scope, 2);
        });
    }

    /// Allocates a local in a scope, which is live for all descendant scopes.
    #[track_caller]
    #[must_use]
    pub fn push_local(&mut self, scope: MirBuilderScopeIdx, info: MirLocal) -> MirLocalIdx {
        let mir_idx = self.body.locals.push(info);

        let unwind_on_scope_drop_panic = self.requires_drop(info.ty).then(|| {
            let continue_unwind_bb = self.scopes[scope].curr_unwind_block;

            let drop_self_unwind_bb =
                self.body
                    .cfg
                    .create_block_with_terminator(MirTerminator::EnsureDropped {
                        place: MirPlace::new(self.tcx, mir_idx, []),
                        target: continue_unwind_bb,
                        unwind: MirUnwindBehavior::DoublePanic,
                    });

            self.scopes[scope].curr_unwind_block = drop_self_unwind_bb;

            continue_unwind_bb
        });

        self.scopes[scope].locals.push(ScopeLocal {
            mir_idx,
            unwind_on_scope_drop_panic,
        });

        self.push_statement(
            scope,
            MirStmt {
                source_info: MirStmtSourceInfo::Local,
                kind: MirStmtKind::StorageLive(mir_idx),
            },
        );

        mir_idx
    }

    /// Pushes a regular statement to a scope.
    #[track_caller]
    pub fn push_statement(&mut self, scope: MirBuilderScopeIdx, stmt: MirStmt) {
        self.push_debug(|debug, cx| {
            debug.push_prose(scope, cx.wrap(&stmt));
        });

        self.body.cfg.push_stmt(self.scopes[scope].curr_block, stmt);
    }

    /// Pushes a terminator that branches into some number of child scopes. This can handle diverging
    /// terminators where the successor count is zero and unconditional scope entries where the
    /// successor count is one (e.g. `loop` entries) but cannot handle jumps out of the current
    /// scope, which must be done with [`Self::push_break`] and [`Self::push_continue`].
    #[must_use]
    fn push_branch_dyn(
        &mut self,
        scope: MirBuilderScopeIdx,
        succ_count: usize,
        f: impl FnOnce(&[MirBlockIdx]) -> MirTerminator,
    ) -> SmallVec<[MirBuilderScopeIdx; 2]> {
        let branching_block = self.scopes[scope].curr_block;
        let continue_parent_unwind = self.scopes[scope].curr_unwind_block;

        let returns_to = self.body.cfg.create_block();
        self.scopes[scope].curr_block = returns_to;
        // (BB indicator added in caller)

        let successors = (0..succ_count)
            .map(|_| {
                let first_block = self.body.cfg.create_block();

                let child_scope = self.scopes.push(Scope {
                    parent: Some(ScopeParent {
                        target: scope,
                        returns_to,
                        last_local: self.scopes[scope].locals.len(),
                    }),
                    locals: Vec::new(),
                    first_block,
                    curr_block: first_block,
                    curr_unwind_block: continue_parent_unwind,
                });

                self.push_debug_bb_indicator(child_scope);

                child_scope
            })
            .collect::<SmallVec<[MirBuilderScopeIdx; 2]>>();

        self.body.cfg.init_terminator(
            branching_block,
            f(&successors
                .iter()
                .map(|&scope| self.scopes[scope].first_block)
                .collect::<SmallVec<[MirBlockIdx; 2]>>()),
        );

        successors
    }

    #[must_use]
    fn push_branch_fixed<const N: usize>(
        &mut self,
        scope: MirBuilderScopeIdx,
        f: impl FnOnce([MirBlockIdx; N]) -> MirTerminator,
    ) -> [MirBuilderScopeIdx; N] {
        *self
            .push_branch_dyn(scope, N, |indices| f(*indices.as_array().unwrap()))
            .as_array()
            .unwrap()
    }

    fn push_break_shared(
        &mut self,
        scope: MirBuilderScopeIdx,
        target: MirBuilderScopeIdx,
        next_bb: MirBlockIdx,
    ) {
        // Push `StorageDead` statements.
        #[derive(Copy, Clone)]
        struct IterState {
            scope: MirBuilderScopeIdx,
            last_local: usize,
        }

        let mut next = IterState {
            scope,
            last_local: self.scopes[scope].locals.len(),
        };

        loop {
            let curr = next;

            for idx in (0..curr.last_local).rev() {
                let local = self.scopes[curr.scope].locals[idx];

                if let Some(unwind_on_scope_drop_panic) = local.unwind_on_scope_drop_panic {
                    let scope_start = self.scopes[scope].curr_block;

                    self.push_debug(|debug, cx| {
                        debug.push_prose(
                            scope,
                            format_args!(
                                "ensure-dropped({}) unwind {};",
                                cx.wrap(local.mir_idx),
                                cx.wrap(unwind_on_scope_drop_panic),
                            ),
                        );
                    });

                    let scope_continue = self.body.cfg.create_block();
                    self.scopes[scope].curr_block = scope_continue;
                    self.push_debug_bb_indicator(scope);

                    self.body.cfg.init_terminator(
                        scope_start,
                        MirTerminator::EnsureDropped {
                            place: MirPlace::new(self.tcx, local.mir_idx, []),
                            target: scope_continue,
                            unwind: MirUnwindBehavior::Continue(unwind_on_scope_drop_panic),
                        },
                    );
                }

                self.push_statement(
                    scope,
                    MirStmt {
                        source_info: MirStmtSourceInfo::Break,
                        kind: MirStmtKind::StorageDead(local.mir_idx),
                    },
                );
            }

            if curr.scope == target {
                break;
            }

            let parent = self.scopes[curr.scope].parent.expect("not an ancestor");

            next = IterState {
                scope: parent.target,
                last_local: parent.last_local,
            };
        }

        // Push terminator.
        if let old_curr_bb = self.scopes[scope].curr_block
            && next_bb == old_curr_bb
        {
            // Terminators can never branch directly to themselves. To handle this special case—
            // which should only happen for truly infinite loops (e.g. `loop {}`)!—we introduce a
            // dummy block.
            let spacer_block = self.body.cfg.create_block();

            self.push_debug(|debug, cx| {
                debug.push_prose(
                    scope,
                    format!("goto {};  // Loop spacer", cx.wrap(spacer_block)),
                );
            });

            self.body
                .cfg
                .init_terminator(old_curr_bb, MirTerminator::Goto(spacer_block));

            self.scopes[scope].curr_block = spacer_block;

            self.push_debug_bb_indicator(scope);
        }

        let branching_block = self.scopes[scope].curr_block;

        self.body
            .cfg
            .init_terminator(branching_block, MirTerminator::Goto(next_bb));

        self.push_debug(|debug, cx| {
            debug.push_prose(scope, format_args!("goto {};", cx.wrap(next_bb)));
        });

        let dead_block = self.body.cfg.create_block();
        self.scopes[scope].curr_block = dead_block;
        self.push_debug_bb_indicator(scope);
    }

    /// Finishes the current scope by breaking out to a target which must be an ancestor scope.
    pub fn push_break(&mut self, scope: MirBuilderScopeIdx, target: MirBuilderScopeIdx) {
        self.push_debug(|debug, _cx| {
            debug.push_prose(scope, format_args!("break {target} with {{"));
            debug.push_indent(scope, 4);
        });

        self.push_break_shared(scope, target, self.scopes[scope].parent.unwrap().returns_to);

        self.push_debug(|debug, _cx| {
            debug.push_indent(scope, -4);
            debug.push_prose(scope, "};");
        });
    }

    /// Finishes the current scope by jumping back to the start of an ancestor scope.
    pub fn push_continue(&mut self, scope: MirBuilderScopeIdx, target: MirBuilderScopeIdx) {
        self.push_debug(|debug, _cx| {
            debug.push_prose(scope, format_args!("continue {target} with {{"));
            debug.push_indent(scope, 4);
        });

        self.push_break_shared(scope, target, self.scopes[scope].first_block);

        self.push_debug(|debug, _cx| {
            debug.push_indent(scope, -4);
            debug.push_prose(scope, "};");
        });
    }

    fn push_unwind_terminator(
        &mut self,
        scope: MirBuilderScopeIdx,
        f: impl FnOnce(MirBlockIdx, MirUnwindBehavior) -> MirTerminator,
    ) -> MirBlockIdx {
        let start_bb = self.scopes[scope].curr_block;
        let unwind_bb = self.scopes[scope].curr_unwind_block;

        let continue_bb = self.body.cfg.create_block();
        self.scopes[scope].curr_block = continue_bb;
        // (BB indicator added in caller)

        self.body.cfg.init_terminator(
            start_bb,
            f(continue_bb, MirUnwindBehavior::Continue(unwind_bb)),
        );

        unwind_bb
    }

    // TODO: use this, not the discard rvalue statement.
    pub fn push_drop(&mut self, scope: MirBuilderScopeIdx, place: MirPlace) {
        let unwind =
            self.push_unwind_terminator(scope, |target, unwind| MirTerminator::EnsureDropped {
                place,
                target,
                unwind,
            });

        self.push_debug(|debug, cx| {
            debug.push_prose(
                scope,
                format_args!(
                    "ensure-dropped({}) unwind {};",
                    cx.wrap(place),
                    cx.wrap(unwind)
                ),
            );
        });

        self.push_debug_bb_indicator(scope);
    }

    pub fn push_call(
        &mut self,
        scope: MirBuilderScopeIdx,
        callee: MirOperand,
        args: Box<[MirOperand]>,
        destination: MirPlace,
    ) {
        let args_fmt = self.debug.is_some().then(|| {
            let cx = self.body_pretty();

            format_list(
                args.iter().map(|arg| cx.wrap(*arg)),
                SimpleListFormatGlue::OR_LIST,
            )
        });

        let unwind = self.push_unwind_terminator(scope, |target, unwind| MirTerminator::Call {
            callee,
            args,
            destination,
            target,
            unwind,
        });

        self.push_debug(|debug, cx| {
            debug.push_prose(
                scope,
                format_args!(
                    "{} = call({}, [{}]) unwind {};",
                    cx.wrap(destination),
                    cx.wrap(callee),
                    args_fmt.unwrap(),
                    cx.wrap(unwind),
                ),
            );
        });

        self.push_debug_bb_indicator(scope);
    }

    #[must_use]
    pub fn push_scope(&mut self, scope: MirBuilderScopeIdx) -> MirBuilderScopeIdx {
        let [sub_scope] = self.push_branch_fixed(scope, |[target]| MirTerminator::Goto(target));

        self.push_debug(|debug, _cx| {
            debug.push_child(scope, sub_scope);
            debug.push_prose(scope, ";");
        });
        self.push_debug_bb_indicator(scope);

        sub_scope
    }

    #[must_use]
    pub fn push_switch_dyn(
        &mut self,
        scope: MirBuilderScopeIdx,
        discr: MirOperand,
        constants: &[u64],
    ) -> SmallVec<[MirBuilderScopeIdx; 2]> {
        let children = self.push_branch_dyn(scope, constants.len(), |matchers| {
            MirTerminator::SwitchInt {
                discr,
                constants: Box::from_iter(constants.iter().copied()),
                targets: Box::from_iter(matchers.iter().copied()),
            }
        });

        self.push_debug(|debug, cx| {
            debug.push_prose(scope, format_args!("match {} {{", cx.wrap(discr)));

            for (const_, &child) in constants.iter().zip(&children) {
                debug.push_prose_inline(scope, format_args!("{const_} => "));
                debug.push_child(scope, child);
                debug.push_prose(scope, ",");
            }

            debug.push_prose(scope, "}");
        });

        self.push_debug_bb_indicator(scope);

        children
    }

    #[must_use]
    pub fn push_switch_fixed<const N: usize>(
        &mut self,
        scope: MirBuilderScopeIdx,
        discr: MirOperand,
        constants: [u64; N],
    ) -> [MirBuilderScopeIdx; N] {
        *self
            .push_switch_dyn(scope, discr, &constants)
            .as_array()
            .unwrap()
    }

    pub fn push_return(&mut self, scope: MirBuilderScopeIdx) {
        self.push_break(scope, MirBuilderScopeIdx::ENTRY);
    }

    pub fn push_unreachable(&mut self, scope: MirBuilderScopeIdx) {
        let branching_block = self.scopes[scope].curr_block;

        self.body
            .cfg
            .init_terminator(branching_block, MirTerminator::Unreachable);

        self.push_debug(|debug, _cx| {
            debug.push_prose(scope, "unreachable;");
        });

        let dead_block = self.body.cfg.create_block();
        self.scopes[scope].curr_block = dead_block;
        self.push_debug_bb_indicator(scope);
    }

    pub fn finish(mut self) -> MirScopedOutput {
        assert!(
            self.scopes[MirBuilderScopeIdx::BOOTSTRAP_ENTRY]
                .locals
                .is_empty()
        );

        self.body.cfg.init_terminator(
            self.scopes[MirBuilderScopeIdx::BOOTSTRAP_ENTRY].curr_block,
            MirTerminator::Return,
        );

        if let Some(debug) = &self.debug {
            println!("{debug}");
        }

        self.body.cfg.prune_unreachable(self.body.entry);

        MirScopedOutput {
            body: self.body,
            debug: self.debug,
        }
    }
}

/// Trait detection
impl<'tcx> MirScopedBuilder<'tcx> {
    pub fn operand_mode(&mut self, ty: SigTy) -> MirOperandMode {
        // TODO: detect
        MirOperandMode::Move
    }

    pub fn requires_drop(&mut self, ty: SigTy) -> bool {
        // TODO: detect
        true
    }
}

// === Debug Printing === //

#[derive(Clone, Default)]
pub struct MirScopeBodyDebug {
    annotations: IndexVec<MirBuilderScopeIdx, Vec<MirScopeDebugEntry>>,
}

#[derive(Clone)]
pub enum MirScopeDebugEntry {
    Prose(String),
    Block(MirBuilderScopeIdx),
    IndentBy(i32),
}

impl MirScopeBodyDebug {
    pub fn push_prose_inline(&mut self, scope: MirBuilderScopeIdx, text: impl fmt::Display) {
        if scope.index() >= self.annotations.len() {
            self.annotations.resize(scope.index() + 1, Vec::new());
        }

        if let Some(MirScopeDebugEntry::Prose(existing)) = self.annotations[scope].last_mut() {
            write!(existing, "{text}").unwrap();
        } else {
            self.annotations[scope].push(MirScopeDebugEntry::Prose(text.to_string()));
        }
    }

    pub fn push_prose(&mut self, scope: MirBuilderScopeIdx, text: impl fmt::Display) {
        self.push_prose_inline(scope, format_args!("{text}\n"));
    }

    pub fn push_child(&mut self, scope: MirBuilderScopeIdx, child: MirBuilderScopeIdx) {
        if scope.index() >= self.annotations.len() {
            self.annotations.resize(scope.index() + 1, Vec::new());
        }

        self.annotations[scope].push(MirScopeDebugEntry::Block(child));
    }

    pub fn push_indent(&mut self, scope: MirBuilderScopeIdx, by: i32) {
        if scope.index() >= self.annotations.len() {
            self.annotations.resize(scope.index() + 1, Vec::new());
        }

        self.annotations[scope].push(MirScopeDebugEntry::IndentBy(by));
    }

    fn format_node(&self, scope: MirBuilderScopeIdx, f: &mut IndentedFmt) -> fmt::Result {
        writeln!(f, "{scope}: {{")?;
        f.change_level_now(4)?;

        for entry in &self.annotations[scope] {
            match entry {
                MirScopeDebugEntry::Prose(prose) => {
                    f.write_str(prose)?;
                }
                MirScopeDebugEntry::Block(sub_scope) => {
                    self.format_node(*sub_scope, f)?;
                }
                MirScopeDebugEntry::IndentBy(by) => {
                    f.change_level_subsequent(*by);
                }
            }
        }

        f.change_level_now(-4)?;

        write!(f, "}}")?;

        Ok(())
    }
}

impl fmt::Display for MirScopeBodyDebug {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format_node(MirBuilderScopeIdx::ENTRY, &mut IndentedFmt::new(f))
    }
}
