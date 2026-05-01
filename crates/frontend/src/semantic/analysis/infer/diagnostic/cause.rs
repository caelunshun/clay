use crate::{
    base::{Diag, EmissionGuarantee, ErrorGuaranteed, HardDiag, LeafDiag, Level, syntax::Span},
    semantic::analysis::ClauseCx,
};
use std::{cell::Cell, fmt, panic::Location, rc::Rc};

// === ObligeClause === //

#[derive(Clone)]
pub struct ObligeCause {
    kind: ObligeCauseInnerKind,
    created_at: &'static Location<'static>,
}

#[derive(Clone)]
enum ObligeCauseInnerKind {
    Root(ObligeCauseBehavior),
    Nested(Rc<ObligeCauseInnerNested>),
}

struct ObligeCauseInnerNested {
    parent: ObligeCause,
    frame: ObligeCauseFrame,
    depth: u32,
}

#[derive(Copy, Clone)]
pub enum ObligeCauseKind<'a> {
    Root(&'a ObligeCauseBehavior),
    Nested {
        parent: &'a ObligeCause,
        frame: &'a ObligeCauseFrame,
    },
}

#[derive(Debug, Clone)]
pub enum ObligeCauseBehavior {
    /// Errors created in response to this clause origin will be printed during validation.
    Report,

    /// Errors created in response to this clause origin will mark that status in the supplied
    /// [`ClauseOriginProbe`]. These origins can only be used on silent contexts.
    Probe(ObligeCauseProbe),

    /// Errors created in response to this clause origin will be emitted as delay-bug diagnostics.
    /// These diagnostics will not be printed to the user unless no other fatal diagnostics are
    /// emitted during compilation, in which case this diagnostic will be emitted as an internal
    /// compiler error.
    DelayBug,

    /// No errors should ever be reported in response to this clause origin. If they are, raise an
    /// internal compiler error immediately.
    NeverReport,
}

impl fmt::Debug for ObligeCause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut f = f.debug_list();

        f.entries(self.frames().map(|v| v.frame));
        f.entry(&self.behavior());

        f.finish()
    }
}

impl ObligeCause {
    #[track_caller]
    pub fn new(behavior: ObligeCauseBehavior) -> Self {
        Self {
            kind: ObligeCauseInnerKind::Root(behavior),
            created_at: Location::caller(),
        }
    }

    #[track_caller]
    pub fn new_report(frame: ObligeCauseFrame) -> Self {
        Self::new(ObligeCauseBehavior::Report).child(frame)
    }

    #[track_caller]
    pub fn new_probe(probe: ObligeCauseProbe) -> Self {
        Self::new(ObligeCauseBehavior::Probe(probe))
    }

    #[track_caller]
    pub fn new_delay_bug() -> Self {
        Self::new(ObligeCauseBehavior::DelayBug)
    }

    #[track_caller]
    pub fn new_never_report() -> Self {
        Self::new(ObligeCauseBehavior::NeverReport)
    }

    #[track_caller]
    pub fn child(self, frame: ObligeCauseFrame) -> Self {
        let depth = self.depth() + 1;

        Self {
            kind: ObligeCauseInnerKind::Nested(Rc::new(ObligeCauseInnerNested {
                parent: self,
                frame,
                depth,
            })),
            created_at: Location::caller(),
        }
    }

    pub fn kind(&self) -> ObligeCauseKind<'_> {
        match &self.kind {
            ObligeCauseInnerKind::Root(behavior) => ObligeCauseKind::Root(behavior),
            ObligeCauseInnerKind::Nested(nested) => ObligeCauseKind::Nested {
                parent: &nested.parent,
                frame: &nested.frame,
            },
        }
    }

    pub fn own_created_at(&self) -> &'static Location<'static> {
        self.created_at
    }

    pub fn root_created_at(&self) -> &'static Location<'static> {
        let mut curr = self;

        loop {
            match curr.kind() {
                ObligeCauseKind::Root(_) => return curr.created_at,
                ObligeCauseKind::Nested { parent, frame: _ } => {
                    curr = parent;
                }
            }
        }
    }

    pub fn depth(&self) -> u32 {
        match &self.kind {
            ObligeCauseInnerKind::Root(_) => 0,
            ObligeCauseInnerKind::Nested(nested) => nested.depth,
        }
    }

    pub fn behavior(&self) -> &ObligeCauseBehavior {
        let mut curr = self;

        loop {
            match curr.kind() {
                ObligeCauseKind::Root(behavior) => return behavior,
                ObligeCauseKind::Nested { parent, frame: _ } => {
                    curr = parent;
                }
            }
        }
    }

    pub fn frames(&self) -> ObligeCauseFrames<'_> {
        ObligeCauseFrames { next: Some(self) }
    }

    pub fn report<'tcx>(
        &self,
        ccx: &ClauseCx<'tcx>,
        msg: impl FnOnce() -> String,
    ) -> Option<ErrorGuaranteed> {
        match self.behavior() {
            ObligeCauseBehavior::Report => {
                if !ccx.is_silent() {
                    Some(self.build_diag(ccx, msg()).emit())
                } else {
                    None
                }
            }
            ObligeCauseBehavior::Probe(probe) => {
                probe.mark_error();
                None
            }
            ObligeCauseBehavior::DelayBug => {
                if !ccx.is_silent() {
                    eprintln!("Delay bug: {}", self.own_created_at());

                    Some(ErrorGuaranteed::new_unchecked())
                } else {
                    None
                }
            }
            ObligeCauseBehavior::NeverReport => {
                panic!("unreachable clause error printed");
            }
        }
    }

    fn build_diag(&self, ccx: &ClauseCx<'_>, msg: String) -> HardDiag {
        let frames = self.frames().collect::<Vec<_>>();

        // TODO: Fallback span?
        let main_span = frames
            .last()
            .map_or(Span::DUMMY, |v| v.frame.primary_span());

        let mut diag = HardDiag::span_err(main_span, msg);
        Self::append_context(&frames, ccx, &mut diag);

        diag
    }

    fn append_context<E: EmissionGuarantee>(
        frames: &[ObligeCauseFrameRef<'_>],
        ccx: &ClauseCx<'_>,
        diag: &mut Diag<E>,
    ) {
        for (idx, frame) in frames.iter().rev().enumerate() {
            if idx == 0 {
                diag.push_child(LeafDiag::new(
                    Level::Note,
                    format!(
                        "this is necessary because we originally needed to {}",
                        frame.frame.to_do_what(ccx)
                    ),
                ));
            } else {
                diag.push_child(LeafDiag::span_note(
                    frame.frame.primary_span(),
                    format!(
                        "...which then required us to {}",
                        frame.frame.to_do_what(ccx)
                    ),
                ));
            }
        }
    }
}

#[derive(Clone)]
pub struct ObligeCauseFrames<'a> {
    next: Option<&'a ObligeCause>,
}

#[derive(Copy, Clone)]
pub struct ObligeCauseFrameRef<'a> {
    pub full: &'a ObligeCause,
    pub frame: &'a ObligeCauseFrame,
}

impl<'a> Iterator for ObligeCauseFrames<'a> {
    type Item = ObligeCauseFrameRef<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let curr = self.next?;

        match curr.kind() {
            ObligeCauseKind::Root(_) => {
                self.next = None;
                None
            }
            ObligeCauseKind::Nested { parent, frame } => {
                self.next = Some(parent);
                Some(ObligeCauseFrameRef { full: curr, frame })
            }
        }
    }
}

// === ObligeCauseProbe === //

#[derive(Debug, Clone, Default)]
pub struct ObligeCauseProbe(Rc<Cell<bool>>);

impl ObligeCauseProbe {
    pub fn mark_error(&self) {
        self.0.set(true);
    }

    pub fn had_error(&self) -> bool {
        self.0.get()
    }
}

// === ObligeCauseFrame === //

#[derive(Debug, Clone)]
pub enum ObligeCauseFrame {
    Arithmetic {
        op_span: Span,
    },

    Coercion {
        expr_span: Span,
    },

    Pattern {
        pat_span: Span,
    },

    Index {
        target_span: Span,
        index_span: Span,
    },

    ReturnUnit {
        span: Span,
    },

    FunctionCall {
        site_span: Span,
    },

    ForLoopIter {
        iter_span: Span,
    },

    ForLoopPat {
        iter_span: Span,
        pat_span: Span,
    },

    /// This obligation is required to satisfy the requirements of a generic parameter for
    /// well-formedness.
    WfForGenericParam {
        use_span: Span,
        clause_span: Span,
    },

    /// This obligation is required to satisfy the well-formedness requirements of a reference.
    WfForReference {
        pointee: Span,
    },

    WfSuperTrait {
        block: Span,
        clause: Span,
    },

    WfFnDef {
        fn_ty: Span,
    },

    WfHrtb {
        binder_span: Span,
    },

    WfTyAlias {
        span: Span,
    },

    WfTyProjection {
        span: Span,
    },

    /// This obligation is required by a generic parameter's clause list.
    GenericRequirements {
        clause: Span,
    },

    /// This obligation is required to constrain inference variables in an instantiated projection.
    InstantiatedProjection {
        span: Span,
    },

    /// This obligation is required in order for the HRTB variable to meet its clauses.
    HrtbSelection {
        def: Span,
    },
}

impl ObligeCauseFrame {
    pub fn primary_span(&self) -> Span {
        let (ObligeCauseFrame::Arithmetic { op_span: span }
        | ObligeCauseFrame::Coercion { expr_span: span }
        | ObligeCauseFrame::Pattern { pat_span: span }
        | ObligeCauseFrame::Index {
            target_span: _,
            index_span: span,
        }
        | ObligeCauseFrame::ReturnUnit { span }
        | ObligeCauseFrame::FunctionCall { site_span: span }
        | ObligeCauseFrame::ForLoopIter { iter_span: span }
        | ObligeCauseFrame::ForLoopPat {
            iter_span: span,
            pat_span: _,
        }
        | ObligeCauseFrame::WfForGenericParam {
            use_span: span,
            clause_span: _,
        }
        | ObligeCauseFrame::WfForReference { pointee: span }
        | ObligeCauseFrame::WfSuperTrait {
            block: span,
            clause: _,
        }
        | ObligeCauseFrame::WfFnDef { fn_ty: span }
        | ObligeCauseFrame::WfHrtb { binder_span: span }
        | ObligeCauseFrame::WfTyAlias { span }
        | ObligeCauseFrame::WfTyProjection { span }
        | ObligeCauseFrame::GenericRequirements { clause: span }
        | ObligeCauseFrame::InstantiatedProjection { span }
        | ObligeCauseFrame::HrtbSelection { def: span }) = *self;

        span
    }

    pub fn to_do_what(&self, ccx: &ClauseCx<'_>) -> String {
        format!("{self:?}")
    }
}
