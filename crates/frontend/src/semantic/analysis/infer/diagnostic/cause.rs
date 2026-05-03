use crate::{
    base::{Diag, ErrorGuaranteed, LeafDiag, Level, arena::Obj, syntax::Span},
    semantic::{
        analysis::ClauseCx,
        syntax::{HrtbBinder, ImplItem, TraitSpec, Ty},
    },
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
    /// [`ObligeCauseProbe`]. These origins can only be used on silent contexts.
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
    pub fn new_empty_report() -> Self {
        Self::new(ObligeCauseBehavior::Report)
    }

    #[track_caller]
    pub fn new_report(frame: ObligeCauseOrigin) -> Self {
        Self::new_empty_report().child(frame.into())
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
                    Some(self.build_diag(ccx, Level::Error, msg()).emit().unwrap())
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
                    Some(
                        self.build_diag(ccx, Level::DelayedBug, msg())
                            .emit()
                            .unwrap(),
                    )
                } else {
                    None
                }
            }
            ObligeCauseBehavior::NeverReport => {
                panic!("unreachable clause error printed");
            }
        }
    }

    fn build_diag(
        &self,
        ccx: &ClauseCx<'_>,
        level: Level,
        msg: String,
    ) -> Diag<Option<ErrorGuaranteed>> {
        let frames = self.frames().collect::<Vec<_>>();

        let main_span = frames
            .last()
            // TODO: Fallback span?
            .map_or(Span::DUMMY, |v| v.frame.unwrap_origin_ref().primary_span());

        let mut diag = Diag::new(level, msg).primary(main_span, "");

        for frame in frames {
            diag.push_child(LeafDiag::new(Level::Note, format!("{:#?}", frame.frame)));
        }

        diag
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
    /// An oblige cause origin, which indicate root-level causes that started this obligation.
    Origin(ObligeCauseOrigin),

    /// An internal step in fulfilling this obligation.
    Step(ObligeCauseStep),
}

impl From<ObligeCauseOrigin> for ObligeCauseFrame {
    fn from(value: ObligeCauseOrigin) -> Self {
        Self::Origin(value)
    }
}

impl From<ObligeCauseStep> for ObligeCauseFrame {
    fn from(value: ObligeCauseStep) -> Self {
        Self::Step(value)
    }
}

impl ObligeCauseFrame {
    pub fn into_origin(self) -> Result<ObligeCauseOrigin, Self> {
        if let ObligeCauseFrame::Origin(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }

    pub fn into_step(self) -> Result<ObligeCauseStep, Self> {
        if let ObligeCauseFrame::Step(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }

    pub fn as_origin(&self) -> Option<&ObligeCauseOrigin> {
        if let ObligeCauseFrame::Origin(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_step(&self) -> Option<&ObligeCauseStep> {
        if let ObligeCauseFrame::Step(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn unwrap_origin(self) -> ObligeCauseOrigin {
        self.into_origin().ok().unwrap()
    }

    pub fn unwrap_step(self) -> ObligeCauseStep {
        self.into_step().ok().unwrap()
    }

    pub fn unwrap_origin_ref(&self) -> &ObligeCauseOrigin {
        self.as_origin().unwrap()
    }

    pub fn unwrap_step_ref(&self) -> &ObligeCauseStep {
        self.as_step().unwrap()
    }
}

#[derive(Debug, Clone)]
pub enum ObligeCauseOrigin {
    HirBodyCheckArithmetic { op_span: Span },
    HirBodyCheckCoercion { expr_span: Span },
    HirBodyCheckPattern { pat_span: Span },
    HirBodyCheckIndex { target_span: Span, index_span: Span },
    HirBodyCheckReturnUnit { span: Span },
    HirBodyCheckFunctionCall { site_span: Span },
    HirBodyCheckForLoopIter { iter_span: Span },
    HirBodyCheckForLoopPat { iter_span: Span, pat_span: Span },
    ImportWfForGenericParam { use_span: Span, clause_span: Span },
    ImportWfForReference { pointee: Span },
    ImportWfFnDef { fn_ty: Span },
    ImportWfHrtb { binder_span: Span },
    ImportWfTyProjection { span: Span },
    HirCheckSuperTrait { block: Span, clause: Span },
}

impl ObligeCauseOrigin {
    pub fn primary_span(&self) -> Span {
        let (ObligeCauseOrigin::HirBodyCheckArithmetic { op_span: span }
        | ObligeCauseOrigin::HirBodyCheckCoercion { expr_span: span }
        | ObligeCauseOrigin::HirBodyCheckPattern { pat_span: span }
        | ObligeCauseOrigin::HirBodyCheckIndex {
            target_span: _,
            index_span: span,
        }
        | ObligeCauseOrigin::HirBodyCheckReturnUnit { span }
        | ObligeCauseOrigin::HirBodyCheckFunctionCall { site_span: span }
        | ObligeCauseOrigin::HirBodyCheckForLoopIter { iter_span: span }
        | ObligeCauseOrigin::HirBodyCheckForLoopPat {
            iter_span: span,
            pat_span: _,
        }
        | ObligeCauseOrigin::ImportWfForGenericParam {
            use_span: span,
            clause_span: _,
        }
        | ObligeCauseOrigin::ImportWfForReference { pointee: span }
        | ObligeCauseOrigin::HirCheckSuperTrait {
            block: span,
            clause: _,
        }
        | ObligeCauseOrigin::ImportWfFnDef { fn_ty: span }
        | ObligeCauseOrigin::ImportWfHrtb { binder_span: span }
        | ObligeCauseOrigin::ImportWfTyProjection { span }) = *self;

        span
    }
}

#[derive(Debug, Clone)]
pub enum ObligeCauseStep {
    ImplInstantiatedClause { lhs: Ty, rhs: TraitSpec },
    ImplUsingInherent { lhs: HrtbBinder, rhs: TraitSpec },
    ImplUsingBlock(Obj<ImplItem>),

    // TODO
    ImportEnvMeetsRequirements { clause: Span },
}
