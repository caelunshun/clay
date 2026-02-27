use crate::{
    base::{Diag, ErrorGuaranteed, syntax::Span},
    semantic::{
        analysis::{
            ClauseCx, ClauseObligation, HrtbUniverse, TyFolderInfallibleExt, UnboundVarHandlingMode,
        },
        syntax::{
            InferTyVar, Re, SimpleTySet, TraitClauseList, TraitParam, TraitSpec, Ty,
            UniversalReVar, UniversalTyVar,
        },
    },
};
use std::{cell::Cell, fmt, iter, panic::Location, rc::Rc};

// === ClauseErrorSink === //

#[derive(Clone, Default)]
pub enum ClauseErrorSink {
    #[default]
    Report,
    NeverReport(&'static Location<'static>),
    Probe(ClauseErrorProbe),
}

impl ClauseErrorSink {
    pub fn report(&self, error: ClauseError, ccx: &ClauseCx<'_>) {
        match self {
            ClauseErrorSink::Report => {
                error.emit(ccx);
            }
            ClauseErrorSink::NeverReport(_) => {
                unreachable!();
            }
            ClauseErrorSink::Probe(probe) => {
                probe.mark_error();
            }
        }
    }
}

#[derive(Clone, Default)]
pub struct ClauseErrorProbe(Rc<Cell<bool>>);

impl ClauseErrorProbe {
    pub fn mark_error(&self) {
        self.0.set(true);
    }

    pub fn had_error(&self) -> bool {
        self.0.get()
    }
}

// === ClauseOrigin === //

#[derive(Clone)]
pub struct ClauseOrigin {
    inner: Rc<ClauseOriginInner>,
}

impl fmt::Debug for ClauseOrigin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.ancestors()).finish()
    }
}

struct ClauseOriginInner {
    branch: Option<ClauseOriginBranch>,
    sink: ClauseErrorSink,
    depth: u32,
}

pub struct ClauseOriginBranch {
    pub parent: ClauseOrigin,
    pub kind: ClauseOriginKind,
}

#[derive(Debug, Clone)]
pub enum ClauseOriginKind {
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

impl ClauseOrigin {
    pub fn empty(sink: ClauseErrorSink) -> Self {
        Self {
            inner: Rc::new(ClauseOriginInner {
                branch: None,
                depth: 0,
                sink,
            }),
        }
    }

    pub fn empty_report() -> Self {
        thread_local! {
            static EMPTY_REPORT: ClauseOrigin = ClauseOrigin::empty(ClauseErrorSink::Report);
        }

        EMPTY_REPORT.with(|v| v.clone())
    }

    #[track_caller]
    pub fn never_printed() -> Self {
        Self::empty(ClauseErrorSink::NeverReport(Location::caller()))
    }

    pub fn probe(probe: ClauseErrorProbe) -> Self {
        Self::empty(ClauseErrorSink::Probe(probe))
    }

    pub fn root(sink: ClauseErrorSink, kind: ClauseOriginKind) -> Self {
        Self::empty(sink).child(kind)
    }

    pub fn root_report(kind: ClauseOriginKind) -> Self {
        Self::empty_report().child(kind)
    }

    pub fn child(self, kind: ClauseOriginKind) -> Self {
        let sink = self.sink().clone();
        let depth = self.depth() + 1;

        Self {
            inner: Rc::new(ClauseOriginInner {
                branch: Some(ClauseOriginBranch { parent: self, kind }),
                sink,
                depth,
            }),
        }
    }

    pub fn as_branch(&self) -> Option<&ClauseOriginBranch> {
        self.inner.branch.as_ref()
    }

    pub fn parent(&self) -> Option<&ClauseOrigin> {
        self.as_branch().map(|v| &v.parent)
    }

    pub fn kind(&self) -> Option<&ClauseOriginKind> {
        self.as_branch().map(|v| &v.kind)
    }

    pub fn ancestors(&self) -> impl Iterator<Item = &ClauseOriginKind> {
        let mut iter = self.as_branch();

        iter::from_fn(move || {
            let curr = iter?;
            iter = curr.parent.as_branch();
            Some(&curr.kind)
        })
    }

    pub fn depth(&self) -> u32 {
        self.inner.depth
    }

    pub fn sink(&self) -> &ClauseErrorSink {
        &self.inner.sink
    }

    pub fn report(&self, error: ClauseError, ccx: &ClauseCx<'_>) {
        self.sink().report(error, ccx);
    }
}

// === Errors === //

macro_rules! clause_error {
    ($($name:ident),*$(,)?) => {
        #[derive(Debug, Clone)]
        pub enum ClauseError {
            $($name($name),)*
        }

        $(
            impl From<$name> for ClauseError {
                fn from(inner: $name) -> Self {
                    Self::$name(inner)
                }
            }
        )*

        impl ClauseError {
            pub fn emit(&self, ccx: &ClauseCx<'_>) -> Option<ErrorGuaranteed> {
                if ccx.is_silent() {
                    return None;
                }

                Some(self.force_emit(ccx))
            }

            pub fn force_emit(&self, ccx: &ClauseCx<'_>) -> ErrorGuaranteed {
                match self {
                    $(Self::$name(err) => err.emit(ccx),)*
                }
            }
        }
    };
}

clause_error! {
    RecursionLimitReached,
    ObligationUnfulfilled,
    NoTraitImplError,
    ReAndReUnifyError,
    TyAndTyUnifyError,
    TyAndSimpleTySetUnifyError,
}

#[derive(Debug, Clone)]
pub struct RecursionLimitReached {
    pub origin: ClauseOrigin,
}

impl RecursionLimitReached {
    pub fn emit(&self, ccx: &ClauseCx<'_>) -> ErrorGuaranteed {
        // TODO
        Diag::anon_err(format!("{self:#?}")).emit()
    }
}

#[derive(Debug, Clone)]
pub struct ObligationUnfulfilled {
    pub obligation: ClauseObligation,
}

impl ObligationUnfulfilled {
    pub fn emit(&self, ccx: &ClauseCx<'_>) -> ErrorGuaranteed {
        // TODO
        Diag::anon_err(format!("{self:#?}")).emit()
    }
}

#[derive(Debug, Clone)]
pub struct NoTraitImplError {
    pub origin: ClauseOrigin,
    pub target: Ty,
    pub spec: TraitSpec,
}

impl NoTraitImplError {
    pub fn emit(&self, ccx: &ClauseCx<'_>) -> ErrorGuaranteed {
        let mut sub = ccx
            .ucx()
            .substitutor(UnboundVarHandlingMode::NormalizeToRoot);

        let me = Self {
            origin: self.origin.clone(),
            target: sub.fold(self.target),
            spec: sub.fold(self.spec),
        };

        Diag::anon_err(format!("{me:#?}")).emit()
    }
}

#[derive(Debug, Clone)]
pub struct ReAndReUnifyError {
    pub origin: ClauseOrigin,
    pub lhs: Re,
    pub rhs: Re,
    pub requires_var: UniversalReVar,
    pub to_outlive: Re,
}

impl ReAndReUnifyError {
    pub fn emit(&self, ccx: &ClauseCx<'_>) -> ErrorGuaranteed {
        // TODO
        Diag::anon_err(format!("{self:#?}")).emit()
    }
}

#[derive(Debug, Clone)]
pub struct TyAndTyUnifyError {
    pub origin: ClauseOrigin,
    pub origin_lhs: Ty,
    pub origin_rhs: Ty,
    pub culprits: Vec<TyAndTyUnifyCulprit>,
}

impl TyAndTyUnifyError {
    pub fn emit(&self, ccx: &ClauseCx<'_>) -> ErrorGuaranteed {
        // TODO
        Diag::anon_err(format!("{self:#?}")).emit()
    }
}

#[derive(Debug, Clone)]
pub enum TyAndTyUnifyCulprit {
    Types(Ty, Ty),
    ClauseLists(TraitClauseList, TraitClauseList),
    Params(TraitParam, TraitParam),
    Occurs(InferTyOccursError),
    Leaks(InferTyLeaksError),
    NotPermittedSolid(SimpleTySet, Ty),
    NotPermittedFloating(SimpleTySet, SimpleTySet),
    UnifyDenied,
}

#[derive(Debug, Clone)]
pub struct InferTyOccursError {
    pub var: InferTyVar,
    pub occurs_in: Ty,
}

#[derive(Debug, Clone)]
pub struct InferTyLeaksError {
    pub var: InferTyVar,
    pub max_universe: HrtbUniverse,
    pub leaks_universal: UniversalTyVar,
}

#[derive(Debug, Clone)]
pub struct TyAndSimpleTySetUnifyError {
    pub origin: ClauseOrigin,
    pub lhs: Ty,
    pub rhs: SimpleTySet,
}

impl TyAndSimpleTySetUnifyError {
    pub fn emit(&self, ccx: &ClauseCx<'_>) -> ErrorGuaranteed {
        // TODO
        Diag::anon_err(format!("{self:#?}")).emit()
    }
}
