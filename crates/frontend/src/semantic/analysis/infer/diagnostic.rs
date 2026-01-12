use crate::{
    base::{Diag, ErrorGuaranteed, syntax::Span},
    semantic::{
        analysis::ClauseCx,
        syntax::{InferTyVar, Re, TraitClauseList, TraitParam, TraitSpec, Ty, UniversalReVar},
    },
};
use std::{fmt, iter, rc::Rc};

// === Errors === //

#[derive(Debug, Clone)]
pub struct RecursionLimitReached {
    pub origin: CheckOrigin,
}

impl RecursionLimitReached {
    pub fn emit(&self, ccx: &ClauseCx<'_>) -> ErrorGuaranteed {
        // TODO
        Diag::anon_err(format!("{self:#?}")).emit()
    }
}

#[derive(Debug, Clone)]
pub struct NoTraitImplError {
    pub origin: CheckOrigin,
    pub target: Ty,
    pub spec: TraitSpec,
}

impl NoTraitImplError {
    pub fn emit(&self, ccx: &ClauseCx<'_>) -> ErrorGuaranteed {
        // TODO
        Diag::anon_err(format!("{self:#?}")).emit()
    }
}

#[derive(Debug, Clone)]
pub struct ReAndReUnifyError {
    pub origin: CheckOrigin,
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
    pub origin: CheckOrigin,
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
    RecursiveType(InferTyOccursError),
}

#[derive(Debug, Clone)]
pub struct InferTyOccursError {
    pub var: InferTyVar,
    pub occurs_in: Ty,
}

// === CheckOrigin === //

#[derive(Clone)]
pub struct CheckOrigin(Rc<CheckOriginInner>);

impl fmt::Debug for CheckOrigin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(self.ancestors().map(|v| &v.0.kind))
            .finish()
    }
}

struct CheckOriginInner {
    parent: Option<CheckOrigin>,
    depth: u32,
    kind: CheckOriginKind,
}

#[derive(Debug, Clone)]
pub enum CheckOriginKind {
    /// This obligation is required to type-check the function body.
    FunctionBody {
        at: Span,
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

    NeverErrors,
}

impl CheckOrigin {
    pub fn new(parent: Option<CheckOrigin>, kind: CheckOriginKind) -> Self {
        let depth = parent.as_ref().map_or(0, |v| v.depth() + 1);

        Self(Rc::new(CheckOriginInner {
            parent,
            depth,
            kind,
        }))
    }

    pub fn child(self, kind: CheckOriginKind) -> Self {
        CheckOrigin::new(Some(self), kind)
    }

    pub fn parent(&self) -> Option<&CheckOrigin> {
        self.0.parent.as_ref()
    }

    pub fn ancestors(&self) -> impl Iterator<Item = &CheckOrigin> {
        let mut iter = Some(self);

        iter::from_fn(move || {
            let curr = iter?;
            iter = curr.parent();
            Some(curr)
        })
    }

    pub fn depth(&self) -> u32 {
        self.0.depth
    }

    pub fn kind(&self) -> &CheckOriginKind {
        &self.0.kind
    }
}
