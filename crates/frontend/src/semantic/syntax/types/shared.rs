use crate::{base::syntax::Symbol, symbol};
use smallvec::{SmallVec, smallvec};

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum ReVariance {
    Invariant,
    Covariant,
    Contravariant,
}

impl ReVariance {
    pub fn rev(self) -> Self {
        match self {
            ReVariance::Invariant => ReVariance::Invariant,
            ReVariance::Covariant => ReVariance::Contravariant,
            ReVariance::Contravariant => ReVariance::Covariant,
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum RelationDirection {
    LhsOntoRhs,
    RhsOntoLhs,
}

impl RelationDirection {
    pub fn kw(self) -> Symbol {
        match self {
            RelationDirection::LhsOntoRhs => symbol!("&shorter"),
            RelationDirection::RhsOntoLhs => symbol!("&longer"),
        }
    }

    #[must_use]
    pub fn to_mode(self) -> RelationMode {
        match self {
            RelationDirection::LhsOntoRhs => RelationMode::LhsOntoRhs,
            RelationDirection::RhsOntoLhs => RelationMode::RhsOntoLhs,
        }
    }

    #[must_use]
    pub fn invert(self) -> RelationDirection {
        match self {
            RelationDirection::LhsOntoRhs => RelationDirection::RhsOntoLhs,
            RelationDirection::RhsOntoLhs => RelationDirection::LhsOntoRhs,
        }
    }

    pub fn adapt<T: Copy>(self, lhs: T, rhs: T) -> (T, T) {
        match self {
            RelationDirection::LhsOntoRhs => (lhs, rhs),
            RelationDirection::RhsOntoLhs => (rhs, lhs),
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum RelationMode {
    LhsOntoRhs,
    RhsOntoLhs,
    Equate,
}

impl RelationMode {
    #[must_use]
    pub fn with_variance(self, variance: ReVariance) -> RelationMode {
        match variance {
            ReVariance::Invariant => RelationMode::Equate,
            ReVariance::Covariant => self,
            ReVariance::Contravariant => self.invert(),
        }
    }

    #[must_use]
    pub fn invert(self) -> RelationMode {
        match self {
            RelationMode::LhsOntoRhs => RelationMode::RhsOntoLhs,
            RelationMode::RhsOntoLhs => RelationMode::LhsOntoRhs,
            RelationMode::Equate => RelationMode::Equate,
        }
    }

    pub fn enumerate<T: Copy>(self, lhs: T, rhs: T) -> SmallVec<[(T, T); 2]> {
        match self {
            RelationMode::LhsOntoRhs => smallvec![(lhs, rhs)],
            RelationMode::RhsOntoLhs => smallvec![(rhs, lhs)],
            RelationMode::Equate => smallvec![(lhs, rhs), (rhs, lhs)],
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum Mutability {
    Not,
    Mut,
}

impl Mutability {
    pub fn adverb(self) -> Symbol {
        match self {
            Mutability::Mut => symbol!("mutably"),
            Mutability::Not => symbol!("immutably"),
        }
    }

    pub fn opt_space_qual(self) -> Symbol {
        match self {
            Mutability::Not => symbol!(""),
            Mutability::Mut => symbol!("mut "),
        }
    }
}

// === SimpleTy === //

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum SimpleTyKind {
    Never,
    Bool,
    Char,
    Int(IntKind),
    Uint(IntKind),
    Float(FloatKind),
    Str,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum IntKind {
    S8,
    S16,
    S32,
    S64,
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum FloatKind {
    S32,
    S64,
}
