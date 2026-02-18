use crate::{semantic::analysis::ClauseOrigin, utils::hash::FxHashSet};
use std::{fmt, hash, rc::Rc};

/// HRTBs in the RHS position of a type-implements-clause obligation work by instantiating each HRTB
/// parameter as a universally-quantified type. This can cause confusing scenarios when doing things
/// like...
///
/// ```text
/// fn meow<T>(v: T) -> T {
///     v
//  }
///
/// let hrtb = meow::<_>;
/// let funky = hrtb.as::<&'gc dyn for<T> FnOnce<(T,), T>>;
/// hrtb('a');  // Leaked universe :(
/// ```
///
/// Where we're expected to let `char` unify with some universal that only exists within this HRTB
/// context, which is *super* confusing and possibly unsound, although I'm not yet sure how.
///
/// To prevent these types of scenarios, we extend the unify context with the following rules:
///
/// - We have a lattice of `HrtbUniverse`s starting from the `HrtbUniverse::root` and counting up
///   as we spawn child universes.
/// - Every universal belongs to an `HrtbUniverse`.
/// - Every inference variable has a maximum `HrtbUniverse` in which it is willing to mention types.
/// - Unification is denied if an inference variable would be caused to mention a universal beyond
///   its maximum universe. This can be thought of as that inference variable being forced to range
///   over a set of types when it must instead take on a singular concrete type.
///
#[derive(Clone)]
pub struct HrtbUniverse {
    inner: HrtbUniverseInner,
}

#[derive(Clone)]
enum HrtbUniverseInner {
    Root,
    Child(Rc<HrtbUniverseChild>),
}

#[derive(Clone)]
struct HrtbUniverseChild {
    parent: HrtbUniverse,
    info: HrtbUniverseInfo,
}

#[derive(Debug, Clone)]
pub struct HrtbUniverseInfo {
    pub origin: ClauseOrigin,
}

impl fmt::Debug for HrtbUniverse {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut f = f.debug_list();

        for curr in self.ancestors() {
            let entry = match curr.info() {
                Some(info) => info as &dyn fmt::Debug,
                None => &fmt::from_fn(|f| f.write_str("<root>")),
            };

            f.entry(entry);
        }

        f.finish()
    }
}

impl Eq for HrtbUniverse {}

impl PartialEq for HrtbUniverse {
    fn eq(&self, other: &Self) -> bool {
        match (&self.inner, &other.inner) {
            (HrtbUniverseInner::Root, HrtbUniverseInner::Root) => true,
            (HrtbUniverseInner::Child(lhs), HrtbUniverseInner::Child(rhs)) => Rc::ptr_eq(lhs, rhs),
            _ => false,
        }
    }
}

impl hash::Hash for HrtbUniverse {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        match &self.inner {
            HrtbUniverseInner::Root => {
                std::ptr::null::<HrtbUniverseChild>().hash(state);
            }
            HrtbUniverseInner::Child(child) => {
                Rc::as_ptr(child).hash(state);
            }
        }
    }
}

impl HrtbUniverse {
    pub const ROOT: HrtbUniverse = Self {
        inner: HrtbUniverseInner::Root,
    };

    pub const ROOT_REF: &'static HrtbUniverse = &Self::ROOT;

    #[must_use]
    pub fn nest(self, info: HrtbUniverseInfo) -> Self {
        Self {
            inner: HrtbUniverseInner::Child(Rc::new(HrtbUniverseChild { parent: self, info })),
        }
    }

    #[must_use]
    pub fn parent(&self) -> Option<&HrtbUniverse> {
        match &self.inner {
            HrtbUniverseInner::Root => None,
            HrtbUniverseInner::Child(child) => Some(&child.parent),
        }
    }

    #[must_use]
    pub fn is_root(&self) -> bool {
        self == HrtbUniverse::ROOT_REF
    }

    #[must_use]
    pub fn ancestors(&self) -> HrtbUniverseAncestors<'_> {
        HrtbUniverseAncestors { iter: Some(self) }
    }

    #[must_use]
    pub fn info(&self) -> Option<&HrtbUniverseInfo> {
        match &self.inner {
            HrtbUniverseInner::Root => None,
            HrtbUniverseInner::Child(child) => Some(&child.info),
        }
    }

    #[must_use]
    pub fn is_leq_than(&self, other: &HrtbUniverse) -> bool {
        other.ancestors().any(|v| v == self)
    }

    #[must_use]
    pub fn min<'a>(&'a self, other: &'a HrtbUniverse) -> &'a HrtbUniverse {
        let ancestors = self
            .ancestors()
            .filter(|v| !v.is_root())
            .collect::<FxHashSet<_>>();

        other
            .ancestors()
            .find(|v| ancestors.contains(v))
            .unwrap_or(HrtbUniverse::ROOT_REF)
    }
}

#[derive(Clone)]
pub struct HrtbUniverseAncestors<'a> {
    iter: Option<&'a HrtbUniverse>,
}

impl<'a> Iterator for HrtbUniverseAncestors<'a> {
    type Item = &'a HrtbUniverse;

    fn next(&mut self) -> Option<Self::Item> {
        let curr = self.iter?;
        self.iter = curr.parent();
        Some(curr)
    }
}
