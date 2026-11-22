use crate::semantic::{
    infer::{
        ClauseCx, Promise, PromiseResolutionQueue, ReAndReUnifyError, ReConstraintOrder,
        RePermissionFlags, UnifyCxMode, unify::regions::graph::RegionRelationGraph,
    },
    syntax::{InferReVar, Re, RelationMode, UniversalReVar, UniversalReVarSourceInfo},
};
use index_vec::IndexVec;

// === ReUnifyTracker === //

#[derive(Clone)]
pub struct ReUnifyTracker<'sess> {
    universals: IndexVec<UniversalReVar, UniversalReVarSourceInfo>,
    relations: Option<RegionRelationGraph<'sess>>,
}

impl<'sess> ReUnifyTracker<'sess> {
    pub fn new(mode: UnifyCxMode) -> Self {
        Self {
            universals: IndexVec::new(),
            relations: match mode {
                UnifyCxMode::RegionBlind => None,
                UnifyCxMode::RegionAware => Some(RegionRelationGraph::default()),
            },
        }
    }

    pub fn mode(&self) -> UnifyCxMode {
        match self.relations.is_some() {
            true => UnifyCxMode::RegionAware,
            false => UnifyCxMode::RegionBlind,
        }
    }

    pub fn fresh_universal(&mut self, src_info: UniversalReVarSourceInfo) -> UniversalReVar {
        self.universals.push(src_info)
    }

    pub fn lookup_universal_src_info(&self, var: UniversalReVar) -> UniversalReVarSourceInfo {
        self.universals[var]
    }

    pub fn fresh_infer(&mut self) -> InferReVar {
        let Some(relations) = &mut self.relations else {
            return InferReVar::ERASED;
        };

        relations.fresh_infer()
    }

    pub fn constrain(
        &mut self,
        order: ReConstraintOrder,
        mode: RelationMode,
        lhs: impl IntoIterator<Item = Re>,
        rhs: impl IntoIterator<Item = Re>,
    ) -> Promise<'sess, ReAndReUnifyError> {
        let Some(relations) = &mut self.relations else {
            return Promise::trivial();
        };

        relations.constrain(order, mode, lhs, rhs)
    }

    pub fn permit(
        &mut self,
        mode: RelationMode,
        flags: RePermissionFlags,
        lhs: impl IntoIterator<Item = Re>,
        rhs: impl IntoIterator<Item = Re>,
    ) {
        let Some(relations) = &mut self.relations else {
            return;
        };

        relations.permit(mode, flags, lhs, rhs);
    }

    pub fn verify(&mut self) -> PromiseResolutionQueue<'sess> {
        let mut queue = PromiseResolutionQueue::default();

        let Some(relations) = &mut self.relations else {
            return queue;
        };

        relations.verify(&mut queue, self.universals.len());

        queue
    }

    pub fn graphviz(&self, ccx: &ClauseCx<'_>) -> String {
        if let Some(relations) = &self.relations {
            relations.graphviz(ccx, self.universals.len())
        } else {
            "[relations unavailable]".to_string()
        }
    }
}

// === Tests === //

#[cfg(test)]
mod tests {
    use crate::{
        base::Session,
        semantic::{
            analysis::TyCtxt,
            infer::{ClauseCx, ImplCache, RePermissionFlags, UnifyCxMode},
            syntax::{LangItems, RelationMode, UniversalReVarSourceInfo},
        },
    };

    #[test]
    fn perm_idealization() {
        let s = Session::new();
        let _guard = s.clone().bind();

        let s = &s;

        let tcx = TyCtxt {
            session: s,
            impl_cache: &ImplCache::default(),
            lang_items: &LangItems::default(),
        };

        let mut ccx = ClauseCx::new(&tcx, UnifyCxMode::RegionAware);

        let re_a = ccx.fresh_re_universal(UniversalReVarSourceInfo::UnitTest("'a"));
        let re_b = ccx.fresh_re_universal(UniversalReVarSourceInfo::UnitTest("'b"));
        let re_inf = ccx.fresh_re_infer();

        ccx.permit_outlives(
            RelationMode::LhsOntoRhs,
            RePermissionFlags::IDEALIZE_RHS,
            re_a,
            re_inf,
        );

        ccx.oblige_outlives(RelationMode::LhsOntoRhs, re_a, re_b)
            .report_never();

        ccx.verify();
    }
}
