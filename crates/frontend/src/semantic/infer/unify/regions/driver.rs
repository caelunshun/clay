use crate::semantic::{
    infer::{
        ClauseCx, Promise, PromiseResolutionQueue, ReAndReUnifyError, ReConstraintOrder,
        UnifyCxMode, unify::regions::graph::RegionRelationGraph,
    },
    syntax::{InferReVar, Re, RelationMode, UniversalReVar, UniversalReVarSourceInfo},
};
use index_vec::IndexVec;

// === ReUnifyTracker === //

#[derive(Clone)]
pub struct ReUnifyTracker<'sess> {
    universals: IndexVec<UniversalReVar, UniversalReVarSourceInfo>,
    next_infer: InferReVar,
    relations: Option<RegionRelationGraph<'sess>>,
}

impl<'sess> ReUnifyTracker<'sess> {
    pub fn new(mode: UnifyCxMode) -> Self {
        Self {
            universals: IndexVec::new(),
            next_infer: InferReVar::from_usize(0),
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
        if self.mode() == UnifyCxMode::RegionBlind {
            // For better interning
            return InferReVar::ERASED;
        }

        let var = self.next_infer;
        self.next_infer += 1;
        var
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
        lhs: impl IntoIterator<Item = Re>,
        rhs: impl IntoIterator<Item = Re>,
    ) {
        let Some(relations) = &mut self.relations else {
            return;
        };

        relations.permit(mode, lhs, rhs);
    }

    pub fn verify(&mut self) -> PromiseResolutionQueue<'sess> {
        let mut queue = PromiseResolutionQueue::default();

        let Some(relations) = &mut self.relations else {
            return queue;
        };

        relations.verify(&mut queue, self.universals.len(), self.next_infer.index());

        queue
    }

    pub fn graphviz(&self, ccx: &ClauseCx<'_>) -> String {
        if let Some(relations) = &self.relations {
            relations.graphviz(ccx, self.universals.len(), self.next_infer.index())
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
            infer::{ClauseCx, ImplCache, UnifyCxMode},
            syntax::{LangItems, RelationMode, UniversalReVarSourceInfo},
        },
    };

    #[test]
    fn region_chain_shorter() {
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
        let re_c = ccx.fresh_re_universal(UniversalReVarSourceInfo::UnitTest("'c"));
        let re_1 = ccx.fresh_re_infer();
        let re_2 = ccx.fresh_re_infer();

        // constrain(re_a: &shorter re_1)
        ccx.unify_re_and_re(RelationMode::RhsOntoLhs, [re_a], [re_1])
            .report_never();

        // permit(re_1: &shorter re_b)
        ccx.permit_re_and_re(RelationMode::LhsOntoRhs, [re_b], [re_1]);

        // constrain(re_b: &shorter re_2)
        ccx.unify_re_and_re(RelationMode::RhsOntoLhs, [re_b], [re_2])
            .report_never();

        // permit(re_2: &shorter re_c)
        ccx.permit_re_and_re(RelationMode::LhsOntoRhs, [re_c], [re_2]);

        // constrain(re_a: &shorter re_c)
        // Should be derived from...
        // - constrain(re_a: &shorter re_1), permit(re_1: &shorter re_b)
        //   => permit(re_1: &shorter re_b)
        // - constrain(re_b: &shorter re_2), permit(re_2: &shorter re_c)
        //   => permit(re_b: &shorter re_c)
        ccx.unify_re_and_re(RelationMode::RhsOntoLhs, [re_a], [re_c])
            .report_never();

        ccx.verify();
    }

    #[test]
    fn region_chain_longer() {
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
        let re_c = ccx.fresh_re_universal(UniversalReVarSourceInfo::UnitTest("'c"));
        let re_1 = ccx.fresh_re_infer();
        let re_2 = ccx.fresh_re_infer();

        // constrain(re_a: &longer re_1)
        ccx.unify_re_and_re(RelationMode::LhsOntoRhs, [re_a], [re_1])
            .report_never();

        // permit(re_1: &longer re_b)
        ccx.permit_re_and_re(RelationMode::RhsOntoLhs, [re_b], [re_1]);

        // constrain(re_b: &longer re_2)
        ccx.unify_re_and_re(RelationMode::LhsOntoRhs, [re_b], [re_2])
            .report_never();

        // permit(re_2: &longer re_c)
        ccx.permit_re_and_re(RelationMode::RhsOntoLhs, [re_c], [re_2]);

        // constrain(re_a: &longer re_c)
        // Should be derived from...
        // - constrain(re_a: &longer re_1), permit(re_1: &longer re_b)
        //   => permit(re_1: &longer re_b)
        // - constrain(re_b: &longer re_2), permit(re_2: &longer re_c)
        //   => permit(re_b: &longer re_c)
        ccx.unify_re_and_re(RelationMode::LhsOntoRhs, [re_a], [re_c])
            .report_never();

        ccx.verify();
    }
}
