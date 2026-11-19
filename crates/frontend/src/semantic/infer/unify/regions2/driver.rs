use crate::semantic::{
    infer::{
        Promise, ReAndReUnifyError, ReConstraintOrder, UnifyCxMode,
        unify::regions2::graph::RegionRelationGraph,
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
}

// === Tests === //

#[cfg(test)]
mod tests {
    use crate::{
        base::Session,
        semantic::{
            analysis::TyCtxt,
            infer::{ClauseCx, ImplCache, UnifyCxMode},
            syntax::{LangItems, RelationDirection, RelationMode, UniversalReVarSourceInfo},
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
        ccx.unify_re_and_re(re_a, re_1, RelationMode::RhsOntoLhs)
            .report_never();

        // permit(re_1: &shorter re_b)
        ccx.permit_universe_re_outlives_re(re_b, re_1, RelationDirection::LhsOntoRhs);

        // constrain(re_b: &shorter re_2)
        ccx.unify_re_and_re(re_b, re_2, RelationMode::RhsOntoLhs)
            .report_never();

        // permit(re_2: &shorter re_c)
        ccx.permit_universe_re_outlives_re(re_c, re_2, RelationDirection::LhsOntoRhs);

        // constrain(re_a: &shorter re_c)
        // Should be derived from...
        // - constrain(re_a: &shorter re_1), permit(re_1: &shorter re_b)
        //   => permit(re_1: &shorter re_b)
        // - constrain(re_b: &shorter re_2), permit(re_2: &shorter re_c)
        //   => permit(re_b: &shorter re_c)
        ccx.unify_re_and_re(re_a, re_c, RelationMode::RhsOntoLhs)
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
        ccx.unify_re_and_re(re_a, re_1, RelationMode::LhsOntoRhs)
            .report_never();

        // permit(re_1: &longer re_b)
        ccx.permit_universe_re_outlives_re(re_b, re_1, RelationDirection::RhsOntoLhs);

        // constrain(re_b: &longer re_2)
        ccx.unify_re_and_re(re_b, re_2, RelationMode::LhsOntoRhs)
            .report_never();

        // permit(re_2: &longer re_c)
        ccx.permit_universe_re_outlives_re(re_c, re_2, RelationDirection::RhsOntoLhs);

        // constrain(re_a: &longer re_c)
        // Should be derived from...
        // - constrain(re_a: &longer re_1), permit(re_1: &longer re_b)
        //   => permit(re_1: &longer re_b)
        // - constrain(re_b: &longer re_2), permit(re_2: &longer re_c)
        //   => permit(re_b: &longer re_c)
        ccx.unify_re_and_re(re_a, re_c, RelationMode::LhsOntoRhs)
            .report_never();

        ccx.verify();
    }
}
