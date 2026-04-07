use crate::{
    base::{Diag, LeafDiag, Session, arena::Obj},
    semantic::{
        analysis::{
            ClauseCx, ClauseOrigin, CoherenceMap, HrtbUniverse, MirBbOperationKind,
            MirBbOperationVisitor, MirBuildCtxt, MirDataflowFacts, TyCtxt, TyFolderInfallibleExt,
            TyVisitorInfallibleExt, UnifyCxMode,
        },
        syntax::{
            Crate, FnDef, ItemKind, MirInstructionLoc, MirLocalIdx, Re, RelationDirection,
            UniversalReVarSourceInfo,
        },
    },
};
use index_vec::IndexVec;
use std::ops::ControlFlow;

pub struct CrateBorrowCheckVisitor<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub krate: Obj<Crate>,
    pub coherence: &'tcx CoherenceMap,
}

impl<'tcx> CrateBorrowCheckVisitor<'tcx> {
    pub fn tcx(&self) -> &'tcx TyCtxt {
        self.tcx
    }

    pub fn session(&self) -> &'tcx Session {
        &self.tcx.session
    }

    pub fn visit_crate(&mut self) {
        let s = self.session();

        for &item in self.krate.r(s).items.iter() {
            match *item.r(s).kind {
                ItemKind::Fn(def) => {
                    self.visit_fn_def(*def.r(s).def);
                }
                ItemKind::Trait(def) => {
                    for &method in def.r(s).methods.iter() {
                        self.visit_fn_def(method);
                    }
                }
                ItemKind::Impl(def) => {
                    for &method in def.r(s).methods.iter() {
                        let Some(method) = method else {
                            continue;
                        };

                        self.visit_fn_def(method);
                    }
                }

                ItemKind::Module(..)
                | ItemKind::Adt(..)
                | ItemKind::EnumVariant(..)
                | ItemKind::TypeAlias(..) => {
                    // (no bodies)
                }
            }
        }
    }

    pub fn visit_fn_def(&self, def: Obj<FnDef>) {
        let tcx = self.tcx();
        let s = self.session();

        if def.r(s).hir_body.is_none() {
            return;
        }

        // Lower MIR
        let mut ctxt = MirBuildCtxt::new(self.tcx, def);
        ctxt.lower_entry();
        let body = ctxt.body;

        // Compute data-flow
        let df = MirDataflowFacts::compute(self.tcx, &body);

        // Check ownership and local occupancy
        for (block_idx, block) in body.blocks.iter_enumerated() {
            for instr_idx in block.instructions() {
                let location = MirInstructionLoc {
                    block: block_idx,
                    instr: instr_idx,
                };
                let occupancy = df.occupancy.state_before(location);

                _ = MirBbOperationVisitor(s, |op| {
                    match op.kind {
                        MirBbOperationKind::Provide => {
                            // (no-op)
                        }
                        MirBbOperationKind::Steal | MirBbOperationKind::Use => {
                            if !occupancy.contains(op.place) {
                                if let Some(thief) =
                                    df.find_last_thief(s, &body, location, op.place)
                                {
                                    Diag::span_err(
                                        block.lookup(instr_idx).span(),
                                        "local used after ownership transferred",
                                    )
                                    .child(LeafDiag::span_note(
                                        body.lookup(thief).span(),
                                        "ownership previously transferred here",
                                    ))
                                    .emit();
                                } else {
                                    Diag::span_err(
                                        block.lookup(instr_idx).span(),
                                        "local used before initialized",
                                    )
                                    .emit();
                                }

                                return ControlFlow::Break(());
                            }
                        }
                    }

                    ControlFlow::Continue(())
                })
                .visit_instr(block.lookup(instr_idx));
            }
        }

        // Type-check regions.
        let mut ccx = ClauseCx::new(tcx, self.coherence, self.krate, UnifyCxMode::RegionAware);

        let env = ccx.import_fn_def_env_as_universal(
            &ClauseOrigin::never_printed(),
            HrtbUniverse::ROOT_REF,
            def,
        );

        let local_universals = body
            .locals
            .indices()
            .map(|idx| ccx.fresh_re_universal(UniversalReVarSourceInfo::MirLocal(idx)))
            .collect::<IndexVec<MirLocalIdx, Re>>();

        for (rhs_local, &rhs_re) in local_universals.iter_enumerated() {
            let lhs_outlive_mask = df.can_outlive_rhs_mask(&body, rhs_local);

            for lhs_local in lhs_outlive_mask.iter() {
                let lhs_re = local_universals[lhs_local];

                ccx.permit_universe_re_outlives_re(lhs_re, rhs_re, RelationDirection::LhsOntoRhs);
            }
        }

        let mut body_instantiated = body.clone();

        for (local_idx, local) in body_instantiated.locals.iter_mut_enumerated() {
            local.ty = ccx
                .importer(
                    &ClauseOrigin::never_printed(),
                    HrtbUniverse::ROOT,
                    env.as_ref(),
                )
                .fold(local.ty);

            ccx.wf_visitor(HrtbUniverse::ROOT).visit(local.ty);

            ccx.oblige_ty_outlives_re(
                ClauseOrigin::empty_report(),
                local.ty,
                local_universals[local_idx],
                RelationDirection::LhsOntoRhs,
            );
        }

        // TODO: type-check

        ccx.verify();
    }
}
