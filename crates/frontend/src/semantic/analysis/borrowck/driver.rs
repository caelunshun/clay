use crate::{
    base::{Diag, LeafDiag, Session, arena::Obj},
    semantic::{
        analysis::{
            MirBbOperationKind, MirBbOperationVisitor, MirBuildCtxt, MirDataflowFacts, TyCtxt,
        },
        syntax::{Crate, FnDef, ItemKind, MirInstructionLoc},
    },
};
use std::ops::ControlFlow;

pub struct CrateBorrowCheckVisitor<'tcx> {
    pub tcx: &'tcx TyCtxt,
    pub krate: Obj<Crate>,
}

impl<'tcx> CrateBorrowCheckVisitor<'tcx> {
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
        let s = self.session();

        if def.r(s).hir_body.is_none() {
            return;
        }

        let mut ctxt = MirBuildCtxt::new(self.tcx, def);
        ctxt.lower_entry();

        let df = MirDataflowFacts::compute(self.tcx, &ctxt.body);

        for (block_idx, block) in ctxt.body.blocks.iter_enumerated() {
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
                                let thief = df.find_last_thief(s, &ctxt.body, location, op.place);

                                Diag::span_err(
                                    block.lookup(instr_idx).span(),
                                    "local used after ownership transferred",
                                )
                                .child(LeafDiag::span_note(
                                    ctxt.body.lookup(thief).span(),
                                    "ownership previously transferred here",
                                ))
                                .emit();

                                return ControlFlow::Break(());
                            }
                        }
                    }

                    ControlFlow::Continue(())
                })
                .visit_instr(block.lookup(instr_idx));
            }
        }
    }
}
