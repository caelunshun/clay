use crate::semantic::syntax::{
    MirAssignRvalue, MirBlock, MirBlockIdx, MirBody, MirOperand, MirPlace, MirStmt, MirStmtKind,
    MirTerminator,
};

pub struct MirLowerFlow {
    curr: Option<MirBlockIdx>,
}

impl MirLowerFlow {
    pub fn new(body: &mut MirBody) -> Self {
        Self {
            curr: Some(body.blocks.push(MirBlock::default())),
        }
    }

    pub fn is_finished(&self) -> bool {
        self.curr.is_none()
    }

    pub fn is_continuing(&self) -> bool {
        self.curr.is_some()
    }

    pub fn opt_curr(&self) -> Option<MirBlockIdx> {
        self.curr
    }

    pub fn expect_curr(&self) -> MirBlockIdx {
        self.curr.expect("flow is finished")
    }

    pub fn start_new_curr(&mut self, body: &mut MirBody) -> MirBlockIdx {
        assert!(self.curr.is_none(), "flow is not yet finished");
        let curr = body.blocks.push(MirBlock::default());
        self.curr = Some(curr);
        curr
    }

    pub fn ensure_curr(&mut self, body: &mut MirBody) -> MirBlockIdx {
        *self
            .curr
            .get_or_insert_with(|| body.blocks.push(MirBlock::default()))
    }

    pub fn push_stmt(&self, body: &mut MirBody, stmt: MirStmt) {
        body.blocks[self.expect_curr()].stmts.push(stmt);
    }

    pub fn push_assign(&self, body: &mut MirBody, lhs: MirPlace, rhs: MirAssignRvalue) {
        self.push_stmt(
            body,
            MirStmt {
                kind: MirStmtKind::Assign(Box::new((lhs, rhs))),
            },
        );
    }

    pub fn push_assign_use(&self, body: &mut MirBody, lhs: MirPlace, rhs: MirOperand) {
        self.push_assign(body, lhs, MirAssignRvalue::Use(rhs));
    }

    pub fn push_terminator_final(&mut self, body: &mut MirBody, terminator: MirTerminator) {
        body.blocks[self.expect_curr()].terminator = terminator;
        self.curr = None;
    }

    pub fn push_terminator_chained(
        &mut self,
        body: &mut MirBody,
        f: impl FnOnce(MirBlockIdx) -> MirTerminator,
    ) {
        let successor = body.blocks.push(MirBlock::default());
        let terminator = f(successor);
        body.blocks[self.expect_curr()].terminator = terminator;
        self.curr = Some(successor);
    }

    pub fn push_call(
        &mut self,
        body: &mut MirBody,
        callee: MirOperand,
        args: Box<[MirOperand]>,
        destination: MirPlace,
    ) {
        self.push_terminator_chained(body, |target| MirTerminator::Call {
            callee,
            args,
            destination,
            target,
        });
    }

    pub fn push_drop(&mut self, body: &mut MirBody, place: MirPlace) {
        self.push_terminator_chained(body, |target| MirTerminator::Drop { place, target });
    }

    pub fn push_goto(&mut self, body: &mut MirBody, target: MirBlockIdx) {
        self.push_terminator_final(body, MirTerminator::Goto(target));
    }

    pub fn push_unreachable(&mut self, body: &mut MirBody) {
        self.push_terminator_final(body, MirTerminator::Unreachable);
    }

    pub fn push_switch(
        &mut self,
        body: &mut MirBody,
        scrutinee: MirPlace,
        targets: Box<[MirBlockIdx]>,
    ) {
        self.push_terminator_final(body, MirTerminator::Switch { scrutinee, targets });
    }

    pub fn fallthrough_to(&mut self, body: &mut MirBody, target: &mut MirLowerFlow) {
        if self.is_finished() {
            return;
        }

        let bb = target.ensure_curr(body);
        self.push_goto(body, bb);
    }
}
