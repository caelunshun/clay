use crate::{
    Val,
    module::{BasicBlock, BasicBlockData, FuncData},
};
use cranelift_entity::{EntityList, ListPool, PrimaryMap, SecondaryMap};
use fir_core::Db;

/// Convert a function to SSA form, returning the new function.
pub fn make_ssa<'db>(db: &'db Db, func: &FuncData<'db>) -> FuncData<'db> {
    let new_func = FuncData {
        basic_blocks: PrimaryMap::new(),
        vals: PrimaryMap::new(),
        val_lists: ListPool::new(),
        ..func.clone()
    };
    let mut converter = SsaConverter {
        db,
        func,
        new_func,
        vars_in_blocks: Default::default(),
        extra_terminator_args: Vec::new(),
    };
    converter.run();
    converter.new_func
}

struct SsaConverter<'db, 'a> {
    #[allow(unused)]
    db: &'db Db,
    func: &'a FuncData<'db>,
    new_func: FuncData<'db>,
    vars_in_blocks: SecondaryMap<BasicBlock, SecondaryMap<Val, Option<Val>>>,
    extra_terminator_args: Vec<(BasicBlock, BasicBlock, Val)>,
}

impl<'db, 'a> SsaConverter<'db, 'a> {
    pub fn run(&mut self) {
        // Initialize new blocks
        for (block, block_data) in &self.func.basic_blocks {
            let mut params = EntityList::new();
            for param_var in block_data.params.as_slice(&self.func.val_lists) {
                let param_val = self.new_func.vals.push(self.func.vals[*param_var].clone());
                params.push(param_val, &mut self.new_func.val_lists);
                self.vars_in_blocks[block][*param_var] = Some(param_val);
            }

            let new_block_id = self.new_func.basic_blocks.push(BasicBlockData {
                instrs: vec![],
                params,
                name: block_data.name.clone(),
            });
            // Same order of insertion, so block IDs should match
            assert_eq!(block, new_block_id);
        }

        // Perform SSA conversion
        self.func.visit_basic_blocks_topological(|block| {
            let block_data = &self.func.basic_blocks[block];
            for &param_var in block_data.params.as_slice(&self.func.val_lists) {
                let param_val = self.new_func.vals.push(self.func.vals[param_var].clone());
                self.vars_in_blocks[block][param_var] = Some(param_val);
            }

            for &instr in &block_data.instrs {
                let new_instr =
                    instr.move_to_list_pool(&self.func.val_lists, &mut self.new_func.val_lists);

                let mut needed_vars = Vec::new();
                new_instr.visit_src_operands(&self.new_func.val_lists, |var| {
                    needed_vars.push(var);
                });

                for needed_var in needed_vars {
                    self.get_var_in_block(block, needed_var);
                }
                let new_instr = new_instr.map_src_operands(&mut self.new_func.val_lists, |var| {
                    self.vars_in_blocks[block][var].unwrap()
                });

                let mut written_vars = Vec::new();
                new_instr.visit_dst_operands(&self.new_func.val_lists, |var| {
                    written_vars.push(var);
                });

                for written_var in written_vars {
                    let val = self.new_func.vals.push(self.func.vals[written_var].clone());
                    self.vars_in_blocks[block][written_var] = Some(val);
                }

                let new_instr = new_instr.map_dst_operands(&mut self.new_func.val_lists, |var| {
                    self.vars_in_blocks[block][var].unwrap()
                });
                self.new_func.basic_blocks[block].instrs.push(new_instr);
            }
        });

        // Iteratively update basic block arguments
        // until all variables have been "threaded" to
        // all dependent blocks
        while let Some((block, successor_block, var)) = self.extra_terminator_args.pop() {
            let val = self.get_var_in_block(block, var);
            let block_data = &mut self.new_func.basic_blocks[block];
            block_data
                .instrs
                .last_mut()
                .unwrap()
                .successor_args_mut(successor_block)
                .push(val, &mut self.new_func.val_lists);
        }
    }

    fn get_var_in_block(&mut self, block: BasicBlock, var: Val) -> Val {
        if let Some(val) = self.vars_in_blocks[block][var] {
            val
        } else {
            // Need to add the variable as a parameter
            // and "thread" the variable from the block's
            // ancestors to get it in this block
            let param = self.new_func.vals.push(self.func.vals[var].clone());
            self.new_func.basic_blocks[block]
                .params
                .push(param, &mut self.new_func.val_lists);
            self.vars_in_blocks[block][var] = Some(param);

            self.func.visit_block_predecessors(block, |pred| {
                // Update the block terminator to pass this value
                // as an arguments
                self.extra_terminator_args.push((pred, block, var));
            });
            param
        }
    }
}
