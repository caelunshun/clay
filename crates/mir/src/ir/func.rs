use crate::{
    InstrData,
    ir::{
        ContextLike, TypeArgs, TypeParams,
        context::{FuncId, TraitId},
        trait_::AssocFuncId,
        typ::Type,
    },
};
use compact_str::CompactString;
use cranelift_entity::{EntityList, EntitySet, ListPool, PrimaryMap, SecondaryMap};
use salsa::Database;

#[salsa::tracked(debug)]
pub struct Func<'db> {
    #[returns(ref)]
    #[tracked]
    pub data: FuncData<'db>,
}

/// The function header describes the signature
/// of the function but not its behavior.
#[derive(Debug, Clone, PartialEq, Hash, salsa::Update)]
pub struct FuncHeader<'db> {
    /// Used for debugging; may be synthetic
    /// in the case of anonymous functions.
    pub name: CompactString,
    /// Type used to store the captured variables
    /// for the function. A managed reference
    /// to the captures is the first argument
    /// to the entry block of the function.
    pub captures_type: Type<'db>,
    /// Parameters expected by the function, not including the captures.
    pub param_types: Vec<Type<'db>>,
    pub return_type: Type<'db>,
    pub type_params: TypeParams<'db>,
}

#[derive(Debug, Clone, PartialEq, Hash, salsa::Update)]
pub struct FuncData<'db> {
    pub header: FuncHeader<'db>,
    /// Set of values used by the function. Values can be assigned
    /// multiple times until after the SSA lowering pass is applied.
    pub vals: PrimaryMap<ValId, Val<'db>>,

    /// Basic blocks in the function instruction stream.
    pub basic_blocks: PrimaryMap<BasicBlockId, BasicBlock<'db>>,
    /// Basic block where execution of this function starts.
    pub entry_block: BasicBlockId,

    /// Pool of `Local` references used for lists
    /// of locals in `instrs`.
    pub val_lists: ListPool<ValId>,
}

impl<'db> FuncData<'db> {
    /// Visits all basic blocks in an order such that
    /// a block B is not visited until after all blocks that
    /// appear in any *path* (not a walk) from the entry block to B (exclusive)
    /// are visited.
    pub fn visit_basic_blocks_topological(&self, mut visit: impl FnMut(BasicBlockId)) {
        let acyclic_ancestors = self.compute_acyclic_ancestors();

        let mut stack = vec![self.entry_block];
        let mut visited = EntitySet::<BasicBlockId>::new();
        while let Some(current) = stack.pop() {
            visit(current);
            visited.insert(current);

            self.visit_block_successors(current, |suc| {
                if !visited.contains(suc)
                    && acyclic_ancestors[suc]
                        .iter()
                        .all(|anc| visited.contains(anc))
                {
                    stack.push(suc);
                }
            });
        }
    }

    /// Computes the set of blocks reachable by paths
    /// (not walks) from the entry block to each block
    /// (excluding the destination block).
    pub fn compute_acyclic_ancestors(&self) -> SecondaryMap<BasicBlockId, EntitySet<BasicBlockId>> {
        // For each block, calculate blocks that appear in a path from the entry block
        let mut acyclic_ancestors: SecondaryMap<BasicBlockId, EntitySet<BasicBlockId>> =
            Default::default();

        let mut stack = vec![(self.entry_block, EntitySet::<BasicBlockId>::new())];
        while let Some((current_block, mut current_path)) = stack.pop() {
            for ancestor in current_path.iter() {
                acyclic_ancestors[current_block].insert(ancestor);
            }
            current_path.insert(current_block);
            self.visit_block_successors(current_block, |suc| {
                if !current_path.contains(suc) {
                    stack.push((suc, current_path.clone()));
                }
            });
        }

        acyclic_ancestors
    }

    /// Computes the set of paths from the entry block
    /// to each block. These paths do not include
    /// the destination blocks.
    pub fn compute_paths_from_entry(
        &self,
    ) -> SecondaryMap<BasicBlockId, Vec<EntitySet<BasicBlockId>>> {
        let mut paths: SecondaryMap<BasicBlockId, Vec<EntitySet<BasicBlockId>>> =
            SecondaryMap::new();

        let mut stack = vec![(self.entry_block, EntitySet::<BasicBlockId>::new())];
        while let Some((current_block, mut current_path)) = stack.pop() {
            paths[current_block].push(current_path.clone());
            current_path.insert(current_block);
            self.visit_block_successors(current_block, |suc| {
                if !current_path.contains(suc) {
                    stack.push((suc, current_path.clone()));
                }
            });
        }

        paths
    }

    pub fn is_block_edge(&self, a: BasicBlockId, b: BasicBlockId) -> bool {
        let mut is_edge = false;
        self.visit_block_successors(a, |b2| {
            if b2 == b {
                is_edge = true;
            }
        });
        is_edge
    }

    pub fn visit_block_successors(&self, block: BasicBlockId, visit: impl FnMut(BasicBlockId)) {
        self.basic_blocks[block]
            .instrs
            .last()
            .unwrap()
            .visit_successors(visit)
    }

    pub fn visit_block_predecessors(
        &self,
        block: BasicBlockId,
        mut visit: impl FnMut(BasicBlockId),
    ) {
        self.basic_blocks.keys().for_each(|block2| {
            let mut is_predecessor = false;
            self.visit_block_successors(block2, |b| {
                if b == block {
                    is_predecessor = true;
                }
            });
            if is_predecessor {
                visit(block2);
            }
        })
    }
}

entity_ref_16bit! {
    pub struct ValId;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub struct Val<'db> {
    /// Type of the local.
    pub typ: Type<'db>,
    /// Optional name, for debugging and testing.
    pub name: Option<CompactString>,
}

entity_ref_16bit! {
    pub struct BasicBlockId;
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, salsa::Update)]
pub struct BasicBlock<'db> {
    /// Optional name, for debugging and testing.
    pub name: Option<CompactString>,
    pub instrs: Vec<InstrData<'db>>,
    /// Only used after SSA transformation; empty before then, except for
    /// the entry block, where the capture pointer followed by the function arguments are assigned
    /// here.
    pub params: EntityList<ValId>,
}

#[salsa::interned(debug)]
pub struct FuncInstance<'db> {
    pub func: MaybeAssocFunc<'db>,
    #[returns(ref)]
    pub type_args: TypeArgs<'db>,
}

impl<'db> FuncInstance<'db> {
    pub fn type_params(
        &self,
        db: &'db dyn Database,
        cx: &impl ContextLike<'db>,
    ) -> TypeParams<'db> {
        match self.func(db) {
            MaybeAssocFunc::Func(func_id) => func_id.resolve_header(db, cx).type_params.clone(),
            MaybeAssocFunc::AssocFunc {
                trait_, assoc_func, ..
            } => trait_.resolve(db, cx).data(db).assoc_funcs[assoc_func]
                .type_params
                .clone(),
        }
    }

    /// Resolves the concrete return type of the function.
    pub fn return_type(&self, db: &'db dyn Database, cx: &impl ContextLike<'db>) -> Type<'db> {
        match self.func(db) {
            MaybeAssocFunc::Func(func_id) => func_id
                .resolve_header(db, cx)
                .return_type
                .substitute_type_args(db, self.type_args(db)),
            MaybeAssocFunc::AssocFunc {
                trait_,
                typ,
                assoc_func,
            } => {
                let trait_ = trait_.resolve(db, cx);
                let assoc_func = &trait_.data(db).assoc_funcs[assoc_func];
                assoc_func
                    .return_type
                    .substitute_self_type(db, typ)
                    .substitute_type_args(db, self.type_args(db))
            }
        }
    }

    /// Resolves the concrete parameter types of the function.
    pub fn param_types(&self, db: &'db dyn Database, cx: &impl ContextLike<'db>) -> Vec<Type<'db>> {
        match self.func(db) {
            MaybeAssocFunc::Func(func_id) => func_id
                .resolve_header(db, cx)
                .param_types
                .iter()
                .copied()
                .map(|param_type| param_type.substitute_type_args(db, self.type_args(db)))
                .collect(),
            MaybeAssocFunc::AssocFunc {
                trait_,
                typ,
                assoc_func,
            } => {
                let trait_ = trait_.resolve(db, cx);
                let assoc_func = &trait_.data(db).assoc_funcs[assoc_func];
                assoc_func
                    .param_types
                    .iter()
                    .copied()
                    .map(|param_type| {
                        param_type
                            .substitute_self_type(db, typ)
                            .substitute_type_args(db, self.type_args(db))
                    })
                    .collect()
            }
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, salsa::Update)]
pub enum MaybeAssocFunc<'db> {
    Func(FuncId),
    AssocFunc {
        trait_: TraitId,
        typ: Type<'db>,
        assoc_func: AssocFuncId,
    },
}
