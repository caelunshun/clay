use crate::{gc::GarbageCollector, interpreter::Interpreter, type_registry::TypeRegistry};
use bytecode::{entity_ref, module::FuncData, LocalFunc, ModuleData};
use cranelift_entity::{PrimaryMap, SecondaryMap};
use std::{cell::RefCell, sync::Arc};
use thread_local::ThreadLocal;

#[derive(Default)]
pub struct Engine {
    pub(crate) modules: PrimaryMap<Module, ModuleData>,
    pub(crate) type_registry: TypeRegistry,
    /// Maps global function IDs to local function IDs in modules.
    pub(crate) funcs: PrimaryMap<Func, (Module, LocalFunc)>,
    pub(crate) funcs_by_module: SecondaryMap<Module, SecondaryMap<LocalFunc, Func>>,
    pub(crate) interpreter: ThreadLocal<RefCell<Interpreter>>,
}

impl Engine {
    pub(crate) fn load_module(&mut self, module: ModuleData) -> Module {
        let id = self.modules.push(module);
        self.type_registry.load_module_types(id, &self.modules[id]);

        for local_func in self.modules[id].funcs.keys() {
            let func = self.funcs.push((id, local_func));
            self.funcs_by_module[id][local_func] = func;
        }

        id
    }

    pub(crate) fn func_data(&self, func: Func) -> &FuncData {
        let (module, local_func) = self.funcs[func];
        &self.modules[module].funcs[local_func]
    }
}

entity_ref! {
    pub struct Func;
}

pub struct Instance {
    pub(crate) engine: Arc<Engine>,
    pub(crate) gc: Arc<dyn GarbageCollector>,
}

impl Instance {
    #[doc(hidden)]
    pub fn new_test(module: bytecode::ModuleData, approx_max_memory: usize) -> Self {
        let mut engine = Engine::default();
        engine.load_module(module);
        let gc = crate::gc_impl::simple::SimpleGarbageCollector::new(approx_max_memory);
        Self {
            engine: Arc::new(engine),
            gc: Arc::new(gc),
        }
    }

    pub fn interp(&self, func: Func) -> i64 {
        self.gc.mark_thread_active();
        let res = self
            .engine
            .interpreter
            .get_or(|| RefCell::new(Interpreter::new()))
            .borrow_mut()
            .interp(func, self);
        self.gc.mark_thread_inactive();
        res
    }
}

entity_ref! {
    /// ID of a bytecode module loaded into an `Engine`.
    pub struct Module;
}
