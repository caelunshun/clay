use crate::{
    gc::StackWalker,
    ptr::MRef,
    type_registry::{FuncObject, LazyLayout, Type, TypeKind},
    Error, Func, Instance, Module, Value,
};
use bytecode::{
    instr::CompareMode,
    module::{ConstantData, FuncData, ValData},
    Instr, InstrData, ModuleData, PrimitiveType, Val,
};
use core::slice;
use cranelift_entity::{EntityRef, SecondaryMap};
use parking_lot::OnceState;
use portable_atomic::AtomicU128;
use stack::Stack;
use stack_map::FunctionStackMap;
use std::{
    iter::Rev,
    sync::{
        atomic::{AtomicBool, AtomicI64, AtomicPtr, AtomicU64, Ordering},
        Arc,
    },
};

mod stack;
mod stack_map;

macro_rules! invalid_bytecode {
    () => {
        panic!("invalid bytecode encountered")
    };
}

/// Cached interpreter state.
pub struct Interpreter {
    stack: Stack,
    function_stack_maps: SecondaryMap<Func, Option<Arc<FunctionStackMap>>>,
    continuations: Vec<Continuation>, // cached allocation
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            stack: Stack::new(),
            function_stack_maps: SecondaryMap::default(),
            continuations: Vec::new(),
        }
    }

    fn reset(&mut self) {
        self.stack.clear();
        self.continuations.clear();
    }

    pub fn interp_bare(&mut self, func: Func, instance: &Instance) -> Result<Value, Error> {
        self.reset();
        InterpreterLoop::new(self, instance, func).run()
    }
}

/// Interpreter loop state.
///
/// Due to the lack of guaranteed tail calls in Rust,
/// we have to implement mutual recursion manually via
/// a state machine.
/// This can be cleaned up once rustc implements the `become`
/// keyword.
struct InterpreterLoop<'a> {
    instance: &'a Instance,
    stack: &'a Stack,
    function_stack_maps: &'a mut SecondaryMap<Func, Option<Arc<FunctionStackMap>>>,

    current_func: Func,
    current_func_data: &'a FuncData,
    current_func_stack_map: Arc<FunctionStackMap>,

    next_instr: Instr,

    current_module: Module,
    current_module_data: &'a ModuleData,

    /// No continuations left means to return to the host
    /// when encountering a `Return`.
    continuations: &'a mut Vec<Continuation>,
}

impl<'a> InterpreterLoop<'a> {
    pub fn new(interpreter: &'a mut Interpreter, instance: &'a Instance, func: Func) -> Self {
        let current_module = instance.engine.funcs[func].0;
        let current_func_stack_map = interpreter.function_stack_maps[func]
            .get_or_insert_with(|| {
                Arc::new(FunctionStackMap::new(
                    instance.engine.func_data(func),
                    current_module,
                    &instance.engine,
                ))
            })
            .clone();

        interpreter
            .stack
            .push_frame(current_func_stack_map.layout.size());

        Self {
            instance,
            stack: &interpreter.stack,
            current_func: func,
            current_func_data: instance.engine.func_data(func),
            current_func_stack_map,
            function_stack_maps: &mut interpreter.function_stack_maps,
            next_instr: Instr::new(0),
            current_module,
            current_module_data: &instance.engine.modules[current_module],
            continuations: &mut interpreter.continuations,
        }
    }

    pub fn run(&mut self) -> Result<Value, Error> {
        loop {
            let instr = &self.current_func_data.instrs[self.next_instr];
            self.next_instr = Instr::new(self.next_instr.index() + 1);

            match instr {
                InstrData::Jump(instr) => {
                    self.next_instr = instr.target;
                    self.gc_safepoint();
                }
                InstrData::Branch(instr) => {
                    if self.load_local::<bool>(instr.condition) {
                        self.next_instr = instr.target;
                        self.gc_safepoint();
                    }
                }
                InstrData::Call(instr) => {
                    self.gc_safepoint();

                    let function_object = &self.load_local::<FuncObject>(instr.func);
                    let args = instr.args.as_slice(&self.current_func_data.val_lists);
                    self.continuations.push(Continuation::ResumeCaller {
                        caller_func: self.current_func,
                        caller_instr: self.next_instr,
                        return_value_dst: self.current_func_stack_map.local_offsets
                            [instr.return_value_dst],
                    });
                    self.call(function_object, args);
                }
                InstrData::Return(instr) => match self.continuations.pop() {
                    Some(cont) => {
                        self.continue_(instr.return_value, cont);
                        self.stack.pop_frame();
                    }
                    None => return Ok(self.local_to_value(instr.return_value)),
                },
                InstrData::Copy(instr) => {
                    let src = self.current_func_stack_map.local_offsets[instr.src];
                    let dst = self.current_func_stack_map.local_offsets[instr.dst];
                    let local_type = self.current_func_data.vals[instr.dst].typ;
                    let typ = self.instance.engine.type_registry.module_mapping
                        [self.current_module][local_type];
                    let layout = self.instance.engine.type_registry.layouts[typ];
                    unsafe {
                        self.stack.copy(src, dst, layout.unwrap().size() as u32);
                    }
                }
                InstrData::IntConstant(instr) => {
                    let ConstantData::Int(val) = self.current_module_data.constants[instr.constant]
                    else {
                        invalid_bytecode!()
                    };
                    self.store_local(instr.dst, val);
                }
                InstrData::IntAdd(instr) => {
                    let lhs: i64 = self.load_local(instr.src1);
                    let rhs: i64 = self.load_local(instr.src2);
                    let result = lhs.wrapping_add(rhs);
                    self.store_local(instr.dst, result);
                }
                InstrData::IntSub(instr) => {
                    let lhs: i64 = self.load_local(instr.src1);
                    let rhs: i64 = self.load_local(instr.src2);
                    let result = lhs.wrapping_sub(rhs);
                    self.store_local(instr.dst, result);
                }
                InstrData::IntMul(instr) => {
                    let lhs: i64 = self.load_local(instr.src1);
                    let rhs: i64 = self.load_local(instr.src2);
                    let result = lhs.wrapping_mul(rhs);
                    self.store_local(instr.dst, result);
                }
                InstrData::IntDiv(instr) => {
                    let lhs: i64 = self.load_local(instr.src1);
                    let rhs: i64 = self.load_local(instr.src2);
                    let result = lhs.wrapping_div(rhs);
                    self.store_local(instr.dst, result);
                }
                InstrData::IntCmp(instr) => {
                    let lhs: i64 = self.load_local(instr.src1);
                    let rhs: i64 = self.load_local(instr.src2);
                    let result: bool = match instr.mode {
                        CompareMode::Less => lhs < rhs,
                        CompareMode::LessOrEqual => lhs <= rhs,
                        CompareMode::Greater => lhs > rhs,
                        CompareMode::GreaterOrEqual => lhs >= rhs,
                        CompareMode::Equal => lhs == rhs,
                        CompareMode::NotEqual => lhs != rhs,
                    };
                    self.store_local(instr.dst, result);
                }
                InstrData::RealConstant(instr) => {
                    let ConstantData::Real(val) =
                        self.current_module_data.constants[instr.constant]
                    else {
                        invalid_bytecode!()
                    };
                    self.store_local(instr.dst, val);
                }
                InstrData::RealAdd(instr) => {
                    let lhs: f64 = self.load_local(instr.src1);
                    let rhs: f64 = self.load_local(instr.src2);
                    let result = lhs + rhs;
                    self.store_local(instr.dst, result);
                }
                InstrData::RealSub(instr) => {
                    let lhs: f64 = self.load_local(instr.src1);
                    let rhs: f64 = self.load_local(instr.src2);
                    let result = lhs - rhs;
                    self.store_local(instr.dst, result);
                }
                InstrData::RealMul(instr) => {
                    let lhs: f64 = self.load_local(instr.src1);
                    let rhs: f64 = self.load_local(instr.src2);
                    let result = lhs * rhs;
                    self.store_local(instr.dst, result);
                }
                InstrData::RealDiv(instr) => {
                    let lhs: f64 = self.load_local(instr.src1);
                    let rhs: f64 = self.load_local(instr.src2);
                    let result = lhs / rhs;
                    self.store_local(instr.dst, result);
                }
                InstrData::RealCmp(instr) => {
                    let lhs: f64 = self.load_local(instr.src1);
                    let rhs: f64 = self.load_local(instr.src2);
                    let result: bool = match instr.mode {
                        CompareMode::Less => lhs < rhs,
                        CompareMode::LessOrEqual => lhs <= rhs,
                        CompareMode::Greater => lhs > rhs,
                        CompareMode::GreaterOrEqual => lhs >= rhs,
                        CompareMode::Equal => lhs == rhs,
                        CompareMode::NotEqual => lhs != rhs,
                    };
                    self.store_local(instr.dst, result);
                }
                InstrData::BoolConstant(instr) => {
                    let ConstantData::Bool(val) =
                        self.current_module_data.constants[instr.constant]
                    else {
                        invalid_bytecode!()
                    };
                    self.store_local(instr.dst, val);
                }
                InstrData::BoolAnd(instr) => {
                    let lhs: bool = self.load_local(instr.src1);
                    let rhs: bool = self.load_local(instr.src2);
                    let result = lhs & rhs;
                    self.store_local(instr.dst, result);
                }
                InstrData::BoolOr(instr) => {
                    let lhs: bool = self.load_local(instr.src1);
                    let rhs: bool = self.load_local(instr.src2);
                    let result = lhs | rhs;
                    self.store_local(instr.dst, result);
                }
                InstrData::BoolXor(instr) => {
                    let lhs: bool = self.load_local(instr.src1);
                    let rhs: bool = self.load_local(instr.src2);
                    let result = lhs ^ rhs;
                    self.store_local(instr.dst, result);
                }
                InstrData::BoolNot(instr) => {
                    let x: bool = self.load_local(instr.src);
                    let result = !x;
                    self.store_local(instr.dst, result);
                }
                InstrData::InitStruct(instr) => {
                    let struct_type = self.instance.engine.type_registry.module_mapping
                        [self.current_module][instr.typ];
                    let TypeKind::Struct(struct_data) =
                        &self.instance.engine.type_registry.types[struct_type].kind
                    else {
                        invalid_bytecode!()
                    };

                    let field_locals = instr.fields.as_slice(&self.current_func_data.val_lists);
                    let dst_base = self.current_func_stack_map.local_offsets[instr.dst];
                    for (field, &local) in struct_data.fields.values().zip(field_locals) {
                        let src = self.current_func_stack_map.local_offsets[local];
                        let dst = dst_base + field.offset as u32;
                        unsafe {
                            self.stack.copy(src, dst, field.size as u32);
                        }
                    }
                }
                InstrData::GetField(instr) => {
                    let struct_type = self.current_func_data.vals[instr.src_struct].typ;
                    let struct_type = self.instance.engine.type_registry.module_mapping
                        [self.current_module][struct_type];
                    let TypeKind::Struct(struct_data) =
                        &self.instance.engine.type_registry.types[struct_type].kind
                    else {
                        invalid_bytecode!()
                    };

                    let offset = struct_data.fields[instr.field].offset as u32;
                    let size = struct_data.fields[instr.field].size as u32;
                    let src_base = self.current_func_stack_map.local_offsets[instr.src_struct];
                    let dst = self.current_func_stack_map.local_offsets[instr.dst];
                    unsafe {
                        self.stack.copy(src_base + offset, dst, size);
                    }
                }
                InstrData::SetField(instr) => {
                    let struct_type = self.current_func_data.vals[instr.dst_struct].typ;
                    let struct_type = self.instance.engine.type_registry.module_mapping
                        [self.current_module][struct_type];
                    let TypeKind::Struct(struct_data) =
                        &self.instance.engine.type_registry.types[struct_type].kind
                    else {
                        invalid_bytecode!()
                    };

                    let offset = struct_data.fields[instr.field].offset as u32;
                    let size = struct_data.fields[instr.field].size as u32;
                    let dst_base = self.current_func_stack_map.local_offsets[instr.dst_struct];
                    let src = self.current_func_stack_map.local_offsets[instr.src];
                    unsafe {
                        self.stack.copy(src, dst_base + offset, size);
                    }
                }
                InstrData::Alloc(instr) => {
                    let mut walker = self.stack_walker();

                    let ref_type = self.current_func_data.vals[instr.dst_ref].typ;
                    let ref_type = self.instance.engine.type_registry.module_mapping
                        [self.current_module][ref_type];
                    let TypeKind::Reference(alloc_type) =
                        &self.instance.engine.type_registry.types[ref_type].kind
                    else {
                        invalid_bytecode!()
                    };

                    let r = self
                        .instance
                        .gc
                        .allocate(self.instance, *alloc_type, &mut walker)?;
                    unsafe {
                        self.memory_store(instr.src, r.as_ptr());
                    }

                    self.store_local(instr.dst_ref, r);
                }
                InstrData::Load(instr) => {
                    let r: MRef = self.load_local(instr.src_ref);
                    unsafe {
                        self.memory_load(r.as_ptr(), instr.dst);
                    }
                }
                InstrData::LoadField(instr) => {
                    let ref_type = self.current_func_data.vals[instr.src_ref].typ;
                    let ref_type = self.instance.engine.type_registry.module_mapping
                        [self.current_module][ref_type];
                    let TypeKind::Reference(struct_type) =
                        &self.instance.engine.type_registry.types[ref_type].kind
                    else {
                        invalid_bytecode!()
                    };

                    let TypeKind::Struct(struct_data) =
                        &self.instance.engine.type_registry.types[*struct_type].kind
                    else {
                        invalid_bytecode!()
                    };

                    let offset = struct_data.fields[instr.field].offset as u32;
                    let r: MRef = self.load_local(instr.src_ref);
                    unsafe {
                        self.memory_load(r.as_ptr().add(offset.try_into().unwrap()), instr.dst);
                    }
                }
                InstrData::Store(instr) => {
                    let r: MRef = self.load_local(instr.dst_ref);
                    unsafe {
                        self.memory_store(instr.src_val, r.as_ptr());
                    }
                }
                InstrData::StoreField(instr) => {
                    let ref_type = self.current_func_data.vals[instr.dst_ref].typ;
                    let ref_type = self.instance.engine.type_registry.module_mapping
                        [self.current_module][ref_type];
                    let TypeKind::Reference(struct_type) =
                        &self.instance.engine.type_registry.types[ref_type].kind
                    else {
                        invalid_bytecode!()
                    };

                    let TypeKind::Struct(struct_data) =
                        &self.instance.engine.type_registry.types[*struct_type].kind
                    else {
                        invalid_bytecode!()
                    };

                    let offset = struct_data.fields[instr.field].offset as u32;
                    let r: MRef = self.load_local(instr.dst_ref);
                    unsafe {
                        self.memory_store(
                            instr.src_val,
                            r.as_ptr().add(offset.try_into().unwrap()),
                        );
                    }
                }
                InstrData::MakeFunctionObject(instr) => {
                    let object = FuncObject {
                        captures: self.load_local(instr.captures_ref),
                        func: self.instance.engine.funcs_by_module[self.current_module][instr.func],
                        padding: 0,
                    };
                    self.store_local(instr.dst, object);
                }
            }
        }
    }

    fn gc_safepoint(&mut self) {
        let mut walker = self.stack_walker();
        self.instance.gc.safepoint(self.instance, &mut walker);
    }

    fn continue_(&mut self, result: Val, cont: Continuation) {
        match cont {
            Continuation::ResumeCaller {
                caller_func,
                caller_instr,
                return_value_dst,
            } => {
                let return_value_size = self.current_func_stack_map.local_sizes[result];
                let return_value_src = self.current_func_stack_map.local_offsets[result];
                unsafe {
                    self.stack.copy_to_caller(
                        return_value_src,
                        return_value_dst,
                        return_value_size,
                    );
                }
                self.resume(caller_func, caller_instr);
            }
            Continuation::WriteLazy {
                lazy_layout,
                lazy_ref,
                caller_func,
                caller_instr,
            } => {
                unsafe {
                    lazy_layout.get_once_ptr(lazy_ref).call_once(|| {
                        self.memory_store(result, lazy_layout.get_value_ptr(lazy_ref) as _);
                    });
                }
                self.resume(caller_func, caller_instr);
            }
        }
    }

    fn resume(&mut self, func: Func, instr: Instr) {
        self.current_module = self.instance.engine.funcs[func].0;
        self.current_module_data = &self.instance.engine.modules[self.current_module];

        self.current_func = func;
        self.current_func_data = self.instance.engine.func_data(func);
        self.current_func_stack_map = self.function_stack_maps[func]
            .get_or_insert_with(|| {
                Arc::new(FunctionStackMap::new(
                    self.current_func_data,
                    self.current_module,
                    &self.instance.engine,
                ))
            })
            .clone();

        self.next_instr = instr;
    }

    fn call(&mut self, func_object: &FuncObject, args: &[Val]) {
        let caller_stack_map = self.current_func_stack_map.clone();
        self.resume(func_object.func, Instr::new(0));
        self.stack
            .push_frame(self.current_func_stack_map.layout.size());

        debug_assert_eq!(args.len(), self.current_func_data.params.len());

        for (dst, arg) in self.current_func_data.params.values().zip(args) {
            unsafe {
                self.stack.copy_from_caller(
                    caller_stack_map.local_offsets[*arg],
                    self.current_func_stack_map.local_offsets[dst.bind_to_val],
                    caller_stack_map.local_sizes[*arg],
                );
            }
        }

        unsafe {
            self.stack.store(
                self.current_func_stack_map.local_offsets[self.current_func_data.captures_val],
                func_object.captures,
            );
        }
    }

    /// Note: may trigger invocation of a lazy function
    /// and call `self.resume`; thus this function takes `&mut self`.
    unsafe fn memory_load(&mut self, src: *const u8, dst: Val) -> bool {
        let typ = self.instance.engine.type_registry.module_mapping[self.current_module]
            [self.current_func_data.vals[dst].typ];
        self.memory_load_impl(typ, src, self.current_func_stack_map.local_offsets[dst])
    }

    unsafe fn memory_load_impl(&mut self, typ: Type, src: *const u8, dst_offset: u32) -> bool {
        match &self.instance.engine.type_registry.types[typ].kind {
            TypeKind::Struct(s) => {
                for field in s.fields.values() {
                    self.memory_load_impl(
                        field.field_type,
                        src.add(field.offset),
                        dst_offset + field.offset as u32,
                    );
                }
            }
            TypeKind::Primitive(p) => match *p {
                PrimitiveType::Int => {
                    let val = (*src.cast::<AtomicI64>()).load(Ordering::Relaxed);
                    self.stack.store(dst_offset, val);
                }
                PrimitiveType::Real => {
                    let val = f64::from_bits((*src.cast::<AtomicU64>()).load(Ordering::Relaxed));
                    self.stack.store(dst_offset, val);
                }
                PrimitiveType::Bool => {
                    let val = (*src.cast::<AtomicBool>()).load(Ordering::Relaxed);
                    self.stack.store(dst_offset, val);
                }
                PrimitiveType::Unit => {}
            },
            TypeKind::Reference(_) | TypeKind::LazyReference(_) => {
                let val = (*src.cast::<AtomicPtr<u8>>()).load(Ordering::Relaxed);
                self.stack.store(dst_offset, MRef::new(val));
            }
            TypeKind::Lazy(lazy_type) => {
                let once = lazy_type.layout.get_once_ptr(src);
                let mut should_continue = true;
                once.call_once(|| {
                    let func_object = lazy_type.layout.get_initializer_func_ptr(src);
                    self.continuations.push(Continuation::WriteLazy {
                        lazy_layout: lazy_type.layout.clone(),
                        lazy_ref: src as _,
                        caller_func: self.current_func,
                        // we want to continue at _this_ instruction, not the next one,
                        // so that we end up loading the lazy value which should be initialized
                        // after continuing.
                        caller_instr: Instr::new(self.next_instr.index() - 1),
                    });
                    self.call(func_object, &[]);
                    should_continue = false;
                });
                if once.state() == OnceState::Done {
                    self.memory_load_impl(
                        lazy_type.value_type,
                        src.add(lazy_type.layout.value_offset),
                        dst_offset,
                    );
                }
                return should_continue;
            }
            TypeKind::Func(_) => {
                let val =
                    FuncObject::from_u128((*src.cast::<AtomicU128>()).load(Ordering::Relaxed));
                self.stack.store(dst_offset, val);
            }
        }
        true
    }

    unsafe fn memory_store(&self, src: Val, dst: *mut u8) {
        let typ = self.instance.engine.type_registry.module_mapping[self.current_module]
            [self.current_func_data.vals[src].typ];
        self.memory_store_impl(typ, self.current_func_stack_map.local_offsets[src], dst)
    }

    unsafe fn memory_store_impl(&self, typ: Type, src_offset: u32, dst: *mut u8) {
        match &self.instance.engine.type_registry.types[typ].kind {
            TypeKind::Struct(s) => {
                for field in s.fields.values() {
                    self.memory_store_impl(
                        field.field_type,
                        src_offset + field.offset as u32,
                        dst.add(field.offset),
                    );
                }
            }
            TypeKind::Primitive(p) => match *p {
                PrimitiveType::Int => {
                    let val = self.stack.load::<i64>(src_offset);
                    unsafe {
                        (*dst.cast::<AtomicI64>()).store(val, Ordering::Relaxed);
                    }
                }
                PrimitiveType::Real => {
                    let val = self.stack.load::<f64>(src_offset);
                    unsafe {
                        (*dst.cast::<AtomicU64>()).store(val.to_bits(), Ordering::Relaxed);
                    }
                }
                PrimitiveType::Bool => {
                    let val = self.stack.load::<bool>(src_offset);
                    unsafe {
                        (*dst.cast::<AtomicBool>()).store(val, Ordering::Relaxed);
                    }
                }
                PrimitiveType::Unit => {}
            },
            TypeKind::Reference(_) | TypeKind::LazyReference(_) => {
                let val = self.stack.load::<MRef>(src_offset);
                unsafe {
                    (*dst.cast::<AtomicPtr<u8>>()).store(val.as_ptr(), Ordering::Relaxed);
                }
            }
            TypeKind::Lazy(lazy_type) => {
                let value_ptr = lazy_type.layout.get_value_ptr(dst) as *mut u8;
                self.memory_store_impl(lazy_type.value_type, src_offset, value_ptr);
                // Mark initialized
                lazy_type.layout.get_once_ptr(dst).call_once(|| ());
            }
            TypeKind::Func(_) => {
                let val = self.stack.load::<FuncObject>(src_offset);
                unsafe {
                    (*dst.cast::<AtomicU128>()).store(val.to_u128(), Ordering::Relaxed);
                }
            }
        }
    }

    #[inline]
    fn load_local<T: Copy>(&self, local: Val) -> T {
        unsafe {
            self.stack
                .load(self.current_func_stack_map.local_offsets[local])
        }
    }

    #[inline]
    fn store_local<T: Copy>(&self, local: Val, value: T) {
        unsafe {
            self.stack
                .store(self.current_func_stack_map.local_offsets[local], value);
        }
    }

    fn stack_walker(&self) -> impl StackWalker + '_ {
        struct Walker<'a> {
            instance: &'a Instance,
            stack: &'a Stack,
            current_frame: usize,
            current_offset: usize,
            current_func: Func,
            current_func_data: &'a FuncData,
            current_func_stack_map: &'a FunctionStackMap,
            func_stack_maps: &'a SecondaryMap<Func, Option<Arc<FunctionStackMap>>>,
            current_module: Module,
            locals_iter: cranelift_entity::Iter<'a, Val, ValData>,
            conts: Rev<slice::Iter<'a, Continuation>>,
            refs: Vec<MRef>,
        }

        unsafe impl Send for Walker<'_> {}

        impl StackWalker for Walker<'_> {
            fn next(&mut self) -> Option<MRef> {
                if let Some(r) = self.refs.pop() {
                    return Some(r);
                }

                match self.locals_iter.next() {
                    Some((local, local_data)) => {
                        let typ = self.instance.engine.type_registry.module_mapping
                            [self.current_module][local_data.typ];
                        unsafe {
                            let ptr = self.stack.get_pointer_absolute(
                                self.current_offset
                                    + self.current_func_stack_map.local_offsets[local] as usize,
                            );
                            self.instance
                                .engine
                                .type_registry
                                .traverse_references(ptr, typ, |r| {
                                    self.refs.push(r);
                                });
                        }
                        self.next()
                    }
                    None => {
                        let next_offset = self.stack.frame_offset(self.current_frame + 1)?;
                        let next_func = match self.conts.next()? {
                            Continuation::ResumeCaller { caller_func, .. } => *caller_func,
                            Continuation::WriteLazy { caller_func, .. } => *caller_func,
                        };

                        self.current_frame += 1;
                        self.current_offset = next_offset;
                        self.current_func = next_func;
                        self.current_func_data = self.instance.engine.func_data(next_func);
                        self.current_func_stack_map =
                            self.func_stack_maps[next_func].as_ref().unwrap();
                        self.current_module = self.instance.engine.funcs[next_func].0;
                        self.locals_iter = self.current_func_data.vals.iter();
                        self.next()
                    }
                }
            }
        }

        Walker {
            instance: self.instance,
            stack: self.stack,
            func_stack_maps: self.function_stack_maps,
            current_frame: 0,
            current_offset: self.stack.frame_offset(0).unwrap(),
            current_func: self.current_func,
            current_func_data: self.current_func_data,
            current_module: self.current_module,
            current_func_stack_map: &self.current_func_stack_map,
            locals_iter: self.current_func_data.vals.iter(),
            conts: self.continuations.iter().rev(),
            refs: Vec::new(),
        }
    }

    fn local_to_value(&self, local: Val) -> Value {
        let typ = self
            .instance
            .engine
            .type_registry
            .local_type_data(self.current_module, self.current_func_data.vals[local].typ);
        match &typ.kind {
            TypeKind::Primitive(p) => match *p {
                PrimitiveType::Int => Value::Int(self.load_local::<i64>(local)),
                PrimitiveType::Real => Value::Real(self.load_local::<f64>(local)),
                PrimitiveType::Bool => Value::Bool(self.load_local::<bool>(local)),
                PrimitiveType::Unit => Value::Unit,
            },
            _ => todo!("unimplemented Value variant"),
        }
    }
}

/// Encodes what to do after encountering a `Return` instruction.
#[derive(Debug, Clone)]
enum Continuation {
    /// Resume execution of a calling function, placing
    /// the return value into a local of the calling function.
    ResumeCaller {
        caller_func: Func,
        /// Instruction to resume at
        caller_instr: Instr,
        /// Destination offset for return value
        return_value_dst: u32,
    },
    /// Write the return value of the function into a `Lazy`
    /// value, then resume execution of a caller function
    /// (without placing the return value into a local).
    WriteLazy {
        lazy_layout: LazyLayout,
        lazy_ref: *mut u8,
        caller_func: Func,
        caller_instr: Instr,
    },
}

unsafe impl Send for Continuation {}
