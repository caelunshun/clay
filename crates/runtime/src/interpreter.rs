use crate::{
    engine::{Engine, Func, Instance, Module},
    gc::StackWalker,
    ptr::MRef,
    type_registry::{Type, TypeKind},
};
use bytecode::{
    instr::CompareMode,
    module::{ConstantData, FuncData},
    Instr, InstrData, Local, ModuleData, PrimitiveType,
};
use bytemuck::{NoUninit, Pod};
use cranelift_entity::{
    packed_option::{PackedOption, ReservedValue},
    EntityRef, SecondaryMap,
};
use std::{
    alloc::Layout,
    ptr::NonNull,
    sync::atomic::{AtomicBool, AtomicI64, AtomicPtr, AtomicU64, AtomicU8, Ordering},
};

macro_rules! invalid_bytecode {
    () => {
        panic!("invalid bytecode encountered")
    };
}

/// Cached interpreter state.
pub struct Interpreter {
    stack: Stack,
    function_stack_maps: SecondaryMap<Func, Option<FunctionStackMap>>,
    current_func: Option<Func>,
    current_instr: Instr,
    /// Local in the calling function to place the return value
    /// from the current function. Arbitrary if we're at the top of
    /// the stack.
    #[expect(unused)]
    return_target: Local,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            stack: Stack::new(),
            function_stack_maps: SecondaryMap::default(),
            current_func: None,
            current_instr: Instr::reserved_value(),
            return_target: Local::reserved_value(),
        }
    }

    /// Execute the given function in the given instance,
    /// currently providing no parameters
    /// and assuming that the return value is an `int`.
    pub fn interp(&mut self, func: Func, instance: &Instance) -> i64 {
        self.current_func = None;
        self.interp_func(func, instance, &[], true).unwrap()
    }

    /// Args provided as locals in the calling function.
    fn interp_func(
        &mut self,
        func: Func,
        instance: &Instance,
        args: &[Local],
        return_int: bool,
    ) -> Option<i64> {
        if !args.is_empty() {
            todo!();
        }

        let func_data = instance.engine.func_data(func);

        let module = instance.engine.funcs[func].0;
        let module_data = &instance.engine.modules[module];

        let func_stack_map = self.function_stack_maps[func].get_or_insert_with(|| {
            FunctionStackMap::new(func_data, instance.engine.funcs[func].0, &instance.engine)
        });

        let return_address = self.current_func;
        self.stack.push_frame(return_address, func_stack_map);

        self.current_func = Some(func);
        self.current_instr = Instr::new(0);

        let ret_val = self.interp_func_instrs(func, func_data, module, module_data, instance);

        let func_stack_map = self.function_stack_maps[func].as_ref().unwrap(); // reborrow
        let ret_val = if return_int {
            Some(self.stack.load(func_stack_map.local_offsets[ret_val]))
        } else {
            todo!()
        };

        self.stack.pop_frame(&func_stack_map);

        ret_val
    }

    /// Interpret until return, then yield the return value local
    /// without popping the stack frame.
    fn interp_func_instrs(
        &mut self,
        func: Func,
        func_data: &FuncData,
        module: Module,
        module_data: &ModuleData,

        instance: &Instance,
    ) -> Local {
        let func_stack_map = self.function_stack_maps[func].as_ref().unwrap();

        /// Helper to quickly load/store Locals with automatic offset
        /// lookup.
        struct StackHelper<'a> {
            stack: &'a mut Stack,
            func_stack_map: &'a FunctionStackMap,
        }

        impl<'a> StackHelper<'a> {
            pub fn load<T: Pod>(&self, local: Local) -> T {
                self.stack.load(self.func_stack_map.local_offsets[local])
            }

            pub fn load_bool(&self, local: Local) -> bool {
                self.load::<u8>(local) == 1
            }

            pub fn store<T: NoUninit>(&mut self, local: Local, value: T) {
                self.stack
                    .store(self.func_stack_map.local_offsets[local], value)
            }
        }

        let mut locals = StackHelper {
            stack: &mut self.stack,
            func_stack_map,
        };

        loop {
            let instr = &func_data.instrs[self.current_instr];
            match instr {
                InstrData::Jump(instr) => {
                    self.current_instr = instr.target;

                    let mut walker = locals
                        .stack
                        .walker(func, instance, &self.function_stack_maps);
                    instance.gc.safepoint(instance, &mut walker);

                    continue;
                }
                InstrData::Branch(instr) => {
                    if locals.load_bool(instr.condition) {
                        self.current_instr = instr.target;

                        let mut walker =
                            locals
                                .stack
                                .walker(func, instance, &self.function_stack_maps);
                        instance.gc.safepoint(instance, &mut walker);

                        continue;
                    }
                }
                InstrData::Call(_) => {
                    todo!()
                }
                InstrData::Return(instr) => {
                    return instr.return_value;
                }
                InstrData::Copy(instr) => {
                    let typ = func_data.locals[instr.src].typ;
                    let typ = instance.engine.type_registry.module_mapping[module][typ];
                    let layout = instance.engine.type_registry.layouts[typ].unwrap();

                    locals.stack.copy(
                        locals.func_stack_map.local_offsets[instr.src],
                        locals.func_stack_map.local_offsets[instr.dst],
                        layout.size() as u32,
                    );
                }
                InstrData::IntConstant(instr) => {
                    let ConstantData::Int(x) = module_data.constants[instr.constant] else {
                        invalid_bytecode!()
                    };
                    locals.store(instr.dst, x);
                }
                InstrData::IntAdd(instr) => {
                    let lhs = locals.load::<i64>(instr.src1);
                    let rhs = locals.load::<i64>(instr.src2);
                    let result = lhs.wrapping_add(rhs);
                    locals.store(instr.dst, result);
                }
                InstrData::IntSub(instr) => {
                    let lhs = locals.load::<i64>(instr.src1);
                    let rhs = locals.load::<i64>(instr.src2);
                    let result = lhs.wrapping_sub(rhs);
                    locals.store(instr.dst, result);
                }
                InstrData::IntMul(instr) => {
                    let lhs = locals.load::<i64>(instr.src1);
                    let rhs = locals.load::<i64>(instr.src2);
                    let result = lhs.wrapping_mul(rhs);
                    locals.store(instr.dst, result);
                }
                InstrData::IntDiv(instr) => {
                    let lhs = locals.load::<i64>(instr.src1);
                    let rhs = locals.load::<i64>(instr.src2);
                    let result = lhs.wrapping_div(rhs);
                    locals.store(instr.dst, result);
                }
                InstrData::IntCmp(instr) => {
                    let lhs = locals.load::<i64>(instr.src1);
                    let rhs = locals.load::<i64>(instr.src2);
                    let result = match instr.mode {
                        CompareMode::Less => lhs < rhs,
                        CompareMode::LessOrEqual => lhs <= rhs,
                        CompareMode::Greater => lhs > rhs,
                        CompareMode::GreaterOrEqual => lhs >= rhs,
                        CompareMode::Equal => lhs == rhs,
                        CompareMode::NotEqual => lhs != rhs,
                    };
                    locals.store(instr.dst, result);
                }
                InstrData::RealConstant(instr) => {
                    let ConstantData::Real(x) = module_data.constants[instr.constant] else {
                        invalid_bytecode!()
                    };
                    locals.store(instr.dst, x);
                }
                InstrData::RealAdd(instr) => {
                    let lhs = locals.load::<f64>(instr.src1);
                    let rhs = locals.load::<f64>(instr.src2);
                    let result = lhs + rhs;
                    locals.store(instr.dst, result);
                }
                InstrData::RealSub(instr) => {
                    let lhs = locals.load::<f64>(instr.src1);
                    let rhs = locals.load::<f64>(instr.src2);
                    let result = lhs - rhs;
                    locals.store(instr.dst, result);
                }
                InstrData::RealMul(instr) => {
                    let lhs = locals.load::<f64>(instr.src1);
                    let rhs = locals.load::<f64>(instr.src2);
                    let result = lhs * rhs;
                    locals.store(instr.dst, result);
                }
                InstrData::RealDiv(instr) => {
                    let lhs = locals.load::<f64>(instr.src1);
                    let rhs = locals.load::<f64>(instr.src2);
                    let result = lhs / rhs;
                    locals.store(instr.dst, result);
                }
                InstrData::RealCmp(instr) => {
                    let lhs = locals.load::<f64>(instr.src1);
                    let rhs = locals.load::<f64>(instr.src2);
                    let result = match instr.mode {
                        CompareMode::Less => lhs < rhs,
                        CompareMode::LessOrEqual => lhs <= rhs,
                        CompareMode::Greater => lhs > rhs,
                        CompareMode::GreaterOrEqual => lhs >= rhs,
                        CompareMode::Equal => lhs == rhs,
                        CompareMode::NotEqual => lhs != rhs,
                    };
                    locals.store(instr.dst, result);
                }
                InstrData::BoolConstant(instr) => {
                    let ConstantData::Bool(x) = module_data.constants[instr.constant] else {
                        invalid_bytecode!()
                    };
                    locals.store(instr.dst, x);
                }
                InstrData::BoolAnd(instr) => {
                    let lhs = locals.load_bool(instr.src1);
                    let rhs = locals.load_bool(instr.src2);
                    let result = lhs & rhs;
                    locals.store(instr.dst, result);
                }
                InstrData::BoolOr(instr) => {
                    let lhs = locals.load_bool(instr.src1);
                    let rhs = locals.load_bool(instr.src2);
                    let result = lhs | rhs;
                    locals.store(instr.dst, result);
                }
                InstrData::BoolXor(instr) => {
                    let lhs = locals.load_bool(instr.src1);
                    let rhs = locals.load_bool(instr.src2);
                    let result = lhs ^ rhs;
                    locals.store(instr.dst, result);
                }
                InstrData::BoolNot(instr) => {
                    let src = locals.load_bool(instr.src);
                    let result = !src;
                    locals.store(instr.dst, result);
                }
                InstrData::InitStruct(instr) => {
                    let field_vals = instr.fields.as_slice(&func_data.local_pool);
                    let struct_layout = instance
                        .engine
                        .type_registry
                        .local_type_data(module, instr.typ);
                    let TypeKind::Struct(struct_layout) = &struct_layout.kind else {
                        invalid_bytecode!()
                    };

                    let struct_base = locals.func_stack_map.local_offsets[instr.dst];

                    for (field, field_val) in struct_layout.fields.values().zip(field_vals) {
                        let src_offset = locals.func_stack_map.local_offsets[*field_val];
                        let dst_offset = struct_base + field.offset as u32;
                        let size = field.size as u32;

                        locals.stack.copy(src_offset, dst_offset, size);
                    }
                }
                InstrData::GetField(instr) => {
                    let struct_layout = instance
                        .engine
                        .type_registry
                        .local_type_data(module, func_data.locals[instr.src_struct].typ);
                    let TypeKind::Struct(struct_layout) = &struct_layout.kind else {
                        invalid_bytecode!()
                    };
                    let field_layout = &struct_layout.fields[instr.field];

                    let src_offset = locals.func_stack_map.local_offsets[instr.src_struct]
                        + field_layout.offset as u32;
                    let dst_offset = locals.func_stack_map.local_offsets[instr.dst];
                    locals
                        .stack
                        .copy(src_offset, dst_offset, field_layout.size as u32);
                }
                InstrData::SetField(instr) => {
                    let struct_layout = instance
                        .engine
                        .type_registry
                        .local_type_data(module, func_data.locals[instr.dst_struct].typ);
                    let TypeKind::Struct(struct_layout) = &struct_layout.kind else {
                        invalid_bytecode!()
                    };
                    let field_layout = &struct_layout.fields[instr.field];

                    let src_offset = locals.func_stack_map.local_offsets[instr.src];
                    let dst_offset = locals.func_stack_map.local_offsets[instr.dst_struct]
                        + field_layout.offset as u32;
                    locals
                        .stack
                        .copy(src_offset, dst_offset, field_layout.size as u32);
                }
                InstrData::Alloc(instr) => {
                    let mut walker = locals
                        .stack
                        .walker(func, instance, &self.function_stack_maps);

                    let local_type = func_data.locals[instr.src].typ;
                    let typ = instance.engine.type_registry.module_mapping[module][local_type];

                    let mref = instance.gc.allocate(instance, typ, &mut walker);
                    drop(walker);

                    locals.store(instr.dst_ref, mref);

                    unsafe {
                        memory_store(
                            &locals.stack,
                            locals.func_stack_map.local_offsets[instr.src],
                            typ,
                            mref,
                            0,
                            instance,
                        );
                    }
                }
                InstrData::Load(instr) => {
                    let r = locals.load::<MRef>(instr.src_ref);
                    let local_type = func_data.locals[instr.dst].typ;
                    let typ = instance.engine.type_registry.module_mapping[module][local_type];

                    unsafe {
                        memory_load(
                            r,
                            0,
                            typ,
                            &mut locals.stack,
                            locals.func_stack_map.local_offsets[instr.src_ref],
                            instance,
                        );
                    }
                }
                InstrData::LoadField(instr) => {
                    let r = locals.load::<MRef>(instr.src_ref);

                    let field_type = func_data.locals[instr.dst].typ;
                    let field_type =
                        instance.engine.type_registry.module_mapping[module][field_type];

                    let struct_type = func_data.locals[instr.src_ref].typ;
                    let struct_type =
                        instance.engine.type_registry.module_mapping[module][struct_type];
                    let TypeKind::Reference(s) =
                        &instance.engine.type_registry.types[struct_type].kind
                    else {
                        invalid_bytecode!()
                    };
                    let TypeKind::Struct(s) = &instance.engine.type_registry.types[*s].kind else {
                        invalid_bytecode!()
                    };

                    let offset = s.fields[instr.field].offset;

                    unsafe {
                        memory_load(
                            r,
                            offset as u32,
                            field_type,
                            &mut locals.stack,
                            locals.func_stack_map.local_offsets[instr.dst],
                            instance,
                        );
                    }
                }
                InstrData::Store(instr) => {
                    let r = locals.load::<MRef>(instr.dst_ref);

                    let local_type = func_data.locals[instr.src_val].typ;
                    let typ = instance.engine.type_registry.module_mapping[module][local_type];
                    let src_offset = locals.func_stack_map.local_offsets[instr.src_val];

                    unsafe {
                        memory_store(&locals.stack, src_offset, typ, r, 0, instance);
                    }
                }
                InstrData::StoreField(instr) => {
                    let r = locals.load::<MRef>(instr.dst_ref);
                    let field_type = func_data.locals[instr.src_val].typ;
                    let field_type =
                        instance.engine.type_registry.module_mapping[module][field_type];

                    let struct_type = func_data.locals[instr.dst_ref].typ;
                    let struct_type =
                        instance.engine.type_registry.module_mapping[module][struct_type];

                    let TypeKind::Reference(s) =
                        &instance.engine.type_registry.types[struct_type].kind
                    else {
                        invalid_bytecode!()
                    };
                    let TypeKind::Struct(s) = &instance.engine.type_registry.types[*s].kind else {
                        invalid_bytecode!()
                    };

                    let src_offset = locals.func_stack_map.local_offsets[instr.src_val];
                    let dst_offset = s.fields[instr.field].offset;

                    unsafe {
                        memory_store(
                            &locals.stack,
                            src_offset,
                            field_type,
                            r,
                            dst_offset as u32,
                            instance,
                        );
                    }
                }
                InstrData::MakeFunctionObject(_) => todo!(),
            }

            self.current_instr = Instr::new(self.current_instr.index() + 1);
        }
    }
}

/// Contains locals used by bytecode instructions
/// for each Zyon function on the call stack.
///
/// The size of each function's stack is known ahead of time
/// (cached in `Interpreter.function_stack_maps`).
///
/// The underlying memory uses `Vec<u64>` to ensure
/// stack frames are aligned to 8 bytes.
#[derive(Debug)]
struct Stack {
    data: Vec<u64>,
    /// Start of the current stack frame.
    offset: usize,
}

impl Stack {
    pub const fn new() -> Self {
        Self {
            data: Vec::new(),
            offset: 0,
        }
    }

    /// Begins a new stack frame for the given function.
    pub fn push_frame(
        &mut self,
        return_address: Option<Func>,
        new_function_stack_map: &FunctionStackMap,
    ) {
        self.offset = self.data.len() * size_of::<u64>();

        let num_words = new_function_stack_map
            .layout
            .size()
            .div_ceil(size_of::<u64>());
        self.data.extend((0..num_words).map(|_| 0));

        self.store(0, PackedOption::from(return_address));
    }

    /// Pops the current stack frame, returning the `Func`
    /// to return to.
    pub fn pop_frame(&mut self, current_function_stack_map: &FunctionStackMap) -> Option<Func> {
        let return_address = self.load::<ReturnAddress>(0);

        let num_words = current_function_stack_map
            .layout
            .size()
            .div_ceil(size_of::<u64>());
        let new_len = self.data.len() - num_words;
        self.data.truncate(new_len);

        return_address.into()
    }

    /// Loads a `Pod` value from the stack at the given offset.
    pub fn load<T: Pod>(&self, offset: u32) -> T {
        let offset = self.offset + usize::try_from(offset).unwrap();
        let bytes = &self.data()[offset..][..size_of::<T>()];
        *bytemuck::from_bytes(bytes)
    }

    /// Stores a `Pod` value onto the stack at the given offset.
    pub fn store<T: NoUninit>(&mut self, offset: u32, value: T) {
        let offset = self.offset + usize::try_from(offset).unwrap();
        let bytes = &mut self.data_mut()[offset..][..size_of::<T>()];
        bytes.copy_from_slice(bytemuck::bytes_of(&value));
    }

    /// Copies a value of dynamic size from one offset to another.
    pub fn copy(&mut self, src_offset: u32, dst_offset: u32, size: u32) {
        let src_offset = self.offset + usize::try_from(src_offset).unwrap();
        let dst_offset = self.offset + usize::try_from(dst_offset).unwrap();

        self.data_mut().copy_within(
            src_offset..src_offset + usize::try_from(size).unwrap(),
            dst_offset,
        );
    }

    pub fn data(&self) -> &[u8] {
        bytemuck::cast_slice(&self.data)
    }

    pub fn data_mut(&mut self) -> &mut [u8] {
        bytemuck::cast_slice_mut(&mut self.data)
    }

    pub fn walker<'a>(
        &'a self,
        current_func: Func,
        instance: &'a Instance,
        func_stack_maps: &'a SecondaryMap<Func, Option<FunctionStackMap>>,
    ) -> impl StackWalker + 'a {
        struct Walker<'a> {
            data: &'a [u8],
            current_offset: usize,
            current_func: Func,
            local_offsets_iter: cranelift_entity::Iter<'a, Local, u32>,
            current_refs: Vec<MRef>,

            instance: &'a Instance,
            func_stack_maps: &'a SecondaryMap<Func, Option<FunctionStackMap>>,
        }

        impl StackWalker for Walker<'_> {
            fn next(&mut self) -> Option<MRef> {
                if let Some(r) = self.current_refs.pop() {
                    return Some(r);
                }

                let (local, local_offset) = match self.local_offsets_iter.next() {
                    Some(x) => x,
                    None => {
                        // walk up the stack
                        let return_address: ReturnAddress = *bytemuck::from_bytes(
                            &self.data[self.current_offset..][..size_of::<ReturnAddress>()],
                        );
                        return match return_address.into() {
                            Some(next) => {
                                self.current_offset -= self.func_stack_maps[self.current_func]
                                    .as_ref()
                                    .unwrap()
                                    .layout
                                    .size();
                                self.current_func = next;
                                self.local_offsets_iter = self.func_stack_maps[self.current_func]
                                    .as_ref()
                                    .unwrap()
                                    .local_offsets
                                    .iter();
                                self.next()
                            }
                            None => None,
                        };
                    }
                };

                let local_type =
                    self.instance.engine.func_data(self.current_func).locals[local].typ;
                let local_type = self.instance.engine.type_registry.module_mapping
                    [self.instance.engine.funcs[self.current_func].0][local_type];

                self.instance
                    .engine
                    .type_registry
                    .traverse_references(local_type, |ref_offset| {
                        let bytes = &self.data
                            [self.current_offset + *local_offset as usize + ref_offset..]
                            [..size_of::<MRef>()];
                        self.current_refs.push(*bytemuck::from_bytes(bytes));
                    });
                self.next()
            }
        }

        Walker {
            data: self.data(),
            current_offset: self.offset,
            current_func,
            local_offsets_iter: func_stack_maps[current_func]
                .as_ref()
                .unwrap()
                .local_offsets
                .iter(),
            current_refs: Vec::new(),
            instance,
            func_stack_maps,
        }
    }
}

type ReturnAddress = PackedOption<Func>;

/// Cached stack map for a function, mapping `Local`
/// indices to their offset from the start of the stack frame.
///
/// Each stack frame
/// begins with a `PackedOption<Func>` value containing the "return address".
#[derive(Debug, Clone)]
struct FunctionStackMap {
    layout: Layout,
    local_offsets: SecondaryMap<Local, u32>,
}

impl FunctionStackMap {
    pub fn new(func: &FuncData, module: Module, engine: &Engine) -> Self {
        let mut layout = Layout::new::<ReturnAddress>();
        let mut local_offsets = SecondaryMap::default();

        for (local, local_data) in &func.locals {
            let local_type = engine.type_registry.module_mapping[module][local_data.typ];
            let local_layout = engine.type_registry.layouts[local_type].unwrap();

            let (new_layout, offset) = layout.extend(local_layout).unwrap();
            local_offsets[local] = offset.try_into().unwrap();

            layout = new_layout;
        }

        const FRAME_ALIGNMENT: usize = 8;

        assert!(
            layout.align() <= FRAME_ALIGNMENT,
            "alignment > {FRAME_ALIGNMENT} for stack-allocated values not yet supported"
        );
        // Size gets rounded up to a multiple of FRAME_ALIGNMENT.
        let layout = Layout::from_size_align(
            layout.size().div_ceil(FRAME_ALIGNMENT) * FRAME_ALIGNMENT,
            layout.align(),
        )
        .unwrap();

        Self {
            layout,
            local_offsets,
        }
    }
}

unsafe fn memory_load(
    src_ref: MRef,
    src_offset: u32,
    typ: Type,
    dst_stack: &mut Stack,
    dst_offset: u32,
    instance: &Instance,
) {
    let type_data = &instance.engine.type_registry.types[typ];
    let src = src_ref.as_ptr().add(src_offset as usize);
    match &type_data.kind {
        TypeKind::Struct(struct_) => {
            for field_layout in struct_.fields.values() {
                memory_load(
                    src_ref,
                    src_offset + field_layout.offset as u32,
                    field_layout.field_type,
                    dst_stack,
                    dst_offset + field_layout.offset as u32,
                    instance,
                );
            }
        }
        TypeKind::Primitive(p) => match *p {
            PrimitiveType::Int => {
                let val = unsafe { (*src.cast::<AtomicI64>()).load(Ordering::Relaxed) };
                dst_stack.store(dst_offset, val);
            }
            PrimitiveType::Real => {
                let val =
                    f64::from_bits(unsafe { (*src.cast::<AtomicU64>()).load(Ordering::Relaxed) });
                dst_stack.store(dst_offset, val);
            }
            PrimitiveType::Bool => {
                let val = unsafe { (*src.cast::<AtomicBool>()).load(Ordering::Relaxed) };
                dst_stack.store(dst_offset, val);
            }
            PrimitiveType::Unit => {}
        },
        TypeKind::Reference(_) => {
            let val = unsafe { (*src.cast::<AtomicPtr<u8>>()).load(Ordering::Relaxed) };
            dst_stack.store(dst_offset, unsafe { MRef::new(NonNull::new(val).unwrap()) });
        }
        TypeKind::Lazy(_) => todo!(),
        TypeKind::Func(_) => todo!(),
    }
}

unsafe fn memory_store(
    src_stack: &Stack,
    src_offset: u32,
    typ: Type,
    dst_ref: MRef,
    dst_offset: u32,
    instance: &Instance,
) {
    let type_data = &instance.engine.type_registry.types[typ];
    let dst = dst_ref.as_ptr().add(dst_offset as usize);
    match &type_data.kind {
        TypeKind::Struct(struct_) => {
            for field_layout in struct_.fields.values() {
                memory_store(
                    src_stack,
                    src_offset + field_layout.offset as u32,
                    field_layout.field_type,
                    dst_ref,
                    dst_offset + field_layout.offset as u32,
                    instance,
                );
            }
        }
        TypeKind::Primitive(p) => match *p {
            PrimitiveType::Int => {
                let val = src_stack.load(src_offset);
                unsafe {
                    (*dst.cast::<AtomicI64>()).store(val, Ordering::Relaxed);
                }
            }
            PrimitiveType::Real => {
                let val = src_stack.load::<f64>(src_offset);
                unsafe {
                    (*dst.cast::<AtomicU64>()).store(val.to_bits(), Ordering::Relaxed);
                }
            }
            PrimitiveType::Bool => {
                let val = src_stack.load::<u8>(src_offset);
                unsafe {
                    (*dst.cast::<AtomicU8>()).store(val, Ordering::Relaxed);
                }
            }
            PrimitiveType::Unit => {}
        },
        TypeKind::Reference(_) => {
            let val = src_stack.load::<MRef>(src_offset);
            unsafe {
                (*dst.cast::<AtomicPtr<u8>>()).store(val.as_ptr(), Ordering::Relaxed);
            }
        }
        TypeKind::Lazy(_) => todo!(),
        TypeKind::Func(_) => todo!(),
    }
}
