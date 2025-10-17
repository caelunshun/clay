use bytecode::{
    instr,
    module::{
        ConstantData, FieldData, FuncData, FuncParamData, FuncTypeData, StructTypeData, ValData,
    },
    Instr, InstrData, ModuleData, Type,
};
use cranelift_entity::{packed_option::ReservedValue, EntityList, EntityRef, PrimaryMap};
use fir_runtime::{Error, Func, Instance, Value};

extern crate fir_bytecode as bytecode;

#[test]
fn factorial() {
    tracing_subscriber::fmt::try_init().ok();

    let mut module = ModuleData::default();
    let int = module
        .types
        .push(bytecode::TypeData::Primitive(bytecode::PrimitiveType::Int));
    let bool_ = module
        .types
        .push(bytecode::TypeData::Primitive(bytecode::PrimitiveType::Bool));

    let mut func = FuncData::new_no_captures(&mut module);

    let x = func.vals.push(ValData::new(int));
    let i = func.vals.push(ValData::new(int));
    let n = func.vals.push(ValData::new(int));
    let one = func.vals.push(ValData::new(int));
    let condition = func.vals.push(ValData::new(bool_));

    func.instr(InstrData::IntConstant(instr::ConstantInstr {
        dst: x,
        constant: module.constants.push(ConstantData::Int(1)),
    }));
    func.instr(InstrData::IntConstant(instr::ConstantInstr {
        dst: i,
        constant: module.constant(ConstantData::Int(1)),
    }));
    func.instr(InstrData::IntConstant(instr::ConstantInstr {
        dst: n,
        constant: module.constant(ConstantData::Int(10)),
    }));
    func.instr(InstrData::IntConstant(instr::ConstantInstr {
        dst: one,
        constant: module.constant(ConstantData::Int(1)),
    }));

    let loop_start = func.instr(InstrData::IntMul(instr::Binary {
        dst: x,
        src1: x,
        src2: i,
    }));
    func.instr(InstrData::IntAdd(instr::Binary {
        dst: i,
        src1: i,
        src2: one,
    }));
    func.instr(InstrData::IntCmp(instr::Cmp {
        dst: condition,
        src1: i,
        src2: n,
        mode: instr::CompareMode::LessOrEqual,
    }));
    func.instr(InstrData::Branch(instr::Branch {
        condition,
        target: loop_start,
    }));
    func.instr(InstrData::Return(instr::Return { return_value: x }));

    module.funcs.push(func);

    let instance = Instance::new_test(module, 1024);
    assert_eq!(
        instance.interp_bare(Func::new(0)).unwrap(),
        Value::Int(3628800)
    ); // 10!
}

// Tests garbage collection by repeatedly making a big linked list.
#[test]
fn linked_list() {
    tracing_subscriber::fmt::try_init().ok();

    let mut module = ModuleData::default();
    let int = module
        .types
        .push(bytecode::TypeData::Primitive(bytecode::PrimitiveType::Int));
    let bool_ = module
        .types
        .push(bytecode::TypeData::Primitive(bytecode::PrimitiveType::Bool));

    let node_type = module.types.next_key();
    let node_ref_type = Type::new(node_type.index() + 1);

    let mut node_fields = PrimaryMap::default();
    let _prev_field = node_fields.push(FieldData {
        name: "prev".into(),
        typ: node_ref_type,
    });
    let _has_prev_field = node_fields.push(FieldData {
        name: "has_prev".into(),
        typ: bool_,
    });
    let next_field = node_fields.push(FieldData {
        name: "next".into(),
        typ: node_ref_type,
    });
    let has_next_field = node_fields.push(FieldData {
        name: "has_next".into(),
        typ: bool_,
    });
    let val_field = node_fields.push(FieldData {
        name: "val".into(),
        typ: int,
    });

    module
        .types
        .push(bytecode::TypeData::Struct(StructTypeData {
            name: "Node".into(),
            fields: node_fields,
        }));
    module.types.push(bytecode::TypeData::Reference(node_type));

    let mut func = FuncData::new_no_captures(&mut module);

    let head = func.val(node_ref_type);
    let has_head = func.val(bool_);
    let node = func.val(node_type);
    let temp_ref = func.val(node_ref_type);
    let uninit_ref = func.val(node_ref_type);
    let i = func.val(int);
    let j = func.val(int);
    let n = func.val(int);
    let k = func.val(int);
    let one = func.val(int);
    let condition = func.val(bool_);
    let false_ = func.val(bool_);
    let true_ = func.val(bool_);

    func.instr(InstrData::IntConstant(instr::ConstantInstr {
        dst: one,
        constant: module.constant(ConstantData::Int(1)),
    }));
    func.instr(InstrData::IntConstant(instr::ConstantInstr {
        dst: i,
        constant: module.constant(ConstantData::Int(0)),
    }));
    func.instr(InstrData::IntConstant(instr::ConstantInstr {
        dst: j,
        constant: module.constant(ConstantData::Int(0)),
    }));
    func.instr(InstrData::IntConstant(instr::ConstantInstr {
        dst: n,
        constant: module.constant(ConstantData::Int(1000)),
    }));
    func.instr(InstrData::IntConstant(instr::ConstantInstr {
        dst: k,
        constant: module.constant(ConstantData::Int(100)),
    }));
    func.instr(InstrData::BoolConstant(instr::ConstantInstr {
        dst: has_head,
        constant: module.constant(ConstantData::Bool(false)),
    }));
    func.instr(InstrData::BoolConstant(instr::ConstantInstr {
        dst: false_,
        constant: module.constant(ConstantData::Bool(false)),
    }));
    func.instr(InstrData::BoolConstant(instr::ConstantInstr {
        dst: true_,
        constant: module.constant(ConstantData::Bool(true)),
    }));

    let loop_start = func.instr(InstrData::Branch(instr::Branch {
        condition: has_head,
        target: Instr::reserved_value(), // initialized later
    }));

    // !has_head case - initialize head
    let fields = EntityList::from_slice(
        &[uninit_ref, false_, uninit_ref, false_, i],
        &mut func.val_lists,
    );
    func.instr(InstrData::InitStruct(instr::InitStruct {
        dst: node,
        typ: node_type,
        fields,
    }));
    func.instr(InstrData::Alloc(instr::Alloc {
        dst_ref: head,
        src: node,
    }));
    func.instr(InstrData::BoolConstant(instr::ConstantInstr {
        dst: has_head,
        constant: module.constant(ConstantData::Bool(true)),
    }));
    func.instr(InstrData::IntAdd(instr::Binary {
        dst: i,
        src1: i,
        src2: one,
    }));
    func.instr(InstrData::Jump(instr::Jump { target: loop_start }));

    // has_head case - append
    let fields = EntityList::from_slice(&[head, true_, uninit_ref, false_, i], &mut func.val_lists);
    let append_start = func.instr(InstrData::InitStruct(instr::InitStruct {
        dst: node,
        typ: node_type,
        fields,
    }));
    func.instrs[loop_start].set_branch_target(append_start);

    func.instr(InstrData::Alloc(instr::Alloc {
        dst_ref: temp_ref,
        src: node,
    }));
    func.instr(InstrData::StoreField(instr::StoreField {
        dst_ref: head,
        src_val: temp_ref,
        field: next_field,
    }));
    func.instr(InstrData::StoreField(instr::StoreField {
        dst_ref: head,
        src_val: true_,
        field: has_next_field,
    }));
    func.instr(InstrData::Copy(instr::Copy {
        dst: head,
        src: temp_ref,
    }));

    func.instr(InstrData::IntAdd(instr::Binary {
        dst: i,
        src1: i,
        src2: one,
    }));
    func.instr(InstrData::IntCmp(instr::Cmp {
        dst: condition,
        src1: i,
        src2: n,
        mode: instr::CompareMode::Less,
    }));
    func.instr(InstrData::Branch(instr::Branch {
        condition,
        target: loop_start,
    }));

    func.instr(InstrData::IntAdd(instr::Binary {
        dst: j,
        src1: j,
        src2: one,
    }));
    func.instr(InstrData::IntCmp(instr::Cmp {
        dst: condition,
        src1: j,
        src2: k,
        mode: instr::CompareMode::Less,
    }));
    let jump_to_continue = func.instr(InstrData::Branch(instr::Branch {
        condition,
        target: Instr::reserved_value(), // initialized later
    }));
    let jump_to_end = func.instr(InstrData::Jump(instr::Jump {
        target: Instr::reserved_value(), // initialized later
    }));

    let continue_start = func.instr(InstrData::BoolConstant(instr::ConstantInstr {
        dst: has_head,
        constant: module.constant(ConstantData::Bool(false)),
    }));
    func.instr(InstrData::IntConstant(instr::ConstantInstr {
        dst: i,
        constant: module.constant(ConstantData::Int(0)),
    }));
    func.instr(InstrData::Jump(instr::Jump { target: loop_start }));

    func.instrs[jump_to_continue].set_branch_target(continue_start);

    // return value in last node
    let end = func.instr(InstrData::LoadField(instr::LoadField {
        dst: n,
        src_ref: head,
        field: val_field,
    }));
    func.instr(InstrData::Return(instr::Return { return_value: n }));

    func.instrs[jump_to_end].set_branch_target(end);

    module.funcs.push(func);

    let instance = Instance::new_test(module.clone(), 1024 * 34);
    assert_eq!(instance.interp_bare(Func::new(0)).unwrap(), Value::Int(999));

    let instance2 = Instance::new_test(module, 1024 * 32);
    assert!(matches!(
        instance2.interp_bare(Func::new(0)),
        Err(Error::OutOfMemory)
    ));
}

#[test]
fn fibonacci() {
    tracing_subscriber::fmt::try_init().ok();

    let mut module = ModuleData::default();
    let int = module.typ(bytecode::TypeData::Primitive(bytecode::PrimitiveType::Int));
    let bool_ = module.typ(bytecode::TypeData::Primitive(bytecode::PrimitiveType::Bool));
    let unit = module.typ(bytecode::TypeData::Primitive(bytecode::PrimitiveType::Unit));
    let unit_ref_type = module.typ(bytecode::TypeData::Reference(unit));
    let func = module.typ(bytecode::TypeData::Func(FuncTypeData {
        param_types: vec![int],
        return_type: int,
    }));

    let mut recursive_func = FuncData::new_no_captures(&mut module);

    let n = recursive_func.val(int);
    let temp_int1 = recursive_func.val(int);
    let temp_int2 = recursive_func.val(int);
    let condition = recursive_func.val(bool_);
    let zero = recursive_func.val(int);
    let one = recursive_func.val(int);
    let two = recursive_func.val(int);
    let unit_val = recursive_func.val(unit);
    let unit_ref = recursive_func.val(unit_ref_type);
    let f = recursive_func.val(func);

    recursive_func.params.push(FuncParamData { bind_to_val: n });

    recursive_func.instr(InstrData::IntConstant(instr::ConstantInstr {
        dst: zero,
        constant: module.constant(ConstantData::Int(0)),
    }));
    recursive_func.instr(InstrData::IntConstant(instr::ConstantInstr {
        dst: one,
        constant: module.constant(ConstantData::Int(1)),
    }));
    recursive_func.instr(InstrData::IntConstant(instr::ConstantInstr {
        dst: two,
        constant: module.constant(ConstantData::Int(2)),
    }));
    recursive_func.instr(InstrData::Alloc(instr::Alloc {
        dst_ref: unit_ref,
        src: unit_val,
    }));

    recursive_func.instr(InstrData::IntCmp(instr::Cmp {
        dst: condition,
        src1: n,
        src2: one,
        mode: instr::CompareMode::Equal,
    }));
    let branch_n1 = recursive_func.instr(InstrData::Branch(instr::Branch {
        target: Instr::reserved_value(), // initialized later
        condition,
    }));
    recursive_func.instr(InstrData::IntCmp(instr::Cmp {
        dst: condition,
        src1: n,
        src2: one,
        mode: instr::CompareMode::Less,
    }));
    let branch_n0 = recursive_func.instr(InstrData::Branch(instr::Branch {
        target: Instr::reserved_value(), // initialized later
        condition,
    }));

    recursive_func.instr(InstrData::MakeFunctionObject(instr::MakeFunctionObject {
        dst: f,
        func: module.funcs.next_key(),
        captures_ref: unit_ref,
    }));

    // f(n - 1)
    recursive_func.instr(InstrData::IntSub(instr::Binary {
        dst: temp_int1,
        src1: n,
        src2: one,
    }));
    let args = EntityList::from_slice(&[temp_int1], &mut recursive_func.val_lists);
    recursive_func.instr(InstrData::Call(instr::Call {
        func: f,
        args,
        return_value_dst: temp_int1,
    }));

    // f(n - 2)
    recursive_func.instr(InstrData::IntSub(instr::Binary {
        dst: temp_int2,
        src1: n,
        src2: two,
    }));
    let args = EntityList::from_slice(&[temp_int2], &mut recursive_func.val_lists);
    recursive_func.instr(InstrData::Call(instr::Call {
        func: f,
        args,
        return_value_dst: temp_int2,
    }));

    recursive_func.instr(InstrData::IntAdd(instr::Binary {
        dst: temp_int1,
        src1: temp_int1,
        src2: temp_int2,
    }));
    recursive_func.instr(InstrData::Return(instr::Return {
        return_value: temp_int1,
    }));

    // n == 1 case
    let n1_case = recursive_func.instr(InstrData::Return(instr::Return { return_value: one }));
    recursive_func.instrs[branch_n1].set_branch_target(n1_case);

    // n < 1 case
    let n0_case = recursive_func.instr(InstrData::Return(instr::Return { return_value: zero }));
    recursive_func.instrs[branch_n0].set_branch_target(n0_case);

    let recursive_func = module.funcs.push(recursive_func);

    let mut driver_func = FuncData::new_no_captures(&mut module);
    let f = driver_func.val(func);
    let n = driver_func.val(int);
    let unit_val = driver_func.val(unit);
    let unit_ref = driver_func.val(unit_ref_type);

    driver_func.instr(InstrData::IntConstant(instr::ConstantInstr {
        dst: n,
        constant: module.constant(ConstantData::Int(20)),
    }));
    driver_func.instr(InstrData::Alloc(instr::Alloc {
        dst_ref: unit_ref,
        src: unit_val,
    }));

    driver_func.instr(InstrData::MakeFunctionObject(instr::MakeFunctionObject {
        dst: f,
        func: recursive_func,
        captures_ref: unit_ref,
    }));
    let args = EntityList::from_slice(&[n], &mut driver_func.val_lists);
    driver_func.instr(InstrData::Call(instr::Call {
        func: f,
        args,
        return_value_dst: n,
    }));
    driver_func.instr(InstrData::Return(instr::Return { return_value: n }));
    module.funcs.push(driver_func);

    let instance = Instance::new_test(module, 1024);
    assert_eq!(
        instance.interp_bare(Func::new(1)).unwrap(),
        Value::Int(6765)
    );
}
