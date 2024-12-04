use bytecode::{
    instr,
    module::{ConstantData, FieldData, FuncData, LocalData, StructTypeData},
    Instr, InstrData, LocalType, ModuleData,
};
use cranelift_entity::{packed_option::ReservedValue, EntityList, EntityRef, PrimaryMap};
use zyon_runtime::{Func, Instance};

extern crate zyon_bytecode as bytecode;

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

    let mut func = FuncData::new(&mut module);

    let x = func.locals.push(LocalData::new(int));
    let i = func.locals.push(LocalData::new(int));
    let n = func.locals.push(LocalData::new(int));
    let one = func.locals.push(LocalData::new(int));
    let condition = func.locals.push(LocalData::new(bool_));

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

    let loop_start = func.instr(InstrData::IntMul(instr::BinaryInstr {
        dst: x,
        src1: x,
        src2: i,
    }));
    func.instr(InstrData::IntAdd(instr::BinaryInstr {
        dst: i,
        src1: i,
        src2: one,
    }));
    func.instr(InstrData::IntCmp(instr::CmpInstr {
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
    assert_eq!(instance.interp(Func::new(0)), 3628800); // 10!
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
    let node_ref_type = LocalType::new(node_type.index() + 1);

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

    let mut func = FuncData::new(&mut module);

    let head = func.local(node_ref_type);
    let has_head = func.local(bool_);
    let node = func.local(node_type);
    let temp_ref = func.local(node_ref_type);
    let uninit_ref = func.local(node_ref_type);
    let i = func.local(int);
    let j = func.local(int);
    let n = func.local(int);
    let k = func.local(int);
    let one = func.local(int);
    let condition = func.local(bool_);
    let false_ = func.local(bool_);
    let true_ = func.local(bool_);

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
        &mut func.local_pool,
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
    func.instr(InstrData::IntAdd(instr::BinaryInstr {
        dst: i,
        src1: i,
        src2: one,
    }));
    func.instr(InstrData::Jump(instr::Jump { target: loop_start }));

    // has_head case - append
    let fields =
        EntityList::from_slice(&[head, true_, uninit_ref, false_, i], &mut func.local_pool);
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

    func.instr(InstrData::IntAdd(instr::BinaryInstr {
        dst: i,
        src1: i,
        src2: one,
    }));
    func.instr(InstrData::IntCmp(instr::CmpInstr {
        dst: condition,
        src1: i,
        src2: n,
        mode: instr::CompareMode::Less,
    }));
    func.instr(InstrData::Branch(instr::Branch {
        condition,
        target: loop_start,
    }));

    func.instr(InstrData::IntAdd(instr::BinaryInstr {
        dst: j,
        src1: j,
        src2: one,
    }));
    func.instr(InstrData::IntCmp(instr::CmpInstr {
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

    let instance = Instance::new_test(module, 1024 * 34);
    assert_eq!(instance.interp(Func::new(0)), 999);
}

#[test]
fn fibonacci() {}
