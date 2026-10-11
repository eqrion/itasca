//! Function-body validation for both supported profiles.
//!
//! One body worker owns initialization and iteration over the shared operand and
//! control stacks. Wasm 1.0 and multi-value select their control rules; scalar
//! readers and operator callbacks are shared.

use crate::error::{OpError, VisitError};
use crate::limits::{
    MAX_FUNCTION_BYTES, MAX_MULTI_VALUE_PARAMS, MAX_MULTI_VALUE_RESULTS, MAX_RESULTS,
};
use crate::module::Env;
use crate::reader::{
    read_byte, read_f32_bits, read_f64_bits, read_s32_leb, read_s64_leb, read_u32_leb,
};
use crate::signature::{self, BlockType as BlockSignature, ResultType, TypePart};
use crate::types::{FuncType, GlobalType, Mut, ValueType};
use alloc::vec::Vec;

/// The Wasm 1.0 block immediate: zero or one result type.
#[cfg_attr(not(charon), derive(Debug))]
#[derive(Clone, Copy)]
pub(crate) enum BlockType {
    Empty,
    Value(ValueType),
}

impl PartialEq for BlockType {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (BlockType::Empty, BlockType::Empty) => true,
            (BlockType::Value(a), BlockType::Value(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for BlockType {}

/// The alignment exponent and byte offset of a memory instruction.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct MemArg {
    pub align: u32,
    pub offset: u32,
}

/// The parameters, declared locals, and result types of the current function.
///
/// The validator constructs this context from the module declarations before
/// calling `OpVisitor::on_function_start`.
pub struct Context {
    pub locals: Vec<ValueType>,
    /// The declared function results required by `return`.
    pub results: Vec<ValueType>,
}

type Result<T> = core::result::Result<T, OpError>;

/// Converts a callback result into an operator validation result.
pub(crate) fn visit(r: core::result::Result<(), VisitError>) -> Result<()> {
    match r {
        Ok(()) => Ok(()),
        Err(e) => Err(OpError::Visitor(e)),
    }
}

/// An operand type, including the unknown type used in unreachable code.
///
/// `Bot` is internal to stack typing and cannot occur in a function signature.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum StackType {
    Val(ValueType),
    Bot,
}

/// The construct represented by a control frame.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum LabelKind {
    Body,
    Block,
    Loop,
    Then,
    Else,
}

/// A control frame for the function body or a nested control instruction.
#[cfg_attr(not(charon), derive(Debug))]
#[derive(Clone, Copy)]
pub struct Ctrl {
    pub kind: LabelKind,
    pub(crate) block_type: BlockType,
    /// The complete parameter and result signature of this frame.
    pub signature: crate::signature::BlockType,
    /// The operand stack height below this frame.
    pub value_stack_base: usize,
    /// Whether the remaining instructions in this frame are unreachable.
    pub polymorphic_base: bool,
}

/// The operand stack, control stack, and body-relative cursor after an operator.
///
/// Visitors receive a shared reference and cannot change validation state.
pub struct OpIterState {
    pub vals: Vec<StackType>,
    pub ctrls: Vec<Ctrl>,
    pub pos: usize,
}

/// The shared body worker state used by both validation profiles.
struct BodyState {
    core: OpIterState,
}

// --- Opcodes (Wasm 1.0, all single-byte; prefixed opcodes are post-1.0) ---

pub const OP_UNREACHABLE: u8 = 0x00;
pub const OP_NOP: u8 = 0x01;
pub const OP_BLOCK: u8 = 0x02;
pub const OP_LOOP: u8 = 0x03;
pub const OP_IF: u8 = 0x04;
pub const OP_ELSE: u8 = 0x05;
pub const OP_END: u8 = 0x0b;
pub const OP_BR: u8 = 0x0c;
pub const OP_BR_IF: u8 = 0x0d;
pub const OP_BR_TABLE: u8 = 0x0e;
pub const OP_RETURN: u8 = 0x0f;
pub const OP_CALL: u8 = 0x10;
pub const OP_CALL_INDIRECT: u8 = 0x11;
pub const OP_DROP: u8 = 0x1a;
pub const OP_SELECT: u8 = 0x1b;

pub const OP_LOCAL_GET: u8 = 0x20;
pub const OP_LOCAL_SET: u8 = 0x21;
pub const OP_LOCAL_TEE: u8 = 0x22;
pub const OP_GLOBAL_GET: u8 = 0x23;
pub const OP_GLOBAL_SET: u8 = 0x24;

pub const OP_I32_LOAD: u8 = 0x28;
pub const OP_I64_LOAD: u8 = 0x29;
pub const OP_F32_LOAD: u8 = 0x2a;
pub const OP_F64_LOAD: u8 = 0x2b;
pub const OP_I32_LOAD8_S: u8 = 0x2c;
pub const OP_I32_LOAD8_U: u8 = 0x2d;
pub const OP_I32_LOAD16_S: u8 = 0x2e;
pub const OP_I32_LOAD16_U: u8 = 0x2f;
pub const OP_I64_LOAD8_S: u8 = 0x30;
pub const OP_I64_LOAD8_U: u8 = 0x31;
pub const OP_I64_LOAD16_S: u8 = 0x32;
pub const OP_I64_LOAD16_U: u8 = 0x33;
pub const OP_I64_LOAD32_S: u8 = 0x34;
pub const OP_I64_LOAD32_U: u8 = 0x35;

pub const OP_I32_STORE: u8 = 0x36;
pub const OP_I64_STORE: u8 = 0x37;
pub const OP_F32_STORE: u8 = 0x38;
pub const OP_F64_STORE: u8 = 0x39;
pub const OP_I32_STORE8: u8 = 0x3a;
pub const OP_I32_STORE16: u8 = 0x3b;
pub const OP_I64_STORE8: u8 = 0x3c;
pub const OP_I64_STORE16: u8 = 0x3d;
pub const OP_I64_STORE32: u8 = 0x3e;

pub const OP_MEMORY_SIZE: u8 = 0x3f;
pub const OP_MEMORY_GROW: u8 = 0x40;

pub const OP_I32_CONST: u8 = 0x41;
pub const OP_I64_CONST: u8 = 0x42;
pub const OP_F32_CONST: u8 = 0x43;
pub const OP_F64_CONST: u8 = 0x44;

pub const OP_I32_EQZ: u8 = 0x45;
pub const OP_I32_EQ: u8 = 0x46;
pub const OP_I32_NE: u8 = 0x47;
pub const OP_I32_LT_S: u8 = 0x48;
pub const OP_I32_LT_U: u8 = 0x49;
pub const OP_I32_GT_S: u8 = 0x4a;
pub const OP_I32_GT_U: u8 = 0x4b;
pub const OP_I32_LE_S: u8 = 0x4c;
pub const OP_I32_LE_U: u8 = 0x4d;
pub const OP_I32_GE_S: u8 = 0x4e;
pub const OP_I32_GE_U: u8 = 0x4f;

pub const OP_I64_EQZ: u8 = 0x50;
pub const OP_I64_EQ: u8 = 0x51;
pub const OP_I64_NE: u8 = 0x52;
pub const OP_I64_LT_S: u8 = 0x53;
pub const OP_I64_LT_U: u8 = 0x54;
pub const OP_I64_GT_S: u8 = 0x55;
pub const OP_I64_GT_U: u8 = 0x56;
pub const OP_I64_LE_S: u8 = 0x57;
pub const OP_I64_LE_U: u8 = 0x58;
pub const OP_I64_GE_S: u8 = 0x59;
pub const OP_I64_GE_U: u8 = 0x5a;

pub const OP_F32_EQ: u8 = 0x5b;
pub const OP_F32_NE: u8 = 0x5c;
pub const OP_F32_LT: u8 = 0x5d;
pub const OP_F32_GT: u8 = 0x5e;
pub const OP_F32_LE: u8 = 0x5f;
pub const OP_F32_GE: u8 = 0x60;

pub const OP_F64_EQ: u8 = 0x61;
pub const OP_F64_NE: u8 = 0x62;
pub const OP_F64_LT: u8 = 0x63;
pub const OP_F64_GT: u8 = 0x64;
pub const OP_F64_LE: u8 = 0x65;
pub const OP_F64_GE: u8 = 0x66;

pub const OP_I32_SUB: u8 = 0x6b;
pub const OP_I32_MUL: u8 = 0x6c;
pub const OP_I32_DIV_S: u8 = 0x6d;
pub const OP_I32_DIV_U: u8 = 0x6e;
pub const OP_I32_REM_S: u8 = 0x6f;
pub const OP_I32_REM_U: u8 = 0x70;
pub const OP_I32_AND: u8 = 0x71;
pub const OP_I32_OR: u8 = 0x72;
pub const OP_I32_XOR: u8 = 0x73;
pub const OP_I32_SHL: u8 = 0x74;
pub const OP_I32_SHR_S: u8 = 0x75;
pub const OP_I32_SHR_U: u8 = 0x76;
pub const OP_I32_ROTL: u8 = 0x77;
pub const OP_I32_ROTR: u8 = 0x78;

pub const OP_I64_ADD: u8 = 0x7c;
pub const OP_I64_SUB: u8 = 0x7d;
pub const OP_I64_MUL: u8 = 0x7e;
pub const OP_I64_DIV_S: u8 = 0x7f;
pub const OP_I64_DIV_U: u8 = 0x80;
pub const OP_I64_REM_S: u8 = 0x81;
pub const OP_I64_REM_U: u8 = 0x82;
pub const OP_I64_AND: u8 = 0x83;
pub const OP_I64_OR: u8 = 0x84;
pub const OP_I64_XOR: u8 = 0x85;
pub const OP_I64_SHL: u8 = 0x86;
pub const OP_I64_SHR_S: u8 = 0x87;
pub const OP_I64_SHR_U: u8 = 0x88;
pub const OP_I64_ROTL: u8 = 0x89;
pub const OP_I64_ROTR: u8 = 0x8a;

pub const OP_F32_ADD: u8 = 0x92;
pub const OP_F32_SUB: u8 = 0x93;
pub const OP_F32_MUL: u8 = 0x94;
pub const OP_F32_DIV: u8 = 0x95;
pub const OP_F32_MIN: u8 = 0x96;
pub const OP_F32_MAX: u8 = 0x97;
pub const OP_F32_COPYSIGN: u8 = 0x98;

pub const OP_F64_ADD: u8 = 0xa0;
pub const OP_F64_SUB: u8 = 0xa1;
pub const OP_F64_MUL: u8 = 0xa2;
pub const OP_F64_DIV: u8 = 0xa3;
pub const OP_F64_MIN: u8 = 0xa4;
pub const OP_F64_MAX: u8 = 0xa5;
pub const OP_F64_COPYSIGN: u8 = 0xa6;

pub const OP_I32_CLZ: u8 = 0x67;
pub const OP_I32_CTZ: u8 = 0x68;
pub const OP_I32_POPCNT: u8 = 0x69;
pub const OP_I32_ADD: u8 = 0x6a;

pub const OP_I64_CLZ: u8 = 0x79;
pub const OP_I64_CTZ: u8 = 0x7a;
pub const OP_I64_POPCNT: u8 = 0x7b;

pub const OP_F32_ABS: u8 = 0x8b;
pub const OP_F32_NEG: u8 = 0x8c;
pub const OP_F32_CEIL: u8 = 0x8d;
pub const OP_F32_FLOOR: u8 = 0x8e;
pub const OP_F32_TRUNC: u8 = 0x8f;
pub const OP_F32_NEAREST: u8 = 0x90;
pub const OP_F32_SQRT: u8 = 0x91;

pub const OP_F64_ABS: u8 = 0x99;
pub const OP_F64_NEG: u8 = 0x9a;
pub const OP_F64_CEIL: u8 = 0x9b;
pub const OP_F64_FLOOR: u8 = 0x9c;
pub const OP_F64_TRUNC: u8 = 0x9d;
pub const OP_F64_NEAREST: u8 = 0x9e;
pub const OP_F64_SQRT: u8 = 0x9f;

pub const OP_I32_WRAP_I64: u8 = 0xa7;
pub const OP_I32_TRUNC_F32_S: u8 = 0xa8;
pub const OP_I32_TRUNC_F32_U: u8 = 0xa9;
pub const OP_I32_TRUNC_F64_S: u8 = 0xaa;
pub const OP_I32_TRUNC_F64_U: u8 = 0xab;
pub const OP_I64_EXTEND_I32_S: u8 = 0xac;
pub const OP_I64_EXTEND_I32_U: u8 = 0xad;
pub const OP_I64_TRUNC_F32_S: u8 = 0xae;
pub const OP_I64_TRUNC_F32_U: u8 = 0xaf;
pub const OP_I64_TRUNC_F64_S: u8 = 0xb0;
pub const OP_I64_TRUNC_F64_U: u8 = 0xb1;
pub const OP_F32_CONVERT_I32_S: u8 = 0xb2;
pub const OP_F32_CONVERT_I32_U: u8 = 0xb3;
pub const OP_F32_CONVERT_I64_S: u8 = 0xb4;
pub const OP_F32_CONVERT_I64_U: u8 = 0xb5;
pub const OP_F32_DEMOTE_F64: u8 = 0xb6;
pub const OP_F64_CONVERT_I32_S: u8 = 0xb7;
pub const OP_F64_CONVERT_I32_U: u8 = 0xb8;
pub const OP_F64_CONVERT_I64_S: u8 = 0xb9;
pub const OP_F64_CONVERT_I64_U: u8 = 0xba;
pub const OP_F64_PROMOTE_F32: u8 = 0xbb;
pub const OP_I32_REINTERPRET_F32: u8 = 0xbc;
pub const OP_I64_REINTERPRET_F64: u8 = 0xbd;
pub const OP_F32_REINTERPRET_I32: u8 = 0xbe;
pub const OP_F64_REINTERPRET_I64: u8 = 0xbf;

fn read_block_type(data: &[u8], pos: usize) -> Result<(BlockType, usize)> {
    let (b, p) = read_byte(data, pos)?;
    match b {
        0x40 => Ok((BlockType::Empty, p)),
        0x7f => Ok((BlockType::Value(ValueType::I32), p)),
        0x7e => Ok((BlockType::Value(ValueType::I64), p)),
        0x7d => Ok((BlockType::Value(ValueType::F32), p)),
        0x7c => Ok((BlockType::Value(ValueType::F64), p)),
        _ => Err(OpError::InvalidBlockType),
    }
}

// --- Operand and control stack ---

pub(crate) fn cur_base(st: &OpIterState) -> usize {
    let n = st.ctrls.len();
    if n == 0 {
        return 0;
    }
    st.ctrls[n - 1].value_stack_base
}

pub(crate) fn cur_polymorphic(st: &OpIterState) -> bool {
    let n = st.ctrls.len();
    if n == 0 {
        return false;
    }
    st.ctrls[n - 1].polymorphic_base
}

fn push_val(st: &mut OpIterState, t: StackType) {
    st.vals.push(t);
}

/// Pops one operand, returning `Bot` at an exhausted unreachable frame.
fn pop_stack_type(st: &mut OpIterState) -> Result<StackType> {
    if st.vals.len() == cur_base(st) {
        if cur_polymorphic(st) {
            return Ok(StackType::Bot);
        }
        return Err(OpError::EmptyStack);
    }
    match st.vals.pop() {
        Some(t) => Ok(t),
        None => Err(OpError::EmptyStack),
    }
}

/// Pops one operand and checks it against `expected`, allowing `Bot` to match any
/// type.
pub(crate) fn pop_with_type(st: &mut OpIterState, expected: ValueType) -> Result<StackType> {
    let t = pop_stack_type(st)?;
    match t {
        StackType::Bot => Ok(t),
        StackType::Val(v) => {
            if v == expected {
                Ok(t)
            } else {
                Err(OpError::TypeMismatch)
            }
        }
    }
}

/// Pops the expected types in reverse stack order.
pub(crate) fn pop_types(st: &mut OpIterState, types: &[ValueType]) -> Result<()> {
    let mut i: usize = types.len();
    loop {
        if i == 0 {
            return Ok(());
        }
        i -= 1;
        pop_with_type(st, types[i])?;
    }
}

pub(crate) fn push_types(st: &mut OpIterState, types: &[ValueType]) {
    let mut i: usize = 0;
    loop {
        if i >= types.len() {
            return;
        }
        push_val(st, StackType::Val(types[i]));
        i += 1;
    }
}

/// Converts a Wasm 1.0 block immediate into a visitor signature.
fn visitor_block_type(bt: BlockType) -> crate::signature::BlockType {
    match bt {
        BlockType::Empty => crate::signature::BlockType::Empty,
        BlockType::Value(t) => crate::signature::BlockType::Value(t),
    }
}

fn visitor_result_type(bt: BlockType) -> crate::signature::ResultType {
    match bt {
        BlockType::Empty => crate::signature::ResultType::Empty,
        BlockType::Value(t) => crate::signature::ResultType::One(t),
    }
}

/// Returns the zero or one result types of a Wasm 1.0 block.
fn block_results(bt: &BlockType) -> Vec<ValueType> {
    match bt {
        BlockType::Empty => Vec::new(),
        BlockType::Value(vt) => {
            let mut v = Vec::new();
            v.push(*vt);
            v
        }
    }
}

/// Returns the target signature of a Wasm 1.0 frame.
///
/// Loop labels have no parameters; other labels use the frame's results. The
/// descriptor avoids allocating a vector for each branch-table target.
fn branch_target_bt(c: &Ctrl) -> BlockType {
    match c.kind {
        LabelKind::Loop => BlockType::Empty,
        _ => c.block_type,
    }
}

fn branch_target_types(c: &Ctrl) -> Vec<ValueType> {
    block_results(&branch_target_bt(c))
}

pub(crate) fn push_ctrl(st: &mut OpIterState, kind: LabelKind, bt: BlockType) {
    let base = st.vals.len();
    st.ctrls.push(Ctrl {
        kind,
        block_type: bt,
        signature: visitor_block_type(bt),
        value_stack_base: base,
        polymorphic_base: false,
    });
}

/// Discards the current frame's operands and marks it unreachable.
pub(crate) fn mark_unreachable(st: &mut OpIterState) {
    let base = cur_base(st);
    loop {
        if st.vals.len() <= base {
            break;
        }
        let _ = st.vals.pop();
    }
    let n = st.ctrls.len();
    if n == 0 {
        return;
    }
    st.ctrls[n - 1].polymorphic_base = true;
}

// --- Driving one body ---

pub(crate) fn start_function(results: &[ValueType]) -> OpIterState {
    let mut st = OpIterState {
        vals: Vec::new(),
        ctrls: Vec::new(),
        pos: 0,
    };
    let mut bt = BlockType::Empty;
    if results.len() == 1 {
        bt = BlockType::Value(results[0]);
    }
    push_ctrl(&mut st, LabelKind::Body, bt);
    st
}

#[allow(dead_code)]
fn control_stack_empty(st: &OpIterState) -> bool {
    st.ctrls.is_empty()
}

/// Reads the next opcode and advances the body cursor.
#[allow(dead_code)]
fn read_op(st: &mut OpIterState, data: &[u8]) -> Result<u8> {
    let (b, p) = read_byte(data, st.pos)?;
    st.pos = p;
    Ok(b)
}

// --- Readers ---

fn read_unreachable(st: &mut OpIterState) -> Result<()> {
    mark_unreachable(st);
    Ok(())
}

fn read_i32_const(st: &mut OpIterState, data: &[u8]) -> Result<i32> {
    let (v, p) = read_s32_leb(data, st.pos)?;
    st.pos = p;
    push_val(st, StackType::Val(ValueType::I32));
    Ok(v)
}

fn read_i64_const(st: &mut OpIterState, data: &[u8]) -> Result<i64> {
    let (v, p) = read_s64_leb(data, st.pos)?;
    st.pos = p;
    push_val(st, StackType::Val(ValueType::I64));
    Ok(v)
}

/// Reads an `f32.const` immediate, pushes its type, and returns its raw bits.
fn read_f32_const(st: &mut OpIterState, data: &[u8]) -> Result<u32> {
    let (v, p) = read_f32_bits(data, st.pos)?;
    st.pos = p;
    push_val(st, StackType::Val(ValueType::F32));
    Ok(v)
}

/// Reads an `f64.const` immediate, pushes its type, and returns its raw bits.
fn read_f64_const(st: &mut OpIterState, data: &[u8]) -> Result<u64> {
    let (v, p) = read_f64_bits(data, st.pos)?;
    st.pos = p;
    push_val(st, StackType::Val(ValueType::F64));
    Ok(v)
}

/// Applies the stack effect `[ty ty] -> [result]` of a binary operator or
/// comparison.
fn read_binary(st: &mut OpIterState, ty: ValueType, result: ValueType) -> Result<()> {
    pop_with_type(st, ty)?;
    pop_with_type(st, ty)?;
    push_val(st, StackType::Val(result));
    Ok(())
}

/// Applies the stack effect `[from] -> [to]` of a unary operator or conversion.
fn read_conversion(st: &mut OpIterState, from: ValueType, to: ValueType) -> Result<()> {
    pop_with_type(st, from)?;
    push_val(st, StackType::Val(to));
    Ok(())
}

fn read_drop(st: &mut OpIterState) -> Result<StackType> {
    pop_stack_type(st)
}

/// Returns the common operand type, resolving `Bot` to the other type.
fn join_stack_type(a: StackType, b: StackType) -> Result<StackType> {
    match a {
        StackType::Bot => Ok(b),
        StackType::Val(va) => match b {
            StackType::Bot => Ok(a),
            StackType::Val(vb) => {
                if va == vb {
                    Ok(a)
                } else {
                    Err(OpError::TypeMismatch)
                }
            }
        },
    }
}

/// Applies untyped `select`, requiring compatible value operands and an `i32`
/// condition.
///
/// The selected type remains `Bot` when both values come from an exhausted
/// unreachable frame.
fn read_select(st: &mut OpIterState) -> Result<StackType> {
    pop_with_type(st, ValueType::I32)?;
    // Named t2/t3 because the condition that just came off is conventionally
    // t1: these are the two operands below it.
    let t2 = pop_stack_type(st)?;
    let t3 = pop_stack_type(st)?;
    let t = join_stack_type(t2, t3)?;
    push_val(st, t);
    Ok(t)
}

/// Returns the declared type of a local, checking its index.
fn local_type(ctx: &Context, idx: u32) -> Result<ValueType> {
    let i = idx as usize;
    if i >= ctx.locals.len() {
        return Err(OpError::UnknownLocal);
    }
    Ok(ctx.locals[i])
}

/// Reads a local index and resolves its declared type.
fn take_local(st: &mut OpIterState, data: &[u8], ctx: &Context) -> Result<(u32, ValueType)> {
    let (idx, p) = read_u32_leb(data, st.pos)?;
    st.pos = p;
    let t = local_type(ctx, idx)?;
    Ok((idx, t))
}

/// Validates `local.get` and returns its local index.
fn read_local_get(st: &mut OpIterState, data: &[u8], ctx: &Context) -> Result<u32> {
    let (idx, t) = take_local(st, data, ctx)?;
    push_val(st, StackType::Val(t));
    Ok(idx)
}

/// Validates `local.set` and returns its local index.
fn read_local_set(st: &mut OpIterState, data: &[u8], ctx: &Context) -> Result<u32> {
    let (idx, t) = take_local(st, data, ctx)?;
    pop_with_type(st, t)?;
    Ok(idx)
}

/// Validates `local.tee` and returns its local index.
fn read_local_tee(st: &mut OpIterState, data: &[u8], ctx: &Context) -> Result<u32> {
    let (idx, t) = take_local(st, data, ctx)?;
    pop_with_type(st, t)?;
    push_val(st, StackType::Val(t));
    Ok(idx)
}

/// Returns the declared type and mutability of a global, checking its index.
fn global_type(env: &Env, idx: u32) -> Result<GlobalType> {
    let i = idx as usize;
    if i >= env.global_types.len() {
        return Err(OpError::UnknownGlobal);
    }
    Ok(env.global_types[i])
}

/// Reads a global index and resolves its type and mutability.
fn take_global(st: &mut OpIterState, data: &[u8], env: &Env) -> Result<(u32, GlobalType)> {
    let (idx, p) = read_u32_leb(data, st.pos)?;
    st.pos = p;
    let g = global_type(env, idx)?;
    Ok((idx, g))
}

/// Validates `global.get` and returns its global index.
fn read_global_get(st: &mut OpIterState, data: &[u8], env: &Env) -> Result<u32> {
    let (idx, g) = take_global(st, data, env)?;
    push_val(st, StackType::Val(g.valtype));
    Ok(idx)
}

/// Validates `global.set`, requiring a mutable global, and returns its index.
fn read_global_set(st: &mut OpIterState, data: &[u8], env: &Env) -> Result<u32> {
    let (idx, g) = take_global(st, data, env)?;
    match g.mutability {
        Mut::Const => return Err(OpError::ImmutableGlobal),
        Mut::Var => {}
    }
    pop_with_type(st, g.valtype)?;
    Ok(idx)
}

/// Reads a reserved zero byte for a memory or indirect-call instruction.
fn read_reserved_zero(st: &mut OpIterState, data: &[u8]) -> Result<()> {
    let (b, p) = read_byte(data, st.pos)?;
    if b != 0 {
        return Err(OpError::ReservedByteNotZero);
    }
    st.pos = p;
    Ok(())
}

/// Validates `memory.size` and pushes an `i32` result.
fn read_memory_size(st: &mut OpIterState, data: &[u8], env: &Env) -> Result<()> {
    read_reserved_zero(st, data)?;
    require_memory(env)?;
    push_val(st, StackType::Val(ValueType::I32));
    Ok(())
}

/// Validates `memory.grow`, consuming and returning an `i32`.
fn read_memory_grow(st: &mut OpIterState, data: &[u8], env: &Env) -> Result<()> {
    read_reserved_zero(st, data)?;
    require_memory(env)?;
    pop_with_type(st, ValueType::I32)?;
    push_val(st, StackType::Val(ValueType::I32));
    Ok(())
}

fn read_block(st: &mut OpIterState, data: &[u8]) -> Result<BlockType> {
    let (bt, p) = read_block_type(data, st.pos)?;
    st.pos = p;
    push_ctrl(st, LabelKind::Block, bt);
    Ok(bt)
}

fn read_loop(st: &mut OpIterState, data: &[u8]) -> Result<BlockType> {
    let (bt, p) = read_block_type(data, st.pos)?;
    st.pos = p;
    push_ctrl(st, LabelKind::Loop, bt);
    Ok(bt)
}

/// Returns whether the frame represents an open then arm.
fn is_then(kind: LabelKind) -> bool {
    match kind {
        LabelKind::Then => true,
        LabelKind::Body => false,
        LabelKind::Block => false,
        LabelKind::Loop => false,
        LabelKind::Else => false,
    }
}

/// Validates a Wasm 1.0 `if` and opens its then frame.
fn read_if(st: &mut OpIterState, data: &[u8]) -> Result<BlockType> {
    let (bt, p) = read_block_type(data, st.pos)?;
    st.pos = p;
    pop_with_type(st, ValueType::I32)?;
    push_ctrl(st, LabelKind::Then, bt);
    Ok(bt)
}

/// Checks the then arm's results and resets its frame for the else arm.
fn read_else(st: &mut OpIterState) -> Result<BlockType> {
    let n = st.ctrls.len();
    if n == 0 {
        return Err(OpError::StackMismatch);
    }
    let frame = st.ctrls[n - 1];
    if !is_then(frame.kind) {
        return Err(OpError::StackMismatch);
    }
    let results = block_results(&frame.block_type);
    pop_types(st, &results)?;
    if st.vals.len() != frame.value_stack_base {
        return Err(OpError::StackMismatch);
    }
    st.ctrls[n - 1].kind = LabelKind::Else;
    st.ctrls[n - 1].polymorphic_base = false;
    Ok(frame.block_type)
}

/// Checks and closes the current frame, leaving its results on the enclosing
/// stack.
///
/// A Wasm 1.0 then arm without an else must have no results.
fn read_end(st: &mut OpIterState) -> Result<(LabelKind, BlockType)> {
    let n = st.ctrls.len();
    if n == 0 {
        return Err(OpError::StackMismatch);
    }
    let frame = st.ctrls[n - 1];
    let results = block_results(&frame.block_type);
    if is_then(frame.kind) && !results.is_empty() {
        return Err(OpError::StackMismatch);
    }
    pop_types(st, &results)?;
    if st.vals.len() != frame.value_stack_base {
        return Err(OpError::StackMismatch);
    }
    let _ = st.ctrls.pop();
    push_types(st, &results);
    Ok((frame.kind, frame.block_type))
}

/// Reads a label depth and resolves its frame, counting from the innermost frame.
fn read_label(st: &mut OpIterState, data: &[u8]) -> Result<(u32, Ctrl)> {
    let (depth, p) = read_u32_leb(data, st.pos)?;
    st.pos = p;
    let n = st.ctrls.len();
    let d = depth as usize;
    if d >= n {
        return Err(OpError::UnknownLabel);
    }
    Ok((depth, st.ctrls[n - 1 - d]))
}

/// Validates an unconditional branch and marks the remaining code unreachable.
fn read_br(st: &mut OpIterState, data: &[u8]) -> Result<(u32, BlockType)> {
    let (depth, target) = read_label(st, data)?;
    let types = branch_target_types(&target);
    pop_types(st, &types)?;
    mark_unreachable(st);
    Ok((depth, branch_target_bt(&target)))
}

/// Checks the function results and marks the remaining code unreachable.
fn read_return(st: &mut OpIterState, ctx: &Context) -> Result<()> {
    pop_types(st, &ctx.results)?;
    mark_unreachable(st);
    Ok(())
}

/// Validates a conditional branch while retaining target operands for
/// fall-through.
fn read_br_if(st: &mut OpIterState, data: &[u8]) -> Result<(u32, BlockType)> {
    let (depth, target) = read_label(st, data)?;
    let types = branch_target_types(&target);
    pop_with_type(st, ValueType::I32)?;
    pop_types(st, &types)?;
    push_types(st, &types);
    Ok((depth, branch_target_bt(&target)))
}

/// Checks that a branch-table target agrees with the previously resolved
/// signature.
fn merge_target(expect: Option<BlockType>, bt: BlockType) -> Result<BlockType> {
    match expect {
        None => Ok(bt),
        Some(e) => {
            if bt == e {
                Ok(bt)
            } else {
                Err(OpError::TypeMismatch)
            }
        }
    }
}

/// Reads and checks the non-default branch-table targets in encoded order.
fn read_table_labels<V: OpVisitor>(
    st: &mut OpIterState,
    data: &[u8],
    count: u32,
    v: &mut V,
) -> Result<Option<BlockType>> {
    let mut expect: Option<BlockType> = None;
    let mut i: u32 = 0;
    loop {
        if i == count {
            return Ok(expect);
        }
        let (depth, target) = read_label(st, data)?;
        // The one hook inside a reader. The depths cannot be handed over in a
        // `Vec`, whose only bound would be the byte count, so they are handed
        // over one at a time as they are read.
        visit(v.on_br_table_label(st, depth))?;
        let bt = merge_target(expect, branch_target_bt(&target))?;
        expect = Some(bt);
        i += 1;
    }
}

/// Validates a Wasm 1.0 branch table with identical target signatures.
///
/// Targets are reported individually to the visitor instead of being collected in
/// a vector. The default target is reported by the closing callback.
fn read_br_table<V: OpVisitor>(
    st: &mut OpIterState,
    data: &[u8],
    v: &mut V,
) -> Result<(u32, BlockType)> {
    let (count, p) = read_u32_leb(data, st.pos)?;
    st.pos = p;
    let expect = read_table_labels(st, data, count, v)?;
    let (default, target) = read_label(st, data)?;
    let common = merge_target(expect, branch_target_bt(&target))?;
    pop_with_type(st, ValueType::I32)?;
    let types = block_results(&common);
    pop_types(st, &types)?;
    mark_unreachable(st);
    Ok((default, common))
}

/// Reads an index immediate and advances the body cursor.
fn take_index(st: &mut OpIterState, data: &[u8]) -> Result<u32> {
    let (idx, p) = read_u32_leb(data, st.pos)?;
    st.pos = p;
    Ok(idx)
}

/// Checks the Wasm 1.0 result limit before a call can grow the operand stack.
fn require_single_result(results: &[ValueType]) -> Result<()> {
    if results.len() > MAX_RESULTS {
        return Err(OpError::TooManyResults);
    }
    Ok(())
}

/// Validates a direct call using its cached parameter and result types.
fn read_call(st: &mut OpIterState, data: &[u8], env: &Env) -> Result<u32> {
    let idx = take_index(st, data)?;
    let i = idx as usize;
    if i >= env.func_types.len() {
        return Err(OpError::UnknownFunc);
    }
    require_single_result(&env.func_types[i].results)?;
    pop_types(st, &env.func_types[i].params)?;
    push_types(st, &env.func_types[i].results);
    Ok(idx)
}

/// Validates an indirect call using the selected type and the reserved table-zero
/// byte.
fn read_call_indirect(st: &mut OpIterState, data: &[u8], env: &Env) -> Result<u32> {
    let idx = take_index(st, data)?;
    read_reserved_zero(st, data)?;
    if env.table_types.is_empty() {
        return Err(OpError::UnknownTable);
    }
    let i = idx as usize;
    if i >= env.types.len() {
        return Err(OpError::UnknownType);
    }
    require_single_result(&env.types[i].results)?;
    pop_with_type(st, ValueType::I32)?;
    pop_types(st, &env.types[i].params)?;
    push_types(st, &env.types[i].results);
    Ok(idx)
}

/// Validates a load, requiring a memory, an `i32` address, and valid alignment.
fn read_load(
    st: &mut OpIterState,
    data: &[u8],
    env: &Env,
    ty: ValueType,
    natural_align: u32,
) -> Result<MemArg> {
    let memarg = read_memarg(st, data)?;
    check_memory_and_alignment(env, &memarg, natural_align)?;
    pop_with_type(st, ValueType::I32)?;
    push_val(st, StackType::Val(ty));
    Ok(memarg)
}

/// Validates a store, requiring a memory, typed operands, and valid alignment.
fn read_store(
    st: &mut OpIterState,
    data: &[u8],
    env: &Env,
    ty: ValueType,
    natural_align: u32,
) -> Result<MemArg> {
    let memarg = read_memarg(st, data)?;
    check_memory_and_alignment(env, &memarg, natural_align)?;
    pop_with_type(st, ty)?;
    pop_with_type(st, ValueType::I32)?;
    Ok(memarg)
}

fn read_memarg(st: &mut OpIterState, data: &[u8]) -> Result<MemArg> {
    let (align, p1) = read_u32_leb(data, st.pos)?;
    let (offset, p2) = read_u32_leb(data, p1)?;
    st.pos = p2;
    Ok(MemArg { align, offset })
}

/// Checks that the module declares or imports a memory.
fn require_memory(env: &Env) -> Result<()> {
    if env.mem_types.is_empty() {
        return Err(OpError::UnknownMemory);
    }
    Ok(())
}

/// Checks that a memory exists and the alignment does not exceed the natural
/// alignment.
fn check_memory_and_alignment(env: &Env, memarg: &MemArg, natural_align: u32) -> Result<()> {
    require_memory(env)?;
    if memarg.align > natural_align {
        return Err(OpError::InvalidAlignment);
    }
    Ok(())
}

// --- The numeric opcode table ---
//
// The operand types for each numeric opcode are kept as data, one row per
// opcode read straight off the specification's table, rather than spelled out
// in a dispatch switch. That keeps the correspondence proof one branch per
// *shape* rather than one per opcode.

/// Returns the input and output types of a supported unary or conversion opcode.
pub(crate) fn convert_types(opcode: u8) -> Option<(ValueType, ValueType)> {
    match opcode {
        OP_I32_EQZ | OP_I32_CLZ | OP_I32_CTZ | OP_I32_POPCNT => {
            Some((ValueType::I32, ValueType::I32))
        }
        OP_I64_CLZ | OP_I64_CTZ | OP_I64_POPCNT => Some((ValueType::I64, ValueType::I64)),
        OP_F32_ABS | OP_F32_NEG | OP_F32_CEIL | OP_F32_FLOOR | OP_F32_TRUNC | OP_F32_NEAREST
        | OP_F32_SQRT => Some((ValueType::F32, ValueType::F32)),
        OP_F64_ABS | OP_F64_NEG | OP_F64_CEIL | OP_F64_FLOOR | OP_F64_TRUNC | OP_F64_NEAREST
        | OP_F64_SQRT => Some((ValueType::F64, ValueType::F64)),
        OP_I64_EQZ | OP_I32_WRAP_I64 => Some((ValueType::I64, ValueType::I32)),
        OP_I32_TRUNC_F32_S | OP_I32_TRUNC_F32_U | OP_I32_REINTERPRET_F32 => {
            Some((ValueType::F32, ValueType::I32))
        }
        OP_I32_TRUNC_F64_S | OP_I32_TRUNC_F64_U => Some((ValueType::F64, ValueType::I32)),
        OP_I64_EXTEND_I32_S | OP_I64_EXTEND_I32_U => Some((ValueType::I32, ValueType::I64)),
        OP_I64_TRUNC_F32_S | OP_I64_TRUNC_F32_U => Some((ValueType::F32, ValueType::I64)),
        OP_I64_TRUNC_F64_S | OP_I64_TRUNC_F64_U | OP_I64_REINTERPRET_F64 => {
            Some((ValueType::F64, ValueType::I64))
        }
        OP_F32_CONVERT_I32_S | OP_F32_CONVERT_I32_U | OP_F32_REINTERPRET_I32 => {
            Some((ValueType::I32, ValueType::F32))
        }
        OP_F32_CONVERT_I64_S | OP_F32_CONVERT_I64_U => Some((ValueType::I64, ValueType::F32)),
        OP_F32_DEMOTE_F64 => Some((ValueType::F64, ValueType::F32)),
        OP_F64_CONVERT_I32_S | OP_F64_CONVERT_I32_U => Some((ValueType::I32, ValueType::F64)),
        OP_F64_CONVERT_I64_S | OP_F64_CONVERT_I64_U | OP_F64_REINTERPRET_I64 => {
            Some((ValueType::I64, ValueType::F64))
        }
        OP_F64_PROMOTE_F32 => Some((ValueType::F32, ValueType::F64)),
        _ => None,
    }
}

/// Returns the operand and result types of a supported binary or comparison
/// opcode.
pub(crate) fn binary_types(opcode: u8) -> Option<(ValueType, ValueType)> {
    match opcode {
        OP_I32_EQ | OP_I32_NE | OP_I32_LT_S | OP_I32_LT_U | OP_I32_GT_S | OP_I32_GT_U
        | OP_I32_LE_S | OP_I32_LE_U | OP_I32_GE_S | OP_I32_GE_U | OP_I32_ADD | OP_I32_SUB
        | OP_I32_MUL | OP_I32_DIV_S | OP_I32_DIV_U | OP_I32_REM_S | OP_I32_REM_U | OP_I32_AND
        | OP_I32_OR | OP_I32_XOR | OP_I32_SHL | OP_I32_SHR_S | OP_I32_SHR_U | OP_I32_ROTL
        | OP_I32_ROTR => Some((ValueType::I32, ValueType::I32)),
        OP_I64_EQ | OP_I64_NE | OP_I64_LT_S | OP_I64_LT_U | OP_I64_GT_S | OP_I64_GT_U
        | OP_I64_LE_S | OP_I64_LE_U | OP_I64_GE_S | OP_I64_GE_U => {
            Some((ValueType::I64, ValueType::I32))
        }
        OP_F32_EQ | OP_F32_NE | OP_F32_LT | OP_F32_GT | OP_F32_LE | OP_F32_GE => {
            Some((ValueType::F32, ValueType::I32))
        }
        OP_F64_EQ | OP_F64_NE | OP_F64_LT | OP_F64_GT | OP_F64_LE | OP_F64_GE => {
            Some((ValueType::F64, ValueType::I32))
        }
        OP_I64_ADD | OP_I64_SUB | OP_I64_MUL | OP_I64_DIV_S | OP_I64_DIV_U | OP_I64_REM_S
        | OP_I64_REM_U | OP_I64_AND | OP_I64_OR | OP_I64_XOR | OP_I64_SHL | OP_I64_SHR_S
        | OP_I64_SHR_U | OP_I64_ROTL | OP_I64_ROTR => Some((ValueType::I64, ValueType::I64)),
        OP_F32_ADD | OP_F32_SUB | OP_F32_MUL | OP_F32_DIV | OP_F32_MIN | OP_F32_MAX
        | OP_F32_COPYSIGN => Some((ValueType::F32, ValueType::F32)),
        OP_F64_ADD | OP_F64_SUB | OP_F64_MUL | OP_F64_DIV | OP_F64_MIN | OP_F64_MAX
        | OP_F64_COPYSIGN => Some((ValueType::F64, ValueType::F64)),
        _ => None,
    }
}

// --- Dispatch ---

/// Decodes and validates an operator before invoking its visitor hook.
///
/// The hook observes the resulting state. A callback error stops validation as
/// `OpError::Visitor`.
pub(crate) fn step<V: OpVisitor>(
    st: &mut OpIterState,
    data: &[u8],
    env: &Env,
    ctx: &Context,
    opcode: u8,
    v: &mut V,
) -> Result<()> {
    match opcode {
        OP_NOP => {
            visit(v.on_nop(st))?;
            Ok(())
        }
        OP_UNREACHABLE => {
            read_unreachable(st)?;
            visit(v.on_unreachable(st))?;
            Ok(())
        }
        OP_I32_CONST => {
            let imm = read_i32_const(st, data)?;
            visit(v.on_i32_const(st, imm))?;
            Ok(())
        }
        OP_I64_CONST => {
            let imm = read_i64_const(st, data)?;
            visit(v.on_i64_const(st, imm))?;
            Ok(())
        }
        OP_F32_CONST => {
            let bits = read_f32_const(st, data)?;
            visit(v.on_f32_const(st, bits))?;
            Ok(())
        }
        OP_F64_CONST => {
            let bits = read_f64_const(st, data)?;
            visit(v.on_f64_const(st, bits))?;
            Ok(())
        }
        OP_DROP => {
            let ty = read_drop(st)?;
            visit(v.on_drop(st, ty))?;
            Ok(())
        }
        OP_SELECT => {
            let ty = read_select(st)?;
            visit(v.on_select(st, ty))?;
            Ok(())
        }
        OP_BLOCK => {
            let bt = read_block(st, data)?;
            visit(v.on_block(st, visitor_block_type(bt)))?;
            Ok(())
        }
        OP_LOOP => {
            let bt = read_loop(st, data)?;
            visit(v.on_loop(st, visitor_block_type(bt)))?;
            Ok(())
        }
        OP_IF => {
            let bt = read_if(st, data)?;
            visit(v.on_if(st, visitor_block_type(bt)))?;
            Ok(())
        }
        OP_ELSE => {
            let bt = read_else(st)?;
            visit(v.on_else(st, visitor_block_type(bt)))?;
            Ok(())
        }
        OP_END => {
            let (kind, bt) = read_end(st)?;
            visit(v.on_end(st, kind, visitor_block_type(bt)))?;
            Ok(())
        }
        OP_BR => {
            let (depth, bt) = read_br(st, data)?;
            visit(v.on_br(st, depth, visitor_result_type(bt)))?;
            Ok(())
        }
        OP_BR_IF => {
            let (depth, bt) = read_br_if(st, data)?;
            visit(v.on_br_if(st, depth, visitor_result_type(bt)))?;
            Ok(())
        }
        OP_BR_TABLE => {
            let (default, common) = read_br_table(st, data, v)?;
            visit(v.on_br_table(st, default, visitor_result_type(common)))?;
            Ok(())
        }
        OP_RETURN => {
            read_return(st, ctx)?;
            visit(v.on_return(st))?;
            Ok(())
        }
        OP_CALL => {
            let idx = read_call(st, data, env)?;
            visit(v.on_call(st, idx))?;
            Ok(())
        }
        OP_CALL_INDIRECT => {
            let idx = read_call_indirect(st, data, env)?;
            visit(v.on_call_indirect(st, idx))?;
            Ok(())
        }
        OP_LOCAL_GET => {
            let idx = read_local_get(st, data, ctx)?;
            visit(v.on_local_get(st, idx))?;
            Ok(())
        }
        OP_LOCAL_SET => {
            let idx = read_local_set(st, data, ctx)?;
            visit(v.on_local_set(st, idx))?;
            Ok(())
        }
        OP_LOCAL_TEE => {
            let idx = read_local_tee(st, data, ctx)?;
            visit(v.on_local_tee(st, idx))?;
            Ok(())
        }
        OP_GLOBAL_GET => {
            let idx = read_global_get(st, data, env)?;
            visit(v.on_global_get(st, idx))?;
            Ok(())
        }
        OP_GLOBAL_SET => {
            let idx = read_global_set(st, data, env)?;
            visit(v.on_global_set(st, idx))?;
            Ok(())
        }
        _ => step_memory(st, data, env, opcode, v),
    }
}

fn step_memory<V: OpVisitor>(
    st: &mut OpIterState,
    data: &[u8],
    env: &Env,
    opcode: u8,
    v: &mut V,
) -> Result<()> {
    match opcode {
        OP_I32_LOAD => {
            let memarg = read_load(st, data, env, ValueType::I32, 2)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_I64_LOAD => {
            let memarg = read_load(st, data, env, ValueType::I64, 3)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_F32_LOAD => {
            let memarg = read_load(st, data, env, ValueType::F32, 2)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_F64_LOAD => {
            let memarg = read_load(st, data, env, ValueType::F64, 3)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_I32_LOAD8_S | OP_I32_LOAD8_U => {
            let memarg = read_load(st, data, env, ValueType::I32, 0)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_I32_LOAD16_S | OP_I32_LOAD16_U => {
            let memarg = read_load(st, data, env, ValueType::I32, 1)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_I64_LOAD8_S | OP_I64_LOAD8_U => {
            let memarg = read_load(st, data, env, ValueType::I64, 0)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_I64_LOAD16_S | OP_I64_LOAD16_U => {
            let memarg = read_load(st, data, env, ValueType::I64, 1)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_I64_LOAD32_S | OP_I64_LOAD32_U => {
            let memarg = read_load(st, data, env, ValueType::I64, 2)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_I32_STORE => {
            let memarg = read_store(st, data, env, ValueType::I32, 2)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_I64_STORE => {
            let memarg = read_store(st, data, env, ValueType::I64, 3)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_F32_STORE => {
            let memarg = read_store(st, data, env, ValueType::F32, 2)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_F64_STORE => {
            let memarg = read_store(st, data, env, ValueType::F64, 3)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_I32_STORE8 => {
            let memarg = read_store(st, data, env, ValueType::I32, 0)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_I32_STORE16 => {
            let memarg = read_store(st, data, env, ValueType::I32, 1)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_I64_STORE8 => {
            let memarg = read_store(st, data, env, ValueType::I64, 0)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_I64_STORE16 => {
            let memarg = read_store(st, data, env, ValueType::I64, 1)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_I64_STORE32 => {
            let memarg = read_store(st, data, env, ValueType::I64, 2)?;
            visit(visit_memory(v, st, opcode, memarg))?;
            Ok(())
        }
        OP_MEMORY_SIZE => {
            read_memory_size(st, data, env)?;
            visit(v.on_memory_size(st))?;
            Ok(())
        }
        OP_MEMORY_GROW => {
            read_memory_grow(st, data, env)?;
            visit(v.on_memory_grow(st))?;
            Ok(())
        }
        _ => step_numeric(st, opcode, v),
    }
}

/// Validates a numeric opcode and invokes its corresponding visitor hook.
fn step_numeric<V: OpVisitor>(st: &mut OpIterState, opcode: u8, v: &mut V) -> Result<()> {
    match convert_types(opcode) {
        Some((from, to)) => {
            read_conversion(st, from, to)?;
            visit(visit_numeric(v, st, opcode))?;
            return Ok(());
        }
        None => {}
    }
    match binary_types(opcode) {
        Some((ty, result)) => {
            read_binary(st, ty, result)?;
            visit(visit_numeric(v, st, opcode))?;
            return Ok(());
        }
        None => {}
    }
    Err(OpError::UnrecognizedOpcode)
}

// --- Multi-value control and signature handling ---

fn check_func_type(ft: &FuncType) -> Result<()> {
    if ft.params.len() > MAX_MULTI_VALUE_PARAMS {
        return Err(OpError::TooManyParams);
    }
    if ft.results.len() > MAX_MULTI_VALUE_RESULTS {
        return Err(OpError::TooManyResults);
    }
    Ok(())
}

fn pop_results(st: &mut OpIterState, env: &Env, ts: ResultType) -> Result<()> {
    match ts {
        ResultType::Empty => Ok(()),
        ResultType::One(t) => {
            pop_with_type(st, t)?;
            Ok(())
        }
        ResultType::Type { index, part } => {
            let i = index as usize;
            if i >= env.types.len() {
                return Err(OpError::UnknownType);
            }
            match part {
                TypePart::Params => pop_types(st, &env.types[i].params),
                TypePart::Results => pop_types(st, &env.types[i].results),
            }
        }
    }
}

fn push_results(st: &mut OpIterState, env: &Env, ts: ResultType) -> Result<()> {
    let n = ts.len(env)?;
    if n > usize::MAX - st.vals.len() {
        return Err(OpError::StackTooLarge);
    }
    match ts {
        ResultType::Empty => {}
        ResultType::One(t) => st.vals.push(StackType::Val(t)),
        ResultType::Type { index, part } => {
            let i = index as usize;
            if i >= env.types.len() {
                return Err(OpError::UnknownType);
            }
            match part {
                TypePart::Params => push_types(st, &env.types[i].params),
                TypePart::Results => push_types(st, &env.types[i].results),
            }
        }
    }
    Ok(())
}

fn same_types(env: &Env, a: ResultType, b: ResultType) -> Result<bool> {
    let n = a.len(env)?;
    if n != b.len(env)? {
        return Ok(false);
    }
    let mut i = 0;
    loop {
        if i >= n {
            return Ok(true);
        }
        match (a.get(env, i)?, b.get(env, i)?) {
            (Some(x), Some(y)) => {
                if x != y {
                    return Ok(false);
                }
            }
            _ => return Err(OpError::TypeMismatch),
        }
        i += 1;
    }
}

fn push_frame(st: &mut BodyState, kind: LabelKind, bt: BlockSignature) {
    st.core.ctrls.push(Ctrl {
        kind,
        block_type: BlockType::Empty,
        signature: bt,
        value_stack_base: st.core.vals.len(),
        polymorphic_base: false,
    });
}

fn enter_info(
    st: &mut BodyState,
    data: &[u8],
    env: &Env,
    kind: LabelKind,
) -> Result<BlockSignature> {
    let (bt, end) = signature::read_block_type(data, st.core.pos)?;
    st.core.pos = end;
    if let BlockSignature::TypeIndex(index) = bt {
        let i = index as usize;
        if i >= env.types.len() {
            return Err(OpError::UnknownType);
        }
        check_func_type(&env.types[i])?;
    }
    if let LabelKind::Then = kind {
        pop_with_type(&mut st.core, ValueType::I32)?;
    }
    pop_results(&mut st.core, env, bt.params())?;
    // The base excludes the inputs; both arms start with their declared inputs.
    push_frame(st, kind, bt);
    push_results(&mut st.core, env, bt.params())?;
    Ok(bt)
}

// Stable no-op projection used by the extracted semantic contracts.
#[allow(dead_code)]
fn enter(st: &mut BodyState, data: &[u8], env: &Env, kind: LabelKind) -> Result<()> {
    enter_info(st, data, env, kind)?;
    Ok(())
}

fn end_frame_info(
    st: &mut BodyState,
    env: &Env,
    is_else: bool,
) -> Result<(LabelKind, BlockSignature)> {
    let n = st.core.ctrls.len();
    if n == 0 {
        return Err(OpError::UnknownLabel);
    }
    let bt = st.core.ctrls[n - 1].signature;
    let frame = st.core.ctrls[n - 1];
    if is_else {
        match frame.kind {
            LabelKind::Then => {}
            _ => return Err(OpError::TypeMismatch),
        }
    } else if let LabelKind::Then = frame.kind {
        // An omitted else is the identity on the block's input values.
        if !same_types(env, bt.params(), bt.results())? {
            return Err(OpError::TypeMismatch);
        }
    }
    pop_results(&mut st.core, env, bt.results())?;
    if st.core.vals.len() != frame.value_stack_base {
        return Err(OpError::StackMismatch);
    }
    if is_else {
        st.core.ctrls[n - 1].kind = LabelKind::Else;
        st.core.ctrls[n - 1].polymorphic_base = false;
        push_results(&mut st.core, env, bt.params())?;
    } else {
        let _ = st.core.ctrls.pop();
        // There is no enclosing operand stack at function end.
        if n != 1 {
            push_results(&mut st.core, env, bt.results())?;
        }
    }
    Ok((frame.kind, bt))
}

// Stable no-op projection used by the extracted semantic contracts.
#[allow(dead_code)]
fn end_frame(st: &mut BodyState, env: &Env, is_else: bool) -> Result<()> {
    end_frame_info(st, env, is_else)?;
    Ok(())
}

fn label(st: &BodyState, depth: u32) -> Result<ResultType> {
    let n = st.core.ctrls.len();
    let d = depth as usize;
    if d >= n {
        return Err(OpError::UnknownLabel);
    }
    let i = n - 1 - d;
    match st.core.ctrls[i].kind {
        LabelKind::Loop => Ok(st.core.ctrls[i].signature.params()),
        _ => Ok(st.core.ctrls[i].signature.results()),
    }
}

fn read_label_info(st: &mut BodyState, data: &[u8]) -> Result<(u32, ResultType)> {
    let (depth, end) = read_u32_leb(data, st.core.pos)?;
    st.core.pos = end;
    let types = label(st, depth)?;
    Ok((depth, types))
}

// Stable no-op projection used by the extracted semantic contracts.
#[allow(dead_code)]
fn read_multi_value_label(st: &mut BodyState, data: &[u8]) -> Result<ResultType> {
    let (_, types) = read_label_info(st, data)?;
    Ok(types)
}

fn branch_info(
    st: &mut BodyState,
    data: &[u8],
    env: &Env,
    conditional: bool,
) -> Result<(u32, ResultType)> {
    let (depth, ts) = read_label_info(st, data)?;
    if conditional {
        pop_with_type(&mut st.core, ValueType::I32)?;
    }
    pop_results(&mut st.core, env, ts)?;
    if conditional {
        push_results(&mut st.core, env, ts)?;
    } else {
        mark_unreachable(&mut st.core);
    }
    Ok((depth, ts))
}

// Stable no-op projection used by the extracted semantic contracts.
#[allow(dead_code)]
fn branch(st: &mut BodyState, data: &[u8], env: &Env, conditional: bool) -> Result<()> {
    branch_info(st, data, env, conditional)?;
    Ok(())
}

/// Checks the unchanged operand suffix against a branch-table target.
///
/// Keeping `Bot` unresolved allows it to match different concrete target types
/// under the Wasm 2.0 common-subtype rule.
fn check_suffix(st: &OpIterState, env: &Env, ts: ResultType) -> Result<()> {
    let base = cur_base(st);
    let mut stack = st.vals.len();
    let mut i = ts.len(env)?;
    loop {
        if i == 0 {
            return Ok(());
        }
        i -= 1;
        let expected = match ts.get(env, i)? {
            Some(t) => t,
            None => return Err(OpError::TypeMismatch),
        };
        if stack == base {
            if !cur_polymorphic(st) {
                return Err(OpError::EmptyStack);
            }
        } else {
            stack -= 1;
            if let StackType::Val(actual) = st.vals[stack] {
                if actual != expected {
                    return Err(OpError::TypeMismatch);
                }
            }
        }
    }
}

fn branch_table_with<V: OpVisitor>(
    st: &mut BodyState,
    data: &[u8],
    env: &Env,
    visitor: &mut V,
) -> Result<()> {
    let (count, end) = read_u32_leb(data, st.core.pos)?;
    st.core.pos = end;
    pop_with_type(&mut st.core, ValueType::I32)?;
    let mut arity = None;
    let mut i = 0;
    loop {
        let (depth, ts) = read_label_info(st, data)?;
        if i != count {
            visit(visitor.on_br_table_label(&st.core, depth))?;
        }
        let n = ts.len(env)?;
        match arity {
            Some(expected) => {
                if expected != n {
                    return Err(OpError::TypeMismatch);
                }
            }
            None => arity = Some(n),
        }
        check_suffix(&st.core, env, ts)?;
        // Includes the default, without adding one to a possibly-maximal count.
        if i == count {
            mark_unreachable(&mut st.core);
            visit(visitor.on_br_table(&st.core, depth, ts))?;
            return Ok(());
        }
        i += 1;
    }
}

// Stable no-op projection used by the extracted semantic contracts.
#[allow(dead_code)]
fn branch_table(st: &mut BodyState, data: &[u8], env: &Env) -> Result<()> {
    let mut visitor = EmptyOpVisitor;
    branch_table_with(st, data, env, &mut visitor)
}

fn apply_func_type(st: &mut OpIterState, ft: &FuncType) -> Result<()> {
    check_func_type(ft)?;
    pop_types(st, &ft.params)?;
    if ft.results.len() > usize::MAX - st.vals.len() {
        return Err(OpError::StackTooLarge);
    }
    push_types(st, &ft.results);
    Ok(())
}

fn call_info(st: &mut BodyState, data: &[u8], env: &Env, indirect: bool) -> Result<u32> {
    let (index, end) = read_u32_leb(data, st.core.pos)?;
    st.core.pos = end;
    let i = index as usize;
    if indirect {
        let (reserved, end) = read_byte(data, st.core.pos)?;
        if reserved != 0 {
            return Err(OpError::ReservedByteNotZero);
        }
        st.core.pos = end;
        if env.table_types.is_empty() {
            return Err(OpError::UnknownTable);
        }
        if i >= env.types.len() {
            return Err(OpError::UnknownType);
        }
        pop_with_type(&mut st.core, ValueType::I32)?;
        apply_func_type(&mut st.core, &env.types[i])?;
    } else {
        if i >= env.func_types.len() {
            return Err(OpError::UnknownFunc);
        }
        apply_func_type(&mut st.core, &env.func_types[i])?;
    }
    Ok(index)
}

// Stable no-op projection used by the extracted semantic contracts.
#[allow(dead_code)]
fn call(st: &mut BodyState, data: &[u8], env: &Env, indirect: bool) -> Result<()> {
    call_info(st, data, env, indirect)?;
    Ok(())
}

// --- Shared body execution and profile entry points ---

/// Initializes the shared state from the selected profile and function signature.
fn initial_state(
    env: &Env,
    ctx: &Context,
    type_index: u32,
    profile: crate::ValidationProfile,
) -> Result<BodyState> {
    match profile {
        crate::ValidationProfile::Wasm1 => Ok(BodyState {
            core: start_function(&ctx.results),
        }),
        crate::ValidationProfile::MultiValue => {
            let i = type_index as usize;
            if i >= env.types.len() {
                return Err(OpError::UnknownType);
            }
            check_func_type(&env.types[i])?;
            let mut st = BodyState {
                core: OpIterState {
                    vals: Vec::new(),
                    ctrls: Vec::new(),
                    pos: 0,
                },
            };
            push_frame(
                &mut st,
                LabelKind::Body,
                BlockSignature::TypeIndex(type_index),
            );
            Ok(st)
        }
    }
}

/// Runs the shared body loop with the selected profile's control rules.
fn body_loop<V: OpVisitor>(
    data: &[u8],
    env: &Env,
    ctx: &Context,
    type_index: u32,
    profile: crate::ValidationProfile,
    visitor: &mut V,
    mut st: BodyState,
) -> Result<()> {
    loop {
        if st.core.ctrls.is_empty() {
            if st.core.pos != data.len() {
                return Err(OpError::TrailingBytes);
            }
            return Ok(());
        }
        let (op, end) = read_byte(data, st.core.pos)?;
        st.core.pos = end;
        step_profile(&mut st, data, env, ctx, type_index, profile, op, visitor)?;
    }
}

/// Selects profile-specific control handling or shared scalar dispatch.
fn step_profile<V: OpVisitor>(
    st: &mut BodyState,
    data: &[u8],
    env: &Env,
    ctx: &Context,
    type_index: u32,
    profile: crate::ValidationProfile,
    op: u8,
    visitor: &mut V,
) -> Result<()> {
    match profile {
        crate::ValidationProfile::Wasm1 => step(&mut st.core, data, env, ctx, op, visitor),
        crate::ValidationProfile::MultiValue => {
            match op {
                OP_BLOCK => {
                    let bt = enter_info(st, data, env, LabelKind::Block)?;
                    visit(visitor.on_block(&st.core, bt))?;
                }
                OP_LOOP => {
                    let bt = enter_info(st, data, env, LabelKind::Loop)?;
                    visit(visitor.on_loop(&st.core, bt))?;
                }
                OP_IF => {
                    let bt = enter_info(st, data, env, LabelKind::Then)?;
                    visit(visitor.on_if(&st.core, bt))?;
                }
                OP_ELSE => {
                    let (_, bt) = end_frame_info(st, env, true)?;
                    visit(visitor.on_else(&st.core, bt))?;
                }
                OP_END => {
                    let (kind, bt) = end_frame_info(st, env, false)?;
                    visit(visitor.on_end(&st.core, kind, bt))?;
                }
                OP_BR => {
                    let (depth, ts) = branch_info(st, data, env, false)?;
                    visit(visitor.on_br(&st.core, depth, ts))?;
                }
                OP_BR_IF => {
                    let (depth, ts) = branch_info(st, data, env, true)?;
                    visit(visitor.on_br_if(&st.core, depth, ts))?;
                }
                OP_BR_TABLE => branch_table_with(st, data, env, visitor)?,
                OP_RETURN => {
                    pop_results(
                        &mut st.core,
                        env,
                        ResultType::Type {
                            index: type_index,
                            part: TypePart::Results,
                        },
                    )?;
                    mark_unreachable(&mut st.core);
                    visit(visitor.on_return(&st.core))?;
                }
                OP_CALL => {
                    let idx = call_info(st, data, env, false)?;
                    visit(visitor.on_call(&st.core, idx))?;
                }
                OP_CALL_INDIRECT => {
                    let idx = call_info(st, data, env, true)?;
                    visit(visitor.on_call_indirect(&st.core, idx))?;
                }
                _ => {
                    // Every scalar instruction pushes at most one value.
                    if st.core.vals.len() == usize::MAX {
                        return Err(OpError::StackTooLarge);
                    }
                    step(&mut st.core, data, env, ctx, op, visitor)?;
                }
            }
            Ok(())
        }
    }
}

/// Validates a body through the common worker under the selected profile.
pub(crate) fn validate_body_with_profile<V: OpVisitor>(
    data: &[u8],
    env: &Env,
    ctx: &Context,
    type_index: u32,
    profile: crate::ValidationProfile,
    visitor: &mut V,
) -> Result<()> {
    if data.len() > MAX_FUNCTION_BYTES {
        return Err(OpError::BodyTooLarge);
    }
    let st = initial_state(env, ctx, type_index, profile)?;
    body_loop(data, env, ctx, type_index, profile, visitor, st)
}

/// Validates a multi-value body with operator callbacks.
///
/// `ctx.locals` contains the parameters followed by declared locals; `type_index`
/// selects the function's results from `env`. Parameters enter the local space,
/// not the operand stack. The enclosing entry validator reports the
/// function-start callback. Full control signatures are stored in
/// `Ctrl.signature`.
pub(crate) fn validate_multi_value_body_with<V: OpVisitor>(
    data: &[u8],
    env: &Env,
    ctx: &Context,
    type_index: u32,
    visitor: &mut V,
) -> Result<()> {
    validate_body_with_profile(
        data,
        env,
        ctx,
        type_index,
        crate::ValidationProfile::MultiValue,
        visitor,
    )
}

/// Validates a multi-value body with accepting operator callbacks.
#[allow(dead_code)] // Retained as an extracted proof entry point.
pub(crate) fn validate_multi_value_body(
    data: &[u8],
    env: &Env,
    locals: Vec<ValueType>,
    type_index: u32,
) -> Result<()> {
    let ctx = Context {
        locals,
        results: Vec::new(),
    };
    let mut visitor = EmptyOpVisitor;
    validate_multi_value_body_with(data, env, &ctx, type_index, &mut visitor)
}

/// Validates a Wasm 1.0 instruction body with operator callbacks.
///
/// `data` contains exactly the instruction bytes, including the final `end` and
/// excluding local declarations. `ctx` contains the actual parameters, declared
/// locals, and zero or one function results. `env` is the decoded environment of
/// that module. The module entry validator establishes these conditions.
pub(crate) fn validate_body_with<V: OpVisitor>(
    data: &[u8],
    env: &Env,
    ctx: &Context,
    v: &mut V,
) -> Result<()> {
    validate_body_with_profile(data, env, ctx, 0, crate::ValidationProfile::Wasm1, v)
}

/// Validates a Wasm 1.0 body with accepting callbacks and the same component
/// preconditions.
#[allow(dead_code)] // Retained as an extracted proof entry point.
pub(crate) fn validate_body(data: &[u8], env: &Env, ctx: &Context) -> Result<()> {
    let mut nop = EmptyOpVisitor;
    validate_body_with(data, env, ctx, &mut nop)
}

// --- Operator visitors and dispatch tables ---

/// The result of a visitor callback; an error stops validation.
pub type VisitResult = core::result::Result<(), VisitError>;

/// Defines the numeric opcode-to-hook mapping shared by hook declarations and
/// dispatch.
macro_rules! numeric_table {
    ($callback:ident) => {
        $callback! {
        OP_I32_EQZ => on_i32_eqz;
        OP_I32_EQ => on_i32_eq;
        OP_I32_NE => on_i32_ne;
        OP_I32_LT_S => on_i32_lt_s;
        OP_I32_LT_U => on_i32_lt_u;
        OP_I32_GT_S => on_i32_gt_s;
        OP_I32_GT_U => on_i32_gt_u;
        OP_I32_LE_S => on_i32_le_s;
        OP_I32_LE_U => on_i32_le_u;
        OP_I32_GE_S => on_i32_ge_s;
        OP_I32_GE_U => on_i32_ge_u;
        OP_I64_EQZ => on_i64_eqz;
        OP_I64_EQ => on_i64_eq;
        OP_I64_NE => on_i64_ne;
        OP_I64_LT_S => on_i64_lt_s;
        OP_I64_LT_U => on_i64_lt_u;
        OP_I64_GT_S => on_i64_gt_s;
        OP_I64_GT_U => on_i64_gt_u;
        OP_I64_LE_S => on_i64_le_s;
        OP_I64_LE_U => on_i64_le_u;
        OP_I64_GE_S => on_i64_ge_s;
        OP_I64_GE_U => on_i64_ge_u;
        OP_F32_EQ => on_f32_eq;
        OP_F32_NE => on_f32_ne;
        OP_F32_LT => on_f32_lt;
        OP_F32_GT => on_f32_gt;
        OP_F32_LE => on_f32_le;
        OP_F32_GE => on_f32_ge;
        OP_F64_EQ => on_f64_eq;
        OP_F64_NE => on_f64_ne;
        OP_F64_LT => on_f64_lt;
        OP_F64_GT => on_f64_gt;
        OP_F64_LE => on_f64_le;
        OP_F64_GE => on_f64_ge;
        OP_I32_SUB => on_i32_sub;
        OP_I32_MUL => on_i32_mul;
        OP_I32_DIV_S => on_i32_div_s;
        OP_I32_DIV_U => on_i32_div_u;
        OP_I32_REM_S => on_i32_rem_s;
        OP_I32_REM_U => on_i32_rem_u;
        OP_I32_AND => on_i32_and;
        OP_I32_OR => on_i32_or;
        OP_I32_XOR => on_i32_xor;
        OP_I32_SHL => on_i32_shl;
        OP_I32_SHR_S => on_i32_shr_s;
        OP_I32_SHR_U => on_i32_shr_u;
        OP_I32_ROTL => on_i32_rotl;
        OP_I32_ROTR => on_i32_rotr;
        OP_I64_ADD => on_i64_add;
        OP_I64_SUB => on_i64_sub;
        OP_I64_MUL => on_i64_mul;
        OP_I64_DIV_S => on_i64_div_s;
        OP_I64_DIV_U => on_i64_div_u;
        OP_I64_REM_S => on_i64_rem_s;
        OP_I64_REM_U => on_i64_rem_u;
        OP_I64_AND => on_i64_and;
        OP_I64_OR => on_i64_or;
        OP_I64_XOR => on_i64_xor;
        OP_I64_SHL => on_i64_shl;
        OP_I64_SHR_S => on_i64_shr_s;
        OP_I64_SHR_U => on_i64_shr_u;
        OP_I64_ROTL => on_i64_rotl;
        OP_I64_ROTR => on_i64_rotr;
        OP_F32_ADD => on_f32_add;
        OP_F32_SUB => on_f32_sub;
        OP_F32_MUL => on_f32_mul;
        OP_F32_DIV => on_f32_div;
        OP_F32_MIN => on_f32_min;
        OP_F32_MAX => on_f32_max;
        OP_F32_COPYSIGN => on_f32_copysign;
        OP_F64_ADD => on_f64_add;
        OP_F64_SUB => on_f64_sub;
        OP_F64_MUL => on_f64_mul;
        OP_F64_DIV => on_f64_div;
        OP_F64_MIN => on_f64_min;
        OP_F64_MAX => on_f64_max;
        OP_F64_COPYSIGN => on_f64_copysign;
        OP_I32_CLZ => on_i32_clz;
        OP_I32_CTZ => on_i32_ctz;
        OP_I32_POPCNT => on_i32_popcnt;
        OP_I32_ADD => on_i32_add;
        OP_I64_CLZ => on_i64_clz;
        OP_I64_CTZ => on_i64_ctz;
        OP_I64_POPCNT => on_i64_popcnt;
        OP_F32_ABS => on_f32_abs;
        OP_F32_NEG => on_f32_neg;
        OP_F32_CEIL => on_f32_ceil;
        OP_F32_FLOOR => on_f32_floor;
        OP_F32_TRUNC => on_f32_trunc;
        OP_F32_NEAREST => on_f32_nearest;
        OP_F32_SQRT => on_f32_sqrt;
        OP_F64_ABS => on_f64_abs;
        OP_F64_NEG => on_f64_neg;
        OP_F64_CEIL => on_f64_ceil;
        OP_F64_FLOOR => on_f64_floor;
        OP_F64_TRUNC => on_f64_trunc;
        OP_F64_NEAREST => on_f64_nearest;
        OP_F64_SQRT => on_f64_sqrt;
        OP_I32_WRAP_I64 => on_i32_wrap_i64;
        OP_I32_TRUNC_F32_S => on_i32_trunc_f32_s;
        OP_I32_TRUNC_F32_U => on_i32_trunc_f32_u;
        OP_I32_TRUNC_F64_S => on_i32_trunc_f64_s;
        OP_I32_TRUNC_F64_U => on_i32_trunc_f64_u;
        OP_I64_EXTEND_I32_S => on_i64_extend_i32_s;
        OP_I64_EXTEND_I32_U => on_i64_extend_i32_u;
        OP_I64_TRUNC_F32_S => on_i64_trunc_f32_s;
        OP_I64_TRUNC_F32_U => on_i64_trunc_f32_u;
        OP_I64_TRUNC_F64_S => on_i64_trunc_f64_s;
        OP_I64_TRUNC_F64_U => on_i64_trunc_f64_u;
        OP_F32_CONVERT_I32_S => on_f32_convert_i32_s;
        OP_F32_CONVERT_I32_U => on_f32_convert_i32_u;
        OP_F32_CONVERT_I64_S => on_f32_convert_i64_s;
        OP_F32_CONVERT_I64_U => on_f32_convert_i64_u;
        OP_F32_DEMOTE_F64 => on_f32_demote_f64;
        OP_F64_CONVERT_I32_S => on_f64_convert_i32_s;
        OP_F64_CONVERT_I32_U => on_f64_convert_i32_u;
        OP_F64_CONVERT_I64_S => on_f64_convert_i64_s;
        OP_F64_CONVERT_I64_U => on_f64_convert_i64_u;
        OP_F64_PROMOTE_F32 => on_f64_promote_f32;
        OP_I32_REINTERPRET_F32 => on_i32_reinterpret_f32;
        OP_I64_REINTERPRET_F64 => on_i64_reinterpret_f64;
        OP_F32_REINTERPRET_I32 => on_f32_reinterpret_i32;
        OP_F64_REINTERPRET_I64 => on_f64_reinterpret_i64;
        }
    };
}

/// Defines the memory opcode-to-hook mapping shared by hook declarations and
/// dispatch.
macro_rules! memory_table {
    ($callback:ident) => {
        $callback! {
        OP_I32_LOAD => on_i32_load;
        OP_I64_LOAD => on_i64_load;
        OP_F32_LOAD => on_f32_load;
        OP_F64_LOAD => on_f64_load;
        OP_I32_LOAD8_S => on_i32_load8_s;
        OP_I32_LOAD8_U => on_i32_load8_u;
        OP_I32_LOAD16_S => on_i32_load16_s;
        OP_I32_LOAD16_U => on_i32_load16_u;
        OP_I64_LOAD8_S => on_i64_load8_s;
        OP_I64_LOAD8_U => on_i64_load8_u;
        OP_I64_LOAD16_S => on_i64_load16_s;
        OP_I64_LOAD16_U => on_i64_load16_u;
        OP_I64_LOAD32_S => on_i64_load32_s;
        OP_I64_LOAD32_U => on_i64_load32_u;
        OP_I32_STORE => on_i32_store;
        OP_I64_STORE => on_i64_store;
        OP_F32_STORE => on_f32_store;
        OP_F64_STORE => on_f64_store;
        OP_I32_STORE8 => on_i32_store8;
        OP_I32_STORE16 => on_i32_store16;
        OP_I64_STORE8 => on_i64_store8;
        OP_I64_STORE16 => on_i64_store16;
        OP_I64_STORE32 => on_i64_store32;
        }
    };
}

macro_rules! numeric_hooks {
    ($($op:ident => $hook:ident;)*) => {
        $(fn $hook(&mut self, _st: &OpIterState) -> VisitResult {
            Ok(())
        })*
    };
}

macro_rules! memory_hooks {
    ($($op:ident => $hook:ident;)*) => {
        $(fn $hook(&mut self, _st: &OpIterState, _memarg: MemArg) -> VisitResult {
            Ok(())
        })*
    };
}

/// Callbacks for function context and decoded operators during batch validation.
///
/// Operator hooks receive the state after the operator's validation effects, with
/// a cursor relative to the instruction body. Hooks default to accepting. They
/// cannot mutate validator state or bypass checks.
///
/// Callbacks must return normally for termination and accept for completeness. An
/// error stops validation and may reject an otherwise valid module. Branch-table
/// label hooks run after label decoding and bounds checks but before all target
/// compatibility checks finish.
pub trait OpVisitor {
    // --- The function around the operators ---

    /// Reports the function context before validating its instruction body.
    ///
    /// `_body_begin.._body_end` identifies instruction bytes within
    /// `CodeBatch::code`, excluding local declarations. Operator-state
    /// cursors are relative to `_body_begin`. `_type_idx` selects the function's
    /// declared signature.
    fn on_function_start(
        &mut self,
        _ctx: &Context,
        _type_idx: u32,
        _body_begin: usize,
        _body_end: usize,
    ) -> VisitResult {
        Ok(())
    }

    // --- Control ---

    fn on_unreachable(&mut self, _st: &OpIterState) -> VisitResult {
        Ok(())
    }

    fn on_nop(&mut self, _st: &OpIterState) -> VisitResult {
        Ok(())
    }

    fn on_block(&mut self, _st: &OpIterState, _bt: crate::signature::BlockType) -> VisitResult {
        Ok(())
    }

    fn on_loop(&mut self, _st: &OpIterState, _bt: crate::signature::BlockType) -> VisitResult {
        Ok(())
    }

    fn on_if(&mut self, _st: &OpIterState, _bt: crate::signature::BlockType) -> VisitResult {
        Ok(())
    }

    /// Reports the transition to an else arm with the enclosing if signature.
    fn on_else(&mut self, _st: &OpIterState, _bt: crate::signature::BlockType) -> VisitResult {
        Ok(())
    }

    /// Reports a closed frame and its signature.
    ///
    /// A bare if closes with `LabelKind::Then`, identifying its implicit empty
    /// else arm.
    fn on_end(
        &mut self,
        _st: &OpIterState,
        _kind: LabelKind,
        _bt: crate::signature::BlockType,
    ) -> VisitResult {
        Ok(())
    }

    /// Reports a branch target: loop parameters or the results of another frame.
    fn on_br(
        &mut self,
        _st: &OpIterState,
        _depth: u32,
        _types: crate::signature::ResultType,
    ) -> VisitResult {
        Ok(())
    }

    fn on_br_if(
        &mut self,
        _st: &OpIterState,
        _depth: u32,
        _types: crate::signature::ResultType,
    ) -> VisitResult {
        Ok(())
    }

    /// Reports a non-default branch-table label after decoding and bounds checks.
    ///
    /// Labels arrive in encoded order, before all target compatibility checks
    /// finish. `on_br_table` reports the default label and completes the
    /// operator.
    fn on_br_table_label(&mut self, _st: &OpIterState, _depth: u32) -> VisitResult {
        Ok(())
    }

    /// Reports the completed branch table and its default target signature.
    ///
    /// Targets have equal arity. In the multi-value profile, unreachable operands
    /// may match different concrete target types.
    fn on_br_table(
        &mut self,
        _st: &OpIterState,
        _default: u32,
        _default_types: crate::signature::ResultType,
    ) -> VisitResult {
        Ok(())
    }

    fn on_return(&mut self, _st: &OpIterState) -> VisitResult {
        Ok(())
    }

    fn on_call(&mut self, _st: &OpIterState, _idx: u32) -> VisitResult {
        Ok(())
    }

    fn on_call_indirect(&mut self, _st: &OpIterState, _type_idx: u32) -> VisitResult {
        Ok(())
    }

    // --- Parametric ---

    /// Reports the dropped operand type, which may be `StackType::Bot` in
    /// unreachable code.
    fn on_drop(&mut self, _st: &OpIterState, _ty: StackType) -> VisitResult {
        Ok(())
    }

    /// Reports the common operand type selected and pushed by `select`.
    fn on_select(&mut self, _st: &OpIterState, _ty: StackType) -> VisitResult {
        Ok(())
    }

    // --- Variables ---

    fn on_local_get(&mut self, _st: &OpIterState, _idx: u32) -> VisitResult {
        Ok(())
    }

    fn on_local_set(&mut self, _st: &OpIterState, _idx: u32) -> VisitResult {
        Ok(())
    }

    fn on_local_tee(&mut self, _st: &OpIterState, _idx: u32) -> VisitResult {
        Ok(())
    }

    fn on_global_get(&mut self, _st: &OpIterState, _idx: u32) -> VisitResult {
        Ok(())
    }

    fn on_global_set(&mut self, _st: &OpIterState, _idx: u32) -> VisitResult {
        Ok(())
    }

    // --- Memory size ---

    fn on_memory_size(&mut self, _st: &OpIterState) -> VisitResult {
        Ok(())
    }

    fn on_memory_grow(&mut self, _st: &OpIterState) -> VisitResult {
        Ok(())
    }

    // --- Constants ---

    fn on_i32_const(&mut self, _st: &OpIterState, _v: i32) -> VisitResult {
        Ok(())
    }

    fn on_i64_const(&mut self, _st: &OpIterState, _v: i64) -> VisitResult {
        Ok(())
    }

    /// Reports the exact floating-point immediate bits, preserving signed zero
    /// and NaN payloads.
    fn on_f32_const(&mut self, _st: &OpIterState, _bits: u32) -> VisitResult {
        Ok(())
    }

    fn on_f64_const(&mut self, _st: &OpIterState, _bits: u64) -> VisitResult {
        Ok(())
    }

    // --- Loads and stores, one per opcode ---

    memory_table!(memory_hooks);

    // --- The numeric operators, one per opcode ---

    numeric_table!(numeric_hooks);
}

/// An operator visitor whose default hooks all accept.
pub struct EmptyOpVisitor;

impl OpVisitor for EmptyOpVisitor {}

macro_rules! numeric_fanout {
    ($($op:ident => $hook:ident;)*) => {
        /// Invokes the numeric hook selected by the shared opcode table.
        pub(crate) fn visit_numeric<V: OpVisitor>(
            v: &mut V,
            st: &OpIterState,
            opcode: u8,
        ) -> VisitResult {
            match opcode {
                $($op => v.$hook(st),)*
                _ => Ok(()),
            }
        }
    };
}

macro_rules! memory_fanout {
    ($($op:ident => $hook:ident;)*) => {
        /// Invokes the memory hook selected by the shared opcode table.
        pub(crate) fn visit_memory<V: OpVisitor>(
            v: &mut V,
            st: &OpIterState,
            opcode: u8,
            memarg: MemArg,
        ) -> VisitResult {
            match opcode {
                $($op => v.$hook(st, memarg),)*
                _ => Ok(()),
            }
        }
    };
}

numeric_table!(numeric_fanout);
memory_table!(memory_fanout);
