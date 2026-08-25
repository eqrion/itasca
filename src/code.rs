//! Streaming decode and validate for function bodies, and the push interface
//! a consumer is validated through.
//!
//! Nesting lives in an explicit control stack rather than the call stack, so
//! nothing here recurses and no AST is built. The byte-level reads are in
//! `reader`, which the module decoder also uses.
//!
//! What's public here is the vocabulary a hook is handed -- `OpIterState`,
//! `Ctrl`, `Context`, `BlockType`, `MemArg`, and the two stack enums -- the
//! `OP_*` opcode bytes, which belong to the binary format and are inert,
//! `validate_body`/`validate_body_with`, the raw entry point below the code
//! section's framing, and the [`OpVisitor`] push interface itself.
//! `module::validate_code_entry_with` is the one a consumer should call.
//!
//! [`OpVisitor`] is one hook per validated operator, so a consumer never
//! switches on an opcode the validator has already switched on. A hook
//! receives the operator's immediates already decoded and checked, plus the
//! validator state, and may decline the body. The many hooks that carry no
//! immediates beyond a `memarg` come from one table each, below, which also
//! generates the two fan-out functions dispatch goes through; the rest have
//! immediates of their own and are written out. Every hook has a default
//! that does nothing, so a consumer only writes the ones it wants.

use alloc::vec::Vec;
use crate::module::Env;
use crate::error::{OpError, VisitError};
use crate::limits::{MAX_FUNCTION_BYTES, MAX_RESULTS};
use crate::reader::{
    read_byte, read_f32_bits, read_f64_bits, read_s32_leb, read_s64_leb, read_u32_leb,
};
use crate::types::{GlobalType, Mut, ValueType};

/// Mirrors `block_type` (Wasm 1.0: single optional result).
///
/// An instruction immediate, so it lives here rather than in `types`: only the
/// readers in this file produce or consume one.
#[cfg_attr(not(charon), derive(Debug))]
#[derive(Clone, Copy)]
pub enum BlockType {
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

/// Memory argument for load and store instructions.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub struct MemArg {
    pub align: u32,
    pub offset: u32,
}

/// The part of the typing context (spec 3.1) that is specific to one
/// function: its locals and result types. Everything module-wide stays on
/// the `Env`, so validating a second function costs one of these rather than
/// a copy of the index spaces.
///
/// A hook receives one of these built by `validate_code_entry_with` from the
/// module's own declarations. Building one by hand is only sound as an
/// argument to `validate_body_with`, whose preconditions say what it has to
/// hold.
pub struct Context {
    pub locals: Vec<ValueType>,
    /// The function's result types, which `return` branches to.
    pub results: Vec<ValueType>,
}

type Result<T> = core::result::Result<T, OpError>;

/// A hook's verdict, translated into a validator verdict.
fn visit(r: core::result::Result<(), VisitError>) -> Result<()> {
    match r {
        Ok(()) => Ok(()),
        Err(e) => Err(OpError::Visitor(e)),
    }
}

/// The type of a value on the operand stack: a value type, or bottom for
/// unreachable code. Kept separate from `ValueType` so bottom cannot leak
/// into a function signature; that is why `ValueType` has no `Bot` of its own.
///
/// Equality is only derived outside `charon` builds: validation itself
/// never needs to compare these.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum StackType {
    Val(ValueType),
    Bot,
}

/// The kind of control frame on the control stack: the function body itself,
/// a `block`, a `loop`, or one side of an `if`.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum LabelKind {
    Body,
    Block,
    Loop,
    Then,
    Else,
}

/// A control frame, tracking one nested block, loop, if, or the function body.
#[cfg_attr(not(charon), derive(Debug))]
#[derive(Clone, Copy)]
pub struct Ctrl {
    pub kind: LabelKind,
    pub block_type: BlockType,
    /// Operand stack height below this frame.
    pub value_stack_base: usize,
    /// Set once the frame's remaining code is unreachable.
    pub polymorphic_base: bool,
}

/// The running state of a streaming operator validator: the operand stack,
/// the control stack, and the byte cursor. The cursor is a plain index
/// rather than a borrowed slice, so it can be threaded through calls freely.
pub struct OpIterState {
    pub vals: Vec<StackType>,
    pub ctrls: Vec<Ctrl>,
    pub pos: usize,
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
    if b == 0x40 {
        return Ok((BlockType::Empty, p));
    }
    if b == 0x7f {
        return Ok((BlockType::Value(ValueType::I32), p));
    }
    if b == 0x7e {
        return Ok((BlockType::Value(ValueType::I64), p));
    }
    if b == 0x7d {
        return Ok((BlockType::Value(ValueType::F32), p));
    }
    if b == 0x7c {
        return Ok((BlockType::Value(ValueType::F64), p));
    }
    Err(OpError::InvalidBlockType)
}

// --- Operand and control stack ---

fn cur_base(st: &OpIterState) -> usize {
    let n = st.ctrls.len();
    if n == 0 {
        return 0;
    }
    st.ctrls[n - 1].value_stack_base
}

fn cur_polymorphic(st: &OpIterState) -> bool {
    let n = st.ctrls.len();
    if n == 0 {
        return false;
    }
    st.ctrls[n - 1].polymorphic_base
}

fn push_val(st: &mut OpIterState, t: StackType) {
    st.vals.push(t);
}

/// Pop one operand. In unreachable code an exhausted frame yields `Bot`
/// instead of failing.
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

/// Pop one operand and require it to match `expected`. `Bot` matches
/// anything, since it stands for a value of unknown type in unreachable code.
fn pop_with_type(st: &mut OpIterState, expected: ValueType) -> Result<StackType> {
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

/// Pop `types` in reverse, since the last one is what sits on top of the
/// stack.
fn pop_types(st: &mut OpIterState, types: &[ValueType]) -> Result<()> {
    let mut i: usize = types.len();
    loop {
        if i == 0 {
            return Ok(());
        }
        i -= 1;
        pop_with_type(st, types[i])?;
    }
}

fn push_types(st: &mut OpIterState, types: &[ValueType]) {
    let mut i: usize = 0;
    loop {
        if i >= types.len() {
            return;
        }
        push_val(st, StackType::Val(types[i]));
        i += 1;
    }
}

/// Result types of a block type. Wasm 1.0 allows at most one.
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

/// What a branch to this frame must supply, as a block type: a loop's target
/// is its parameters, everything else's is its results. Wasm 1.0 block types
/// have no parameters, so a loop target is empty.
///
/// A block type rather than a list because `br_table` folds one of these per
/// label: `BlockType` is `Copy`, so the running "every target so far agrees"
/// state costs no allocation and needs no bound of its own.
fn branch_target_bt(c: &Ctrl) -> BlockType {
    match c.kind {
        LabelKind::Loop => BlockType::Empty,
        _ => c.block_type,
    }
}

fn branch_target_types(c: &Ctrl) -> Vec<ValueType> {
    block_results(&branch_target_bt(c))
}

fn push_ctrl(st: &mut OpIterState, kind: LabelKind, bt: BlockType) {
    let base = st.vals.len();
    st.ctrls.push(Ctrl {
        kind,
        block_type: bt,
        value_stack_base: base,
        polymorphic_base: false,
    });
}

/// Discard the current frame's operands and mark it unreachable.
fn mark_unreachable(st: &mut OpIterState) {
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

fn start_function(results: &[ValueType]) -> OpIterState {
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

fn control_stack_empty(st: &OpIterState) -> bool {
    st.ctrls.is_empty()
}

/// Read the next opcode and advance past it.
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

/// `[] -> [f32]`. The immediate's bits are returned; see `read_f32_bits`.
fn read_f32_const(st: &mut OpIterState, data: &[u8]) -> Result<u32> {
    let (v, p) = read_f32_bits(data, st.pos)?;
    st.pos = p;
    push_val(st, StackType::Val(ValueType::F32));
    Ok(v)
}

/// `[] -> [f64]`.
fn read_f64_const(st: &mut OpIterState, data: &[u8]) -> Result<u64> {
    let (v, p) = read_f64_bits(data, st.pos)?;
    st.pos = p;
    push_val(st, StackType::Val(ValueType::F64));
    Ok(v)
}

/// `[ty ty] -> [result]`: the binary operators, where `result == ty`, and the
/// comparisons, where `result == i32`. Validation cannot tell the two apart:
/// a comparison has a binary operator's stack effect with a different result
/// type, so one reader covers both and the opcode table supplies the pair.
fn read_binary(st: &mut OpIterState, ty: ValueType, result: ValueType) -> Result<()> {
    pop_with_type(st, ty)?;
    pop_with_type(st, ty)?;
    push_val(st, StackType::Val(result));
    Ok(())
}

/// `[from] -> [to]`: the unary operators, where `from == to`, and
/// `i32.eqz`/`i64.eqz`, where `to == i32`. As with `read_binary`, validation
/// cannot tell those apart, so one reader covers them and the opcode table
/// supplies the pair.
fn read_conversion(st: &mut OpIterState, from: ValueType, to: ValueType) -> Result<()> {
    pop_with_type(st, from)?;
    push_val(st, StackType::Val(to));
    Ok(())
}

fn read_drop(st: &mut OpIterState) -> Result<StackType> {
    pop_stack_type(st)
}

/// The common type of two operands, `Bot` absorbing. `select`'s "both
/// operands are numeric" side condition is vacuous in Wasm 1.0, where every
/// value type is a number type.
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

/// `[t t i32] -> [t]`, `t` being whatever the two value operands agree on:
/// the untyped form of `select`, the only one Wasm 1.0 has.
///
/// The two values come off with `pop_stack_type` rather than `pop_with_type`,
/// because `select` is the one operator whose operand type is not fixed by
/// the opcode. That also covers unreachable code: an exhausted polymorphic
/// frame yields `Bot` for both, the join is `Bot`, and `Bot` is what gets
/// pushed.
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

/// The declared type of local `idx`.
fn local_type(ctx: &Context, idx: u32) -> Result<ValueType> {
    let i = idx as usize;
    if i >= ctx.locals.len() {
        return Err(OpError::UnknownLocal);
    }
    Ok(ctx.locals[i])
}

/// The prologue the three local operators share: read the index and look its
/// type up. They differ only in the stack effect that follows, so this is where
/// the cursor moves and the context is consulted.
fn take_local(st: &mut OpIterState, data: &[u8], ctx: &Context) -> Result<(u32, ValueType)> {
    let (idx, p) = read_u32_leb(data, st.pos)?;
    st.pos = p;
    let t = local_type(ctx, idx)?;
    Ok((idx, t))
}

/// `[] -> [t]`, `t` being local `idx`'s type.
fn read_local_get(st: &mut OpIterState, data: &[u8], ctx: &Context) -> Result<u32> {
    let (idx, t) = take_local(st, data, ctx)?;
    push_val(st, StackType::Val(t));
    Ok(idx)
}

/// `[t] -> []`.
fn read_local_set(st: &mut OpIterState, data: &[u8], ctx: &Context) -> Result<u32> {
    let (idx, t) = take_local(st, data, ctx)?;
    pop_with_type(st, t)?;
    Ok(idx)
}

/// `[t] -> [t]`.
fn read_local_tee(st: &mut OpIterState, data: &[u8], ctx: &Context) -> Result<u32> {
    let (idx, t) = take_local(st, data, ctx)?;
    pop_with_type(st, t)?;
    push_val(st, StackType::Val(t));
    Ok(idx)
}

/// The declared type of global `idx`.
fn global_type(env: &Env, idx: u32) -> Result<GlobalType> {
    let i = idx as usize;
    if i >= env.global_types.len() {
        return Err(OpError::UnknownGlobal);
    }
    Ok(env.global_types[i])
}

/// `take_local`'s counterpart for the two global operators: the index and the
/// lookup. It yields the whole `GlobalType` because `global.set` consults the
/// mutability as well as the value type.
fn take_global(st: &mut OpIterState, data: &[u8], env: &Env) -> Result<(u32, GlobalType)> {
    let (idx, p) = read_u32_leb(data, st.pos)?;
    st.pos = p;
    let g = global_type(env, idx)?;
    Ok((idx, g))
}

/// `[] -> [t]`, `t` being global `idx`'s type.
fn read_global_get(st: &mut OpIterState, data: &[u8], env: &Env) -> Result<u32> {
    let (idx, g) = take_global(st, data, env)?;
    push_val(st, StackType::Val(g.valtype));
    Ok(idx)
}

/// `[t] -> []`, and only for a mutable global.
fn read_global_set(st: &mut OpIterState, data: &[u8], env: &Env) -> Result<u32> {
    let (idx, g) = take_global(st, data, env)?;
    match g.mutability {
        Mut::Const => return Err(OpError::ImmutableGlobal),
        Mut::Var => {}
    }
    pop_with_type(st, g.valtype)?;
    Ok(idx)
}

/// A byte the specification writes out as a literal zero: the memory index of
/// `memory.size` and `memory.grow` (spec 5.4.6: `0x3F 0x00`) and the table index
/// of `call_indirect` (spec 5.4.1: `0x11 y:typeidx 0x00`). Both are indices that
/// only multi-memory and reference types made non-zero.
fn read_reserved_zero(st: &mut OpIterState, data: &[u8]) -> Result<()> {
    let (b, p) = read_byte(data, st.pos)?;
    if b != 0 {
        return Err(OpError::ReservedByteNotZero);
    }
    st.pos = p;
    Ok(())
}

/// `[] -> [i32]`.
fn read_memory_size(st: &mut OpIterState, data: &[u8], env: &Env) -> Result<()> {
    read_reserved_zero(st, data)?;
    require_memory(env)?;
    push_val(st, StackType::Val(ValueType::I32));
    Ok(())
}

/// `[i32] -> [i32]`.
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

/// Whether a frame is an open then-branch, checked here rather than with
/// `match` at each call site since `LabelKind` has no `PartialEq`.
fn is_then(kind: LabelKind) -> bool {
    match kind {
        LabelKind::Then => true,
        LabelKind::Body => false,
        LabelKind::Block => false,
        LabelKind::Loop => false,
        LabelKind::Else => false,
    }
}

/// `[i32] -> []`, opening the then-branch: the condition is consumed and a
/// `Then` frame is opened, exactly like `block` otherwise.
fn read_if(st: &mut OpIterState, data: &[u8]) -> Result<BlockType> {
    let (bt, p) = read_block_type(data, st.pos)?;
    st.pos = p;
    pop_with_type(st, ValueType::I32)?;
    push_ctrl(st, LabelKind::Then, bt);
    Ok(bt)
}

/// Close the then-branch and open the else-branch in its place: the
/// then-branch's results must be on the stack, nothing else may be, and the
/// frame is rewritten in place rather than popped, since the block's own
/// `end` still has to close it.
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

/// Close the current frame: its results must be on the stack, nothing else
/// may be, and the results move onto the enclosing frame.
///
/// A `Then` frame reaching `end` directly means the else-branch is empty, so
/// it can only supply results the empty sequence already has: none. Wasm 1.0
/// requires an `if` with a result type to have an `else`; rejecting it here
/// rather than leaving it to `read_else`'s absence is what keeps this sound.
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

/// Read a label index and resolve it to the control frame it names. Depth 0 is
/// the innermost frame, so the index counts down from the top of the control
/// stack.
///
/// Separate from the opcode because `br_table` reads a whole vector of these
/// after one opcode byte.
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

/// Unconditional branch: the target's types must be available, and the rest
/// of the frame becomes unreachable.
fn read_br(st: &mut OpIterState, data: &[u8]) -> Result<(u32, BlockType)> {
    let (depth, target) = read_label(st, data)?;
    let types = branch_target_types(&target);
    pop_types(st, &types)?;
    mark_unreachable(st);
    Ok((depth, target.block_type))
}

/// Return: the function's results must be on the stack, and the rest of the
/// frame becomes unreachable, as for `br`. The result list comes from the
/// context rather than from a control frame, which is the only difference.
fn read_return(st: &mut OpIterState, ctx: &Context) -> Result<()> {
    pop_types(st, &ctx.results)?;
    mark_unreachable(st);
    Ok(())
}

/// Conditional branch: the condition is consumed and the target's types must
/// be available, but they stay on the stack, because the fall-through path
/// continues with them.
fn read_br_if(st: &mut OpIterState, data: &[u8]) -> Result<(u32, BlockType)> {
    let (depth, target) = read_label(st, data)?;
    let types = branch_target_types(&target);
    pop_with_type(st, ValueType::I32)?;
    pop_types(st, &types)?;
    push_types(st, &types);
    Ok((depth, target.block_type))
}

/// Fold one more branch target into "every target read so far agrees on this
/// block type". `None` is the state before the first one, which is why the
/// empty table is not a special case: the default label fills it in.
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

/// The `vec(labelidx)` immediate (spec 5.1.3), folded down to the block type
/// every one of its `count` entries agrees on.
///
/// A function of its own rather than a loop inside `read_br_table`, since
/// the reader has work to do afterwards.
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

/// `[t* i32] -> []`, `t*` being the branch target type every label in the
/// table shares. Otherwise has `br`'s effect: the operands are consumed and
/// the rest of the frame becomes unreachable.
///
/// **The depths are not returned.** Returning them means a `Vec` whose only
/// bound is the byte count, which would put `Vec::push` back on the live
/// panic list; the common target type is `Copy` and is all validation needs.
/// A compiler consumer has to re-read them.
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

/// The index immediate the two call operators share. `take_local` and
/// `take_global` are the same two lines followed by their own lookup; these two
/// look up different tables, so this is the whole of what they have in common.
fn take_index(st: &mut OpIterState, data: &[u8]) -> Result<u32> {
    let (idx, p) = read_u32_leb(data, st.pos)?;
    st.pos = p;
    Ok(idx)
}

/// Wasm 1.0 function types return at most one value; multi-value arrived later.
///
/// Checked here rather than left to the module validator for the reason
/// `MAX_RESULTS` records: without a bound on `call`'s push count nothing bounds
/// the operand stack. It only ever rejects, so soundness is unaffected.
fn require_single_result(results: &[ValueType]) -> Result<()> {
    if results.len() > MAX_RESULTS {
        return Err(OpError::TooManyResults);
    }
    Ok(())
}

/// `[params] -> [results]`, the callee's signature.
///
/// The first reader whose stack effect is a list from the context rather than
/// a shape fixed by the opcode, which is why `pop_types` and `push_types`
/// have to handle lists of any length. The type is indexed twice rather than
/// bound to a local, to avoid cloning the `FuncType`.
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

/// `[params i32] -> [results]`, the signature named by the type index, with
/// the table index on top.
///
/// Spec 5.4.1 writes it `0x11 y:typeidx x:tableidx`, and Wasm 1.0's only
/// table is table 0, so the table index is the reserved zero byte. The table
/// still has to exist, and its element type is `funcref`, which is the only
/// one Wasm 1.0 has.
fn read_call_indirect(
    st: &mut OpIterState,
    data: &[u8],
    env: &Env,
) -> Result<u32> {
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

/// `[i32] -> [ty]`, with a memory and an alignment constraint. One function
/// for all fourteen load opcodes.
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

/// `[i32 ty] -> []`. One function for all nine store opcodes.
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

/// Every memory operator needs a memory to operate on: Wasm 1.0 has at most
/// one, so the context either has it or the body is rejected.
fn require_memory(env: &Env) -> Result<()> {
    if env.mem_types.is_empty() {
        return Err(OpError::UnknownMemory);
    }
    Ok(())
}

/// Spec 3.3.7: the alignment may not exceed the access's natural alignment.
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

/// `[from] -> [to]`: the unary operators, `eqz`, and the conversions.
///
/// Wasm 1.0 sections 5.4.5. Ranges: `0x45`/`0x50` eqz, `0x67`-`0x69` and
/// `0x79`-`0x7b` integer unary, `0x8b`-`0x91` and `0x99`-`0x9f` float unary,
/// `0xa7`-`0xbf` conversions.
///
/// Grouped by shared `(from, to)` pair rather than one arm per opcode. Every
/// opcode still appears exactly once, under the pair it has.
pub(crate) fn convert_types(opcode: u8) -> Option<(ValueType, ValueType)> {
    if opcode == OP_I32_EQZ
        || opcode == OP_I32_CLZ
        || opcode == OP_I32_CTZ
        || opcode == OP_I32_POPCNT
    {
        return Some((ValueType::I32, ValueType::I32));
    }
    if opcode == OP_I64_CLZ || opcode == OP_I64_CTZ || opcode == OP_I64_POPCNT {
        return Some((ValueType::I64, ValueType::I64));
    }
    if opcode == OP_F32_ABS
        || opcode == OP_F32_NEG
        || opcode == OP_F32_CEIL
        || opcode == OP_F32_FLOOR
        || opcode == OP_F32_TRUNC
        || opcode == OP_F32_NEAREST
        || opcode == OP_F32_SQRT
    {
        return Some((ValueType::F32, ValueType::F32));
    }
    if opcode == OP_F64_ABS
        || opcode == OP_F64_NEG
        || opcode == OP_F64_CEIL
        || opcode == OP_F64_FLOOR
        || opcode == OP_F64_TRUNC
        || opcode == OP_F64_NEAREST
        || opcode == OP_F64_SQRT
    {
        return Some((ValueType::F64, ValueType::F64));
    }
    if opcode == OP_I64_EQZ || opcode == OP_I32_WRAP_I64 {
        return Some((ValueType::I64, ValueType::I32));
    }
    if opcode == OP_I32_TRUNC_F32_S
        || opcode == OP_I32_TRUNC_F32_U
        || opcode == OP_I32_REINTERPRET_F32
    {
        return Some((ValueType::F32, ValueType::I32));
    }
    if opcode == OP_I32_TRUNC_F64_S || opcode == OP_I32_TRUNC_F64_U {
        return Some((ValueType::F64, ValueType::I32));
    }
    if opcode == OP_I64_EXTEND_I32_S || opcode == OP_I64_EXTEND_I32_U {
        return Some((ValueType::I32, ValueType::I64));
    }
    if opcode == OP_I64_TRUNC_F32_S || opcode == OP_I64_TRUNC_F32_U {
        return Some((ValueType::F32, ValueType::I64));
    }
    if opcode == OP_I64_TRUNC_F64_S
        || opcode == OP_I64_TRUNC_F64_U
        || opcode == OP_I64_REINTERPRET_F64
    {
        return Some((ValueType::F64, ValueType::I64));
    }
    if opcode == OP_F32_CONVERT_I32_S
        || opcode == OP_F32_CONVERT_I32_U
        || opcode == OP_F32_REINTERPRET_I32
    {
        return Some((ValueType::I32, ValueType::F32));
    }
    if opcode == OP_F32_CONVERT_I64_S || opcode == OP_F32_CONVERT_I64_U {
        return Some((ValueType::I64, ValueType::F32));
    }
    if opcode == OP_F32_DEMOTE_F64 {
        return Some((ValueType::F64, ValueType::F32));
    }
    if opcode == OP_F64_CONVERT_I32_S || opcode == OP_F64_CONVERT_I32_U {
        return Some((ValueType::I32, ValueType::F64));
    }
    if opcode == OP_F64_CONVERT_I64_S
        || opcode == OP_F64_CONVERT_I64_U
        || opcode == OP_F64_REINTERPRET_I64
    {
        return Some((ValueType::I64, ValueType::F64));
    }
    if opcode == OP_F64_PROMOTE_F32 {
        return Some((ValueType::F32, ValueType::F64));
    }
    None
}

/// `[ty ty] -> [result]`: the binary operators (`result == ty`) and the
/// comparisons (`result == i32`).
///
/// Wasm 1.0 section 5.4.5. Ranges: `0x46`-`0x4F`, `0x51`-`0x5A`, `0x5B`-`0x60`
/// and `0x61`-`0x66` comparisons, `0x6A`-`0x78`, `0x7C`-`0x8A`, `0x92`-`0x98`
/// and `0xA0`-`0xA6` binary.
pub(crate) fn binary_types(opcode: u8) -> Option<(ValueType, ValueType)> {
    if opcode == OP_I32_EQ
        || opcode == OP_I32_NE
        || opcode == OP_I32_LT_S
        || opcode == OP_I32_LT_U
        || opcode == OP_I32_GT_S
        || opcode == OP_I32_GT_U
        || opcode == OP_I32_LE_S
        || opcode == OP_I32_LE_U
        || opcode == OP_I32_GE_S
        || opcode == OP_I32_GE_U
        || opcode == OP_I32_ADD
        || opcode == OP_I32_SUB
        || opcode == OP_I32_MUL
        || opcode == OP_I32_DIV_S
        || opcode == OP_I32_DIV_U
        || opcode == OP_I32_REM_S
        || opcode == OP_I32_REM_U
        || opcode == OP_I32_AND
        || opcode == OP_I32_OR
        || opcode == OP_I32_XOR
        || opcode == OP_I32_SHL
        || opcode == OP_I32_SHR_S
        || opcode == OP_I32_SHR_U
        || opcode == OP_I32_ROTL
        || opcode == OP_I32_ROTR
    {
        return Some((ValueType::I32, ValueType::I32));
    }
    if opcode == OP_I64_EQ
        || opcode == OP_I64_NE
        || opcode == OP_I64_LT_S
        || opcode == OP_I64_LT_U
        || opcode == OP_I64_GT_S
        || opcode == OP_I64_GT_U
        || opcode == OP_I64_LE_S
        || opcode == OP_I64_LE_U
        || opcode == OP_I64_GE_S
        || opcode == OP_I64_GE_U
    {
        return Some((ValueType::I64, ValueType::I32));
    }
    if opcode == OP_F32_EQ
        || opcode == OP_F32_NE
        || opcode == OP_F32_LT
        || opcode == OP_F32_GT
        || opcode == OP_F32_LE
        || opcode == OP_F32_GE
    {
        return Some((ValueType::F32, ValueType::I32));
    }
    if opcode == OP_F64_EQ
        || opcode == OP_F64_NE
        || opcode == OP_F64_LT
        || opcode == OP_F64_GT
        || opcode == OP_F64_LE
        || opcode == OP_F64_GE
    {
        return Some((ValueType::F64, ValueType::I32));
    }
    if opcode == OP_I64_ADD
        || opcode == OP_I64_SUB
        || opcode == OP_I64_MUL
        || opcode == OP_I64_DIV_S
        || opcode == OP_I64_DIV_U
        || opcode == OP_I64_REM_S
        || opcode == OP_I64_REM_U
        || opcode == OP_I64_AND
        || opcode == OP_I64_OR
        || opcode == OP_I64_XOR
        || opcode == OP_I64_SHL
        || opcode == OP_I64_SHR_S
        || opcode == OP_I64_SHR_U
        || opcode == OP_I64_ROTL
        || opcode == OP_I64_ROTR
    {
        return Some((ValueType::I64, ValueType::I64));
    }
    if opcode == OP_F32_ADD
        || opcode == OP_F32_SUB
        || opcode == OP_F32_MUL
        || opcode == OP_F32_DIV
        || opcode == OP_F32_MIN
        || opcode == OP_F32_MAX
        || opcode == OP_F32_COPYSIGN
    {
        return Some((ValueType::F32, ValueType::F32));
    }
    if opcode == OP_F64_ADD
        || opcode == OP_F64_SUB
        || opcode == OP_F64_MUL
        || opcode == OP_F64_DIV
        || opcode == OP_F64_MIN
        || opcode == OP_F64_MAX
        || opcode == OP_F64_COPYSIGN
    {
        return Some((ValueType::F64, ValueType::F64));
    }
    None
}

// --- Dispatch ---

/// Dispatch one operator: its reader, then the consumer's hook for it.
///
/// The hook runs after the reader, so it sees the immediates the reader
/// decoded, the checks it made, and the state its effect left behind. A hook
/// that declines stops the loop, reported as `OpError::Visitor`.
fn step<V: OpVisitor>(
    st: &mut OpIterState,
    data: &[u8],
    env: &Env,
    ctx: &Context,
    opcode: u8,
    v: &mut V,
) -> Result<()> {
    if opcode == OP_NOP {
        visit(v.on_nop(st))?;
        return Ok(());
    }
    if opcode == OP_UNREACHABLE {
        read_unreachable(st)?;
        visit(v.on_unreachable(st))?;
        return Ok(());
    }
    if opcode == OP_I32_CONST {
        let imm = read_i32_const(st, data)?;
        visit(v.on_i32_const(st, imm))?;
        return Ok(());
    }
    if opcode == OP_I64_CONST {
        let imm = read_i64_const(st, data)?;
        visit(v.on_i64_const(st, imm))?;
        return Ok(());
    }
    if opcode == OP_F32_CONST {
        let bits = read_f32_const(st, data)?;
        visit(v.on_f32_const(st, bits))?;
        return Ok(());
    }
    if opcode == OP_F64_CONST {
        let bits = read_f64_const(st, data)?;
        visit(v.on_f64_const(st, bits))?;
        return Ok(());
    }
    if opcode == OP_DROP {
        let ty = read_drop(st)?;
        visit(v.on_drop(st, ty))?;
        return Ok(());
    }
    if opcode == OP_SELECT {
        let ty = read_select(st)?;
        visit(v.on_select(st, ty))?;
        return Ok(());
    }
    if opcode == OP_BLOCK {
        let bt = read_block(st, data)?;
        visit(v.on_block(st, bt))?;
        return Ok(());
    }
    if opcode == OP_LOOP {
        let bt = read_loop(st, data)?;
        visit(v.on_loop(st, bt))?;
        return Ok(());
    }
    if opcode == OP_IF {
        let bt = read_if(st, data)?;
        visit(v.on_if(st, bt))?;
        return Ok(());
    }
    if opcode == OP_ELSE {
        let bt = read_else(st)?;
        visit(v.on_else(st, bt))?;
        return Ok(());
    }
    if opcode == OP_END {
        let (kind, bt) = read_end(st)?;
        visit(v.on_end(st, kind, bt))?;
        return Ok(());
    }
    if opcode == OP_BR {
        let (depth, bt) = read_br(st, data)?;
        visit(v.on_br(st, depth, bt))?;
        return Ok(());
    }
    if opcode == OP_BR_IF {
        let (depth, bt) = read_br_if(st, data)?;
        visit(v.on_br_if(st, depth, bt))?;
        return Ok(());
    }
    if opcode == OP_BR_TABLE {
        let (default, common) = read_br_table(st, data, v)?;
        visit(v.on_br_table(st, default, common))?;
        return Ok(());
    }
    if opcode == OP_RETURN {
        read_return(st, ctx)?;
        visit(v.on_return(st))?;
        return Ok(());
    }
    if opcode == OP_CALL {
        let idx = read_call(st, data, env)?;
        visit(v.on_call(st, idx))?;
        return Ok(());
    }
    if opcode == OP_CALL_INDIRECT {
        let idx = read_call_indirect(st, data, env)?;
        visit(v.on_call_indirect(st, idx))?;
        return Ok(());
    }
    if opcode == OP_LOCAL_GET {
        let idx = read_local_get(st, data, ctx)?;
        visit(v.on_local_get(st, idx))?;
        return Ok(());
    }
    if opcode == OP_LOCAL_SET {
        let idx = read_local_set(st, data, ctx)?;
        visit(v.on_local_set(st, idx))?;
        return Ok(());
    }
    if opcode == OP_LOCAL_TEE {
        let idx = read_local_tee(st, data, ctx)?;
        visit(v.on_local_tee(st, idx))?;
        return Ok(());
    }
    if opcode == OP_GLOBAL_GET {
        let idx = read_global_get(st, data, env)?;
        visit(v.on_global_get(st, idx))?;
        return Ok(());
    }
    if opcode == OP_GLOBAL_SET {
        let idx = read_global_set(st, data, env)?;
        visit(v.on_global_set(st, idx))?;
        return Ok(());
    }
    step_memory(st, data, env, opcode, v)
}

fn step_memory<V: OpVisitor>(
    st: &mut OpIterState,
    data: &[u8],
    env: &Env,
    opcode: u8,
    v: &mut V,
) -> Result<()> {
    if opcode == OP_I32_LOAD {
        let memarg = read_load(st, data, env, ValueType::I32, 2)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I64_LOAD {
        let memarg = read_load(st, data, env, ValueType::I64, 3)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_F32_LOAD {
        let memarg = read_load(st, data, env, ValueType::F32, 2)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_F64_LOAD {
        let memarg = read_load(st, data, env, ValueType::F64, 3)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I32_LOAD8_S {
        let memarg = read_load(st, data, env, ValueType::I32, 0)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I32_LOAD8_U {
        let memarg = read_load(st, data, env, ValueType::I32, 0)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I32_LOAD16_S {
        let memarg = read_load(st, data, env, ValueType::I32, 1)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I32_LOAD16_U {
        let memarg = read_load(st, data, env, ValueType::I32, 1)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I64_LOAD8_S {
        let memarg = read_load(st, data, env, ValueType::I64, 0)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I64_LOAD8_U {
        let memarg = read_load(st, data, env, ValueType::I64, 0)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I64_LOAD16_S {
        let memarg = read_load(st, data, env, ValueType::I64, 1)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I64_LOAD16_U {
        let memarg = read_load(st, data, env, ValueType::I64, 1)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I64_LOAD32_S {
        let memarg = read_load(st, data, env, ValueType::I64, 2)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I64_LOAD32_U {
        let memarg = read_load(st, data, env, ValueType::I64, 2)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I32_STORE {
        let memarg = read_store(st, data, env, ValueType::I32, 2)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I64_STORE {
        let memarg = read_store(st, data, env, ValueType::I64, 3)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_F32_STORE {
        let memarg = read_store(st, data, env, ValueType::F32, 2)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_F64_STORE {
        let memarg = read_store(st, data, env, ValueType::F64, 3)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I32_STORE8 {
        let memarg = read_store(st, data, env, ValueType::I32, 0)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I32_STORE16 {
        let memarg = read_store(st, data, env, ValueType::I32, 1)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I64_STORE8 {
        let memarg = read_store(st, data, env, ValueType::I64, 0)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I64_STORE16 {
        let memarg = read_store(st, data, env, ValueType::I64, 1)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_I64_STORE32 {
        let memarg = read_store(st, data, env, ValueType::I64, 2)?;
        visit(visit_memory(v, st, opcode, memarg))?;
        return Ok(());
    }
    if opcode == OP_MEMORY_SIZE {
        read_memory_size(st, data, env)?;
        visit(v.on_memory_size(st))?;
        return Ok(());
    }
    if opcode == OP_MEMORY_GROW {
        read_memory_grow(st, data, env)?;
        visit(v.on_memory_grow(st))?;
        return Ok(());
    }
    step_numeric(st, opcode, v)
}

/// The numeric operators, dispatched through the opcode table rather than
/// through a branch each. `visit_numeric` is the one place that turns an opcode
/// into a hook, so it is where a wrong row would show up.
fn step_numeric<V: OpVisitor>(
    st: &mut OpIterState,
    opcode: u8,
    v: &mut V,
) -> Result<()> {
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

/// Validate one function body, pushing each operator to `v` as it is accepted.
///
/// Terminates because `read_op` advances `pos` by at least one byte per
/// iteration and `pos` is bounded by `data.len()`, provided the hooks
/// themselves return.
///
/// # Preconditions
///
/// This is the raw entry point below the code section's framing.
/// [`module::validate_code_entry_with`] establishes all of these from a
/// position and an index, and is what a consumer should call instead.
///
/// - `data` is *exactly* the body's bytes: locals declarations already
///   stripped, and nothing after the terminating `end`. This function is
///   what decides the last byte is that `end`, so a slice that's one byte
///   too long or short is validating a different body.
/// - `ctx.locals` is the function's parameters followed by its declared
///   locals, in that order.
/// - `ctx.results` is the function's declared result types, at most one of
///   them (Wasm 1.0 has no multi-value).
/// - `env` is the decoded environment of the module this body belongs to.
///
/// [`module::validate_code_entry_with`]: crate::module::validate_code_entry_with
pub fn validate_body_with<V: OpVisitor>(
    data: &[u8],
    env: &Env,
    ctx: &Context,
    v: &mut V,
) -> Result<()> {
    if data.len() > MAX_FUNCTION_BYTES {
        return Err(OpError::BodyTooLarge);
    }
    let mut st = start_function(&ctx.results);
    loop {
        if control_stack_empty(&st) {
            // The body's `end` closed the outermost frame. Nothing may follow.
            if st.pos == data.len() {
                return Ok(());
            }
            return Err(OpError::TrailingBytes);
        }
        let opcode = read_op(&mut st, data)?;
        step(&mut st, data, env, ctx, opcode, v)?;
    }
}

/// Validate one function body and nothing else. [`validate_body_with`] with
/// a visitor that does nothing, and the same four preconditions.
pub fn validate_body(data: &[u8], env: &Env, ctx: &Context) -> Result<()> {
    let mut nop = EmptyOpVisitor;
    validate_body_with(data, env, ctx, &mut nop)
}

/// What a hook returns. `Ok` is "carry on", and it is the only answer that
/// lets validation finish.
pub type VisitResult = core::result::Result<(), VisitError>;

/// The numeric operators: 123 rows, no immediates. One table, used twice.
///
/// `#[macro_export]`ed so a consumer building a C ABI on top of this crate
/// -- SpiderMonkey's `veriwasm_glue` is one -- can build its vtable from
/// this table rather than transcribing it by hand. This is the only place
/// the opcode-to-hook mapping lives; a hand-transcribed second copy could
/// drift out of sync with it.
#[macro_export]
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

/// The memory operators: 23 rows, each with a `memarg`. `#[macro_export]`ed
/// for the same reason `numeric_table!` is.
#[macro_export]
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

/// Hooks, one per opcode, fired once the operator has been decoded and
/// validated. `st` is the state after the operator's effect, so its stacks,
/// its cursor and the innermost frame's `polymorphic_base` are what a consumer
/// reads to know the operand types and whether the code is reachable.
///
/// # What an implementation owes
///
/// A hook must always return -- no panicking, no looping forever -- or
/// nothing says the validator terminates either. And every hook must return
/// `Ok` for a well-typed body to be accepted: returning `Err` rejects the
/// body (reported as `OpError::Visitor`, not a validity verdict).
///
/// Whether a body is well-typed is decided independently of the hooks, so a
/// hostile implementation can refuse a valid body or fail to terminate, but
/// it can never make an invalid body pass.
///
/// `st` is a shared borrow, so no hook can move the cursor or either stack.
pub trait OpVisitor {
    // --- The function around the operators ---

    /// One code-section entry is about to be validated, with the locals and
    /// results the module declared for it and its type index. A consumer needs
    /// this to size a frame, and `validate_code_entry_with` is what decodes it,
    /// so nothing has to decode the locals twice.
    ///
    /// `_body_begin` and `_body_end` bracket the operators within the module's
    /// own bytes: the first is just past the locals declaration, the second is
    /// the entry's end. A consumer that records a byte offset per operator
    /// needs the first to make those offsets module-wide, and it cannot work it
    /// out for itself, because the locals arrive here flattened and their
    /// encoded length is not recoverable from them.
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

    fn on_block(&mut self, _st: &OpIterState, _bt: BlockType) -> VisitResult {
        Ok(())
    }

    fn on_loop(&mut self, _st: &OpIterState, _bt: BlockType) -> VisitResult {
        Ok(())
    }

    fn on_if(&mut self, _st: &OpIterState, _bt: BlockType) -> VisitResult {
        Ok(())
    }

    /// `_bt` is the block type of the `if` this switches sides on.
    fn on_else(&mut self, _st: &OpIterState, _bt: BlockType) -> VisitResult {
        Ok(())
    }

    /// `_kind` says what closed: the body, a block, a loop, or one side of an
    /// `if`. A bare `if` closes as `Then`, so a consumer that needs the elided
    /// empty `else` knows to supply it.
    fn on_end(
        &mut self,
        _st: &OpIterState,
        _kind: LabelKind,
        _bt: BlockType,
    ) -> VisitResult {
        Ok(())
    }

    /// `_bt` is the target frame's block type: what the branch must supply.
    fn on_br(&mut self, _st: &OpIterState, _depth: u32, _bt: BlockType) -> VisitResult {
        Ok(())
    }

    fn on_br_if(&mut self, _st: &OpIterState, _depth: u32, _bt: BlockType) -> VisitResult {
        Ok(())
    }

    /// One entry of a `br_table`'s label vector, in the order they are
    /// encoded. The vector is not collected first: it has no bound but the byte
    /// count, so collecting it would put `Vec::push` back on the live panic
    /// list. `on_br_table` closes the operator once they have all gone by.
    fn on_br_table_label(&mut self, _st: &OpIterState, _depth: u32) -> VisitResult {
        Ok(())
    }

    /// The end of a `br_table`: its default label, and the target type every
    /// label in it agrees on.
    fn on_br_table(
        &mut self,
        _st: &OpIterState,
        _default: u32,
        _common: BlockType,
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

    /// `_ty` is what came off the stack: `Bot` in unreachable code.
    fn on_drop(&mut self, _st: &OpIterState, _ty: StackType) -> VisitResult {
        Ok(())
    }

    /// `_ty` is the common type of the two operands, which is also what was
    /// pushed.
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

    /// The immediate's bits, not a float: a consumer that wants the value
    /// converts it with `f32::from_bits`.
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

/// The validating-only consumer: every hook is the default. `validate_body` is
/// `validate_body_with` at this instance, which is why the two agree.
pub struct EmptyOpVisitor;

impl OpVisitor for EmptyOpVisitor {}

macro_rules! numeric_fanout {
    ($($op:ident => $hook:ident;)*) => {
        /// Generated from `numeric_table!`: hand a validated numeric operator
        /// to its hook. It cannot touch the validator state, having only a
        /// shared borrow of it, and it is the only place the opcode-to-hook
        /// mapping lives.
        pub(crate) fn visit_numeric<V: OpVisitor>(
            v: &mut V,
            st: &OpIterState,
            opcode: u8,
        ) -> VisitResult {
            $(if opcode == $op {
                return v.$hook(st);
            })*
            Ok(())
        }
    };
}

macro_rules! memory_fanout {
    ($($op:ident => $hook:ident;)*) => {
        /// Generated from `memory_table!`, as `visit_numeric` is.
        pub(crate) fn visit_memory<V: OpVisitor>(
            v: &mut V,
            st: &OpIterState,
            opcode: u8,
            memarg: MemArg,
        ) -> VisitResult {
            $(if opcode == $op {
                return v.$hook(st, memarg);
            })*
            Ok(())
        }
    };
}

numeric_table!(numeric_fanout);
memory_table!(memory_fanout);

// Public so a consumer building a C ABI on top of this crate -- SpiderMonkey's
// veriwasm_glue, for instance -- can build its vtable from these two tables
// rather than transcribing them. They are the only place the opcode-to-hook
// mapping lives and `OpIter_Table.v` proves their rows are not off by one, so
// a second copy would be a copy that proof does not cover.
//
// Declared here at the bottom, rather than next to the tables, so that adding
// it moved no line above it: the extraction records a source line per
// definition, and `theories/Itasca_Funs.v` is generated and committed.
pub use {memory_table, numeric_table};

// Declared here at the bottom so that adding them moved no line above: the
// extraction records a source line per definition and `Itasca_Funs.v` is
// generated and committed.
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_table_covers_every_numeric_opcode_in_its_ranges() {
        // 0x45, 0x50, 0x67-0x69, 0x79-0x7b, 0x8b-0x91, 0x99-0x9f, 0xa7-0xbf.
        let mut covered = 0;
        for op in 0u8..=0xffu8 {
            if convert_types(op).is_some() {
                covered += 1;
            }
        }
        assert_eq!(covered, 47);
    }

    #[test]
    fn the_table_has_no_row_outside_the_numeric_block() {
        for op in 0u8..=0xffu8 {
            let in_range = op == 0x45
                || op == 0x50
                || (0x67..=0x69).contains(&op)
                || (0x79..=0x7b).contains(&op)
                || (0x8b..=0x91).contains(&op)
                || (0x99..=0x9f).contains(&op)
                || (0xa7..=0xbf).contains(&op);
            assert_eq!(convert_types(op).is_some(), in_range, "opcode {op:#x}");
        }
    }

    #[test]
    fn the_binary_table_covers_its_ranges_exactly() {
        // 0x46-0x4f, 0x51-0x5a, 0x5b-0x60, 0x61-0x66 comparisons;
        // 0x6a-0x78, 0x7c-0x8a, 0x92-0x98, 0xa0-0xa6 binary.
        for op in 0u8..=0xffu8 {
            let in_range = (0x46..=0x4f).contains(&op)
                || (0x51..=0x66).contains(&op)
                || (0x6a..=0x78).contains(&op)
                || (0x7c..=0x8a).contains(&op)
                || (0x92..=0x98).contains(&op)
                || (0xa0..=0xa6).contains(&op);
            assert_eq!(binary_types(op).is_some(), in_range, "opcode {op:#x}");
        }
    }

    #[test]
    fn the_two_tables_do_not_overlap() {
        for op in 0u8..=0xffu8 {
            assert!(
                !(convert_types(op).is_some() && binary_types(op).is_some()),
                "opcode {op:#x} is in both tables"
            );
        }
    }

    #[test]
    fn every_opcode_from_0x45_to_0xbf_is_in_one_of_the_tables() {
        for op in 0x45u8..=0xbfu8 {
            assert!(
                convert_types(op).is_some() || binary_types(op).is_some(),
                "opcode {op:#x} is in neither table"
            );
        }
    }

    // MAX_FUNCTION_BYTES is private, so these live here rather than in
    // tests/code_tests.rs.
    #[test]
    fn a_body_at_the_size_limit_is_still_validated() {
        // MAX_FUNCTION_BYTES nops followed by the closing end would be one
        // byte over, so stop one short. This is the largest body the
        // validator accepts, and it must be accepted on its merits rather
        // than rejected for size.
        let mut body = vec![OP_NOP; MAX_FUNCTION_BYTES - 1];
        body.push(OP_END);
        assert_eq!(body.len(), MAX_FUNCTION_BYTES);
        let ctx = Context {
            locals: Vec::new(),
            results: Vec::new(),
        };
        assert!(validate_body(&body, &Env::new(), &ctx).is_ok());
    }

    #[test]
    fn a_body_over_the_size_limit_is_rejected_for_size() {
        let mut body = vec![OP_NOP; MAX_FUNCTION_BYTES];
        body.push(OP_END);
        let ctx = Context {
            locals: Vec::new(),
            results: Vec::new(),
        };
        assert!(matches!(
            validate_body(&body, &Env::new(), &ctx),
            Err(OpError::BodyTooLarge)
        ));
    }

    #[test]
    fn the_size_limit_is_checked_before_anything_else() {
        // An oversized body that is also ill-typed is rejected for size, so
        // the check cannot be reached only on otherwise-valid input.
        let body = vec![OP_I32_ADD; MAX_FUNCTION_BYTES + 1];
        let ctx = Context {
            locals: Vec::new(),
            results: Vec::new(),
        };
        assert!(matches!(
            validate_body(&body, &Env::new(), &ctx),
            Err(OpError::BodyTooLarge)
        ));
    }
}
