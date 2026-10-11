//! Multi-value validation under development.
//!
//! This module is deliberately separate from the verified Wasm 1.0 entry
//! points while the control-flow proofs are generalized. It accepts scalar
//! Wasm 1.0 instructions plus multi-value function and block signatures, and
//! uses Wasm 2.0 branch-table typing. It does not enable the other 2.0 proposals.
//!
//! The operand stack and scalar readers are shared with `code`. The legacy
//! control slots supply only stack bases and reachability here; block signature
//! descriptors are stored alongside them, never expanded into temporary vectors.

use crate::code::{self, Context, EmptyOpVisitor, LabelKind, OpIterState, StackType};
use crate::error::OpError;
use crate::limits::MAX_FUNCTION_BYTES;
use crate::module::Env;
use crate::reader::{read_byte, read_u32_leb};
use crate::signature::{self, BlockType, ResultType, TypePart};
use crate::types::{FuncType, ValueType};
use alloc::vec::Vec;

type Result<T> = core::result::Result<T, OpError>;

/// JavaScript embedding / SpiderMonkey signature limits.
pub const MAX_PARAMS: usize = 1000;
pub const MAX_RESULTS: usize = 1000;

struct State {
    core: OpIterState,
    blocks: Vec<BlockType>,
}

fn check_func_type(ft: &FuncType) -> Result<()> {
    if ft.params.len() > MAX_PARAMS {
        return Err(OpError::TooManyParams);
    }
    if ft.results.len() > MAX_RESULTS {
        return Err(OpError::TooManyResults);
    }
    Ok(())
}

fn pop_results(st: &mut OpIterState, env: &Env, ts: ResultType) -> Result<()> {
    match ts {
        ResultType::Empty => Ok(()),
        ResultType::One(t) => {
            code::pop_with_type(st, t)?;
            Ok(())
        }
        ResultType::Type { index, part } => {
            let i = index as usize;
            if i >= env.types.len() {
                return Err(OpError::UnknownType);
            }
            match part {
                TypePart::Params => code::pop_types(st, &env.types[i].params),
                TypePart::Results => code::pop_types(st, &env.types[i].results),
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
                TypePart::Params => code::push_types(st, &env.types[i].params),
                TypePart::Results => code::push_types(st, &env.types[i].results),
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

fn push_frame(st: &mut State, kind: LabelKind, bt: BlockType) {
    code::push_ctrl(&mut st.core, kind, code::BlockType::Empty);
    st.blocks.push(bt);
}

fn enter(st: &mut State, data: &[u8], env: &Env, kind: LabelKind) -> Result<()> {
    let (bt, end) = signature::read_block_type(data, st.core.pos)?;
    st.core.pos = end;
    if let BlockType::TypeIndex(index) = bt {
        let i = index as usize;
        if i >= env.types.len() {
            return Err(OpError::UnknownType);
        }
        check_func_type(&env.types[i])?;
    }
    if let LabelKind::Then = kind {
        code::pop_with_type(&mut st.core, ValueType::I32)?;
    }
    pop_results(&mut st.core, env, bt.params())?;
    // The base excludes the inputs; both arms start with their declared inputs.
    push_frame(st, kind, bt);
    push_results(&mut st.core, env, bt.params())
}

fn end_frame(st: &mut State, env: &Env, is_else: bool) -> Result<()> {
    let n = st.blocks.len();
    if n == 0 {
        return Err(OpError::UnknownLabel);
    }
    let bt = st.blocks[n - 1];
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
        push_results(&mut st.core, env, bt.params())
    } else {
        let _ = st.core.ctrls.pop();
        let _ = st.blocks.pop();
        if n == 1 {
            // There is no enclosing operand stack at function end.
            Ok(())
        } else {
            push_results(&mut st.core, env, bt.results())
        }
    }
}

fn label(st: &State, depth: u32) -> Result<ResultType> {
    let n = st.blocks.len();
    let d = depth as usize;
    if d >= n {
        return Err(OpError::UnknownLabel);
    }
    let i = n - 1 - d;
    match st.core.ctrls[i].kind {
        LabelKind::Loop => Ok(st.blocks[i].params()),
        _ => Ok(st.blocks[i].results()),
    }
}

fn read_label(st: &mut State, data: &[u8]) -> Result<ResultType> {
    let (depth, end) = read_u32_leb(data, st.core.pos)?;
    st.core.pos = end;
    label(st, depth)
}

fn branch(st: &mut State, data: &[u8], env: &Env, conditional: bool) -> Result<()> {
    let ts = read_label(st, data)?;
    if conditional {
        code::pop_with_type(&mut st.core, ValueType::I32)?;
    }
    pop_results(&mut st.core, env, ts)?;
    if conditional {
        push_results(&mut st.core, env, ts)
    } else {
        code::mark_unreachable(&mut st.core);
        Ok(())
    }
}

/// Check the same unchanged operand suffix against every branch-table target.
/// In particular, do not replace Bot by one target's concrete type before
/// checking a different target (Wasm 2.0 permits a common bottom subtype).
fn check_suffix(st: &OpIterState, env: &Env, ts: ResultType) -> Result<()> {
    let base = code::cur_base(st);
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
            if !code::cur_polymorphic(st) {
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

fn branch_table(st: &mut State, data: &[u8], env: &Env) -> Result<()> {
    let (count, end) = read_u32_leb(data, st.core.pos)?;
    st.core.pos = end;
    code::pop_with_type(&mut st.core, ValueType::I32)?;
    let mut arity = None;
    let mut i = 0;
    loop {
        let ts = read_label(st, data)?;
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
            code::mark_unreachable(&mut st.core);
            return Ok(());
        }
        i += 1;
    }
}

fn apply_func_type(st: &mut OpIterState, ft: &FuncType) -> Result<()> {
    check_func_type(ft)?;
    code::pop_types(st, &ft.params)?;
    if ft.results.len() > usize::MAX - st.vals.len() {
        return Err(OpError::StackTooLarge);
    }
    code::push_types(st, &ft.results);
    Ok(())
}

fn call(st: &mut State, data: &[u8], env: &Env, indirect: bool) -> Result<()> {
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
        code::pop_with_type(&mut st.core, ValueType::I32)?;
        apply_func_type(&mut st.core, &env.types[i])
    } else {
        if i >= env.func_types.len() {
            return Err(OpError::UnknownFunc);
        }
        apply_func_type(&mut st.core, &env.func_types[i])
    }
}

/// Validate a body using an existing type-section entry for its signature.
/// `locals` contains parameters followed by declared locals. Function parameters
/// are locals, and do not appear on the initial operand stack.
///
/// The implementation is extracted, but whole-body multi-value soundness and
/// completeness are not yet proved. Use `code::validate_body` for the verified
/// Wasm 1.0 API. Other Wasm 2.0 proposals remain disabled here.
pub fn validate_body(
    data: &[u8],
    env: &Env,
    locals: Vec<ValueType>,
    type_index: u32,
) -> Result<()> {
    if data.len() > MAX_FUNCTION_BYTES {
        return Err(OpError::BodyTooLarge);
    }
    let i = type_index as usize;
    if i >= env.types.len() {
        return Err(OpError::UnknownType);
    }
    check_func_type(&env.types[i])?;
    let mut st = State {
        core: OpIterState {
            vals: Vec::new(),
            ctrls: Vec::new(),
            pos: 0,
        },
        blocks: Vec::new(),
    };
    push_frame(&mut st, LabelKind::Body, BlockType::TypeIndex(type_index));
    let ctx = Context {
        locals,
        results: Vec::new(),
    };
    let mut visitor = EmptyOpVisitor;
    loop {
        if st.blocks.is_empty() {
            if st.core.pos != data.len() {
                return Err(OpError::TrailingBytes);
            }
            return Ok(());
        }
        let (op, end) = read_byte(data, st.core.pos)?;
        st.core.pos = end;
        match op {
            code::OP_BLOCK => enter(&mut st, data, env, LabelKind::Block)?,
            code::OP_LOOP => enter(&mut st, data, env, LabelKind::Loop)?,
            code::OP_IF => enter(&mut st, data, env, LabelKind::Then)?,
            code::OP_ELSE => end_frame(&mut st, env, true)?,
            code::OP_END => end_frame(&mut st, env, false)?,
            code::OP_BR => branch(&mut st, data, env, false)?,
            code::OP_BR_IF => branch(&mut st, data, env, true)?,
            code::OP_BR_TABLE => branch_table(&mut st, data, env)?,
            code::OP_RETURN => {
                pop_results(
                    &mut st.core,
                    env,
                    ResultType::Type {
                        index: type_index,
                        part: TypePart::Results,
                    },
                )?;
                code::mark_unreachable(&mut st.core);
            }
            code::OP_CALL => call(&mut st, data, env, false)?,
            code::OP_CALL_INDIRECT => call(&mut st, data, env, true)?,
            _ => {
                // Every scalar instruction pushes at most one value.
                if st.core.vals.len() == usize::MAX {
                    return Err(OpError::StackTooLarge);
                }
                code::step(&mut st.core, data, env, &ctx, op, &mut visitor)?;
            }
        }
    }
}

fn decode_types(
    data: &[u8],
    pos: usize,
    limit: usize,
    error: OpError,
) -> core::result::Result<(Vec<ValueType>, usize), crate::Error> {
    let (count, mut pos) = read_u32_leb(data, pos)?;
    // Reject the encoded count before allocating or reading element payloads.
    if count as usize > limit {
        return Err(crate::Error::Read(error));
    }
    let mut out = Vec::new();
    let mut i = 0;
    while i < count {
        let (ty, end) = crate::module::decode_value_type(data, pos)?;
        out.push(ty);
        pos = end;
        i += 1;
    }
    Ok((out, pos))
}

fn decode_type_section(
    data: &[u8],
    pos: usize,
    env: &mut Env,
) -> core::result::Result<usize, crate::Error> {
    let (count, mut pos) = read_u32_leb(data, pos)?;
    let mut i = 0;
    while i < count {
        let (tag, p) = read_byte(data, pos)?;
        if tag != 0x60 {
            return Err(crate::Error::InvalidType(tag));
        }
        let (params, p) = decode_types(data, p, MAX_PARAMS, OpError::TooManyParams)?;
        let (results, p) = decode_types(data, p, MAX_RESULTS, OpError::TooManyResults)?;
        env.types.push(FuncType { params, results });
        pos = p;
        i += 1;
    }
    Ok(pos)
}

fn decode_environment(data: &[u8]) -> core::result::Result<(Env, usize), crate::Error> {
    let mut env = Env::new();
    let mut pos = crate::module::read_header(data)?;
    let mut last_id = 0;
    loop {
        if pos >= data.len() {
            return Ok((env, pos));
        }
        let (id, start, end) = crate::module::read_section_header(data, pos)?;
        if id == 0 {
            crate::module::decode_custom_section(data, start, end)?;
        } else if id >= crate::module::SECTION_CODE {
            return Ok((env, pos));
        } else {
            if id <= last_id {
                return Err(crate::Error::SectionOutOfOrder);
            }
            last_id = id;
            let actual = if id == 1 {
                decode_type_section(data, start, &mut env)?
            } else if id == 9 {
                decode_elements(data, start, &mut env)?
            } else {
                crate::module::decode_env_section(data, start, id, &mut env)?
            };
            if actual != end {
                return Err(crate::Error::SectionSizeMismatch);
            }
        }
        pos = end;
    }
}

fn validate_entry(
    data: &[u8],
    pos: usize,
    env: &Env,
    index: usize,
) -> core::result::Result<usize, crate::Error> {
    if index >= env.func_type_indices.len() {
        return Err(crate::Error::FuncCodeMismatch);
    }
    let (size, p) = read_u32_leb(data, pos)?;
    crate::module::have_bytes(data, p, size as usize)?;
    let end = p + size as usize;
    let (declared, start) = crate::module::decode_locals(data, p)?;
    if start > end {
        return Err(crate::Error::SectionSizeMismatch);
    }
    let type_index = env.func_type_indices[index];
    let i = type_index as usize;
    if i >= env.types.len() {
        return Err(crate::Error::UnknownType(type_index));
    }
    let locals = crate::module::build_func_locals(&env.types[i].params, &declared);
    match validate_body(&data[start..end], env, locals, type_index) {
        Ok(()) => Ok(end),
        Err(e) => Err(crate::Error::Body(e)),
    }
}

/// Validate a contiguous module with multi-value enabled. This experimental
/// entry point shares the scalar readers and section validators with the
/// Wasm 1.0 implementation, but does not yet have its whole-module proofs,
/// visitor API, or parallel streaming integration.
pub fn validate_module(data: &[u8]) -> core::result::Result<crate::Module, crate::Error> {
    if data.len() > crate::limits::MAX_MODULE_BYTES {
        return Err(crate::Error::ModuleTooLarge);
    }
    let (env, mut pos) = decode_environment(data)?;
    pos = validate_code(data, pos, &env)?;
    let tail = validate_tail(data, pos, &env)?;
    Ok(crate::Module { env, tail })
}

fn validate_code(data: &[u8], pos: usize, env: &Env) -> core::result::Result<usize, crate::Error> {
    if pos < data.len() && data[pos] == crate::module::SECTION_CODE {
        let (_, start, end) = crate::module::read_section_header(data, pos)?;
        let (count, entry) = read_u32_leb(data, start)?;
        if count as usize != env.func_type_indices.len() {
            return Err(crate::Error::FuncCodeMismatch);
        }
        return validate_entries(data, entry, end, count, env);
    } else if !env.func_type_indices.is_empty() {
        return Err(crate::Error::MissingCodeSection);
    }
    Ok(pos)
}

fn validate_entries(
    data: &[u8],
    mut entry: usize,
    end: usize,
    count: u32,
    env: &Env,
) -> core::result::Result<usize, crate::Error> {
    let mut i = 0;
    loop {
        if i >= count as usize {
            if entry != end {
                return Err(crate::Error::SectionSizeMismatch);
            }
            return Ok(end);
        }
        entry = validate_entry(data, entry, env, i)?;
        if entry > end {
            return Err(crate::Error::SectionSizeMismatch);
        }
        i += 1;
    }
}

// Core 2's active segment encodings, including explicit index zero. Passive
// and declarative segments belong to bulk memory/reference types and stay off.
fn active_index(data: &[u8], pos: usize) -> core::result::Result<(u32, usize, bool), crate::Error> {
    let (flags, pos) = read_u32_leb(data, pos)?;
    match flags {
        0 => Ok((0, pos, false)),
        2 => {
            let (index, pos) = read_u32_leb(data, pos)?;
            Ok((index, pos, true))
        }
        _ => Err(crate::Error::InvalidType(0xff)),
    }
}

fn decode_elements(
    data: &[u8],
    pos: usize,
    env: &mut Env,
) -> core::result::Result<usize, crate::Error> {
    let (count, mut pos) = read_u32_leb(data, pos)?;
    let mut i = 0;
    loop {
        if i >= count {
            return Ok(pos);
        }
        let (table_idx, p, explicit) = active_index(data, pos)?;
        if table_idx as usize >= env.table_types.len() {
            return Err(crate::Error::UnknownTable(table_idx));
        }
        let (offset, mut p) = crate::module::decode_const_expr(data, p, env, ValueType::I32)?;
        if explicit {
            let (kind, end) = read_byte(data, p)?;
            if kind != 0 {
                return Err(crate::Error::InvalidType(kind));
            }
            p = end;
        }
        let (init, end) = crate::module::decode_func_indices(data, p, env)?;
        env.elements.push(crate::module::Element {
            table_idx,
            offset,
            init,
        });
        pos = end;
        i += 1;
    }
}

fn decode_data(
    data: &[u8],
    pos: usize,
    env: &Env,
) -> core::result::Result<(Vec<crate::module::Data>, usize), crate::Error> {
    let (count, mut pos) = read_u32_leb(data, pos)?;
    let mut segments = Vec::new();
    let mut i = 0;
    loop {
        if i >= count {
            return Ok((segments, pos));
        }
        let (memory_idx, p, _) = active_index(data, pos)?;
        if memory_idx as usize >= env.mem_types.len() {
            return Err(crate::Error::UnknownMemory(memory_idx));
        }
        let (offset, p) = crate::module::decode_const_expr(data, p, env, ValueType::I32)?;
        let (size, p) = read_u32_leb(data, p)?;
        crate::module::have_bytes(data, p, size as usize)?;
        let end = p + size as usize;
        let init = crate::module::copy_bytes(data, p, end);
        segments.push(crate::module::Data {
            memory_idx,
            offset,
            init,
        });
        pos = end;
        i += 1;
    }
}

fn validate_tail(
    data: &[u8],
    mut pos: usize,
    env: &Env,
) -> core::result::Result<crate::module::Tail, crate::Error> {
    let mut segments = Vec::new();
    let mut seen_data = false;
    loop {
        if pos >= data.len() {
            return Ok(crate::module::Tail { data: segments });
        }
        let (id, start, end) = crate::module::read_section_header(data, pos)?;
        if id == 0 {
            crate::module::decode_custom_section(data, start, end)?;
        } else if id != 11 || seen_data {
            return Err(crate::Error::SectionOutOfOrder);
        } else {
            seen_data = true;
            let (decoded, actual) = decode_data(data, start, env)?;
            if actual != end {
                return Err(crate::Error::SectionSizeMismatch);
            }
            segments = decoded;
        }
        pos = end;
    }
}
