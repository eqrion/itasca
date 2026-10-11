//! Shared body worker and multi-value control rules.
//!
//! Both profiles use one initialization path, one instruction loop, and the
//! same operand and control stacks. Wasm 1.0 keeps its existing control rules;
//! multi-value adds parameterized signatures and Wasm 2.0 branch-table typing.
//! Both profiles share scalar instructions and invoke hooks during validation.
//!
//! Each control frame stores its full signature descriptor without expanding
//! indexed signatures into temporary vectors. Other Wasm 2.0 proposals remain
//! disabled.

use crate::code::{self, Context, EmptyOpVisitor, LabelKind, OpIterState, OpVisitor, StackType};
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
    st.core.ctrls.push(code::Ctrl {
        kind,
        block_type: code::BlockType::Empty,
        signature: bt,
        value_stack_base: st.core.vals.len(),
        polymorphic_base: false,
    });
}

fn enter_info(st: &mut State, data: &[u8], env: &Env, kind: LabelKind) -> Result<BlockType> {
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
    push_results(&mut st.core, env, bt.params())?;
    Ok(bt)
}

// Stable no-op projection used by the extracted semantic contracts.
#[allow(dead_code)]
fn enter(st: &mut State, data: &[u8], env: &Env, kind: LabelKind) -> Result<()> {
    enter_info(st, data, env, kind)?;
    Ok(())
}

fn end_frame_info(st: &mut State, env: &Env, is_else: bool) -> Result<(LabelKind, BlockType)> {
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
fn end_frame(st: &mut State, env: &Env, is_else: bool) -> Result<()> {
    end_frame_info(st, env, is_else)?;
    Ok(())
}

fn label(st: &State, depth: u32) -> Result<ResultType> {
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

fn read_label_info(st: &mut State, data: &[u8]) -> Result<(u32, ResultType)> {
    let (depth, end) = read_u32_leb(data, st.core.pos)?;
    st.core.pos = end;
    let types = label(st, depth)?;
    Ok((depth, types))
}

// Stable no-op projection used by the extracted semantic contracts.
#[allow(dead_code)]
fn read_label(st: &mut State, data: &[u8]) -> Result<ResultType> {
    let (_, types) = read_label_info(st, data)?;
    Ok(types)
}

fn branch_info(
    st: &mut State,
    data: &[u8],
    env: &Env,
    conditional: bool,
) -> Result<(u32, ResultType)> {
    let (depth, ts) = read_label_info(st, data)?;
    if conditional {
        code::pop_with_type(&mut st.core, ValueType::I32)?;
    }
    pop_results(&mut st.core, env, ts)?;
    if conditional {
        push_results(&mut st.core, env, ts)?;
    } else {
        code::mark_unreachable(&mut st.core);
    }
    Ok((depth, ts))
}

// Stable no-op projection used by the extracted semantic contracts.
#[allow(dead_code)]
fn branch(st: &mut State, data: &[u8], env: &Env, conditional: bool) -> Result<()> {
    branch_info(st, data, env, conditional)?;
    Ok(())
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

fn branch_table_with<V: OpVisitor>(
    st: &mut State,
    data: &[u8],
    env: &Env,
    visitor: &mut V,
) -> Result<()> {
    let (count, end) = read_u32_leb(data, st.core.pos)?;
    st.core.pos = end;
    code::pop_with_type(&mut st.core, ValueType::I32)?;
    let mut arity = None;
    let mut i = 0;
    loop {
        let (depth, ts) = read_label_info(st, data)?;
        if i != count {
            code::visit(visitor.on_br_table_label(&st.core, depth))?;
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
            code::mark_unreachable(&mut st.core);
            code::visit(visitor.on_br_table(&st.core, depth, ts))?;
            return Ok(());
        }
        i += 1;
    }
}

// Stable no-op projection used by the extracted semantic contracts.
#[allow(dead_code)]
fn branch_table(st: &mut State, data: &[u8], env: &Env) -> Result<()> {
    let mut visitor = EmptyOpVisitor;
    branch_table_with(st, data, env, &mut visitor)
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

fn call_info(st: &mut State, data: &[u8], env: &Env, indirect: bool) -> Result<u32> {
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
fn call(st: &mut State, data: &[u8], env: &Env, indirect: bool) -> Result<()> {
    call_info(st, data, env, indirect)?;
    Ok(())
}

/// Initialize the shared state using the selected profile's function signature.
fn initial_state(
    env: &Env,
    ctx: &Context,
    type_index: u32,
    profile: crate::ValidationProfile,
) -> Result<State> {
    match profile {
        crate::ValidationProfile::Wasm1 => Ok(State {
            core: code::start_function(&ctx.results),
        }),
        crate::ValidationProfile::MultiValue => {
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
            };
            push_frame(&mut st, LabelKind::Body, BlockType::TypeIndex(type_index));
            Ok(st)
        }
    }
}

/// The sole body loop; profile-specific control rules are selected per step.
fn body_loop<V: OpVisitor>(
    data: &[u8],
    env: &Env,
    ctx: &Context,
    type_index: u32,
    profile: crate::ValidationProfile,
    visitor: &mut V,
    mut st: State,
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

/// Select the control rules while retaining the shared scalar dispatcher.
fn step_profile<V: OpVisitor>(
    st: &mut State,
    data: &[u8],
    env: &Env,
    ctx: &Context,
    type_index: u32,
    profile: crate::ValidationProfile,
    op: u8,
    visitor: &mut V,
) -> Result<()> {
    match profile {
        crate::ValidationProfile::Wasm1 => code::step(&mut st.core, data, env, ctx, op, visitor),
        crate::ValidationProfile::MultiValue => {
            match op {
                code::OP_BLOCK => {
                    let bt = enter_info(st, data, env, LabelKind::Block)?;
                    code::visit(visitor.on_block(&st.core, bt))?;
                }
                code::OP_LOOP => {
                    let bt = enter_info(st, data, env, LabelKind::Loop)?;
                    code::visit(visitor.on_loop(&st.core, bt))?;
                }
                code::OP_IF => {
                    let bt = enter_info(st, data, env, LabelKind::Then)?;
                    code::visit(visitor.on_if(&st.core, bt))?;
                }
                code::OP_ELSE => {
                    let (_, bt) = end_frame_info(st, env, true)?;
                    code::visit(visitor.on_else(&st.core, bt))?;
                }
                code::OP_END => {
                    let (kind, bt) = end_frame_info(st, env, false)?;
                    code::visit(visitor.on_end(&st.core, kind, bt))?;
                }
                code::OP_BR => {
                    let (depth, ts) = branch_info(st, data, env, false)?;
                    code::visit(visitor.on_br(&st.core, depth, ts))?;
                }
                code::OP_BR_IF => {
                    let (depth, ts) = branch_info(st, data, env, true)?;
                    code::visit(visitor.on_br_if(&st.core, depth, ts))?;
                }
                code::OP_BR_TABLE => branch_table_with(st, data, env, visitor)?,
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
                    code::visit(visitor.on_return(&st.core))?;
                }
                code::OP_CALL => {
                    let idx = call_info(st, data, env, false)?;
                    code::visit(visitor.on_call(&st.core, idx))?;
                }
                code::OP_CALL_INDIRECT => {
                    let idx = call_info(st, data, env, true)?;
                    code::visit(visitor.on_call_indirect(&st.core, idx))?;
                }
                _ => {
                    // Every scalar instruction pushes at most one value.
                    if st.core.vals.len() == usize::MAX {
                        return Err(OpError::StackTooLarge);
                    }
                    code::step(&mut st.core, data, env, ctx, op, visitor)?;
                }
            }
            Ok(())
        }
    }
}

/// Validate a body in either supported profile through the same worker.
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

/// Validate a multi-value body through the shared worker.
/// `ctx.locals` contains parameters followed by declared locals; `type_index`
/// selects function results. Parameters do not enter the operand stack.
/// The enclosing module entry emits `on_function_start` before this function.
/// Hooks receive the encoded block and label descriptors. `Ctrl.signature`
/// records each enclosing signature; `Ctrl.block_type` is a compatibility
/// field for Wasm 1.0 and remains empty in this profile.
pub fn validate_body_with<V: OpVisitor>(
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

/// Validate a body using the same visiting worker with no-op hooks.
pub fn validate_body(
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
    validate_body_with(data, env, &ctx, type_index, &mut visitor)
}
