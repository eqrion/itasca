//! Tests for the streaming decode+validate function-body validator.

use veriwasm::env::*;
use veriwasm::error::OpError;
use veriwasm::limits::*;
use veriwasm::opiter::*;
use veriwasm::types::*;

fn empty_env() -> Env {
    Env::new()
}

fn env_with_memory() -> Env {
    let mut env = empty_env();
    env.mem_types.push(MemType {
        limits: Limits { min: 1, max: None },
    });
    env
}

fn env_with_globals(globals: &[GlobalType]) -> Env {
    let mut env = env_with_memory();
    env.global_types.extend_from_slice(globals);
    env.num_imported_globals = globals.len();
    env
}

/// The per-function half of the context. `results` is both what the outermost
/// frame has to be left holding and what `return` branches to: one list.
fn ctx(locals: &[ValueType], results: &[ValueType]) -> Context {
    Context {
        locals: locals.to_vec(),
        results: results.to_vec(),
    }
}

fn accepts_locals(body: &[u8], locals: &[ValueType], results: &[ValueType]) -> bool {
    validate_body(body, &env_with_memory(), &ctx(locals, results)).is_ok()
}

fn accepts_globals(body: &[u8], globals: &[GlobalType], results: &[ValueType]) -> bool {
    validate_body(body, &env_with_globals(globals), &ctx(&[], results)).is_ok()
}

fn global(mutability: Mut, valtype: ValueType) -> GlobalType {
    GlobalType {
        mutability,
        valtype,
    }
}

fn accepts(body: &[u8], results: &[ValueType]) -> bool {
    validate_body(body, &env_with_memory(), &ctx(&[], results)).is_ok()
}

fn accepts_no_mem(body: &[u8], results: &[ValueType]) -> bool {
    validate_body(body, &empty_env(), &ctx(&[], results)).is_ok()
}

// ---- Trivial bodies ----

#[test]
fn empty_body_no_results() {
    assert!(accepts(&[OP_END], &[]));
}

#[test]
fn empty_body_expecting_result_is_rejected() {
    assert!(!accepts(&[OP_END], &[ValueType::I32]));
}

#[test]
fn nop_then_end() {
    assert!(accepts(&[OP_NOP, OP_END], &[]));
}

#[test]
fn missing_end_is_rejected() {
    assert!(!accepts(&[OP_NOP], &[]));
}

#[test]
fn trailing_bytes_after_end_are_rejected() {
    assert!(!accepts(&[OP_END, OP_NOP], &[]));
}

// ---- Operand typing ----

#[test]
fn const_add_returns_i32() {
    let body = [OP_I32_CONST, 1, OP_I32_CONST, 2, OP_I32_ADD, OP_END];
    assert!(accepts(&body, &[ValueType::I32]));
}

#[test]
fn add_with_one_operand_is_rejected() {
    let body = [OP_I32_CONST, 1, OP_I32_ADD, OP_END];
    assert!(!accepts(&body, &[ValueType::I32]));
}

#[test]
fn leftover_operand_is_rejected() {
    let body = [OP_I32_CONST, 1, OP_I32_CONST, 2, OP_END];
    assert!(!accepts(&body, &[ValueType::I32]));
}

#[test]
fn i64_const_pushes_an_i64() {
    assert!(accepts(&[OP_I64_CONST, 1, OP_END], &[ValueType::I64]));
    assert!(!accepts(&[OP_I64_CONST, 1, OP_END], &[ValueType::I32]));
}

#[test]
fn i64_const_takes_a_ten_byte_immediate() {
    let body = [
        OP_I64_CONST, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80,
        0x7f, OP_END,
    ];
    assert!(accepts(&body, &[ValueType::I64]));
}

#[test]
fn float_consts_push_their_type() {
    // 1.0f32 is 0x3F800000, little-endian.
    let f32_body = [OP_F32_CONST, 0x00, 0x00, 0x80, 0x3f, OP_END];
    assert!(accepts(&f32_body, &[ValueType::F32]));
    assert!(!accepts(&f32_body, &[ValueType::F64]));
    // 1.0f64 is 0x3FF0000000000000.
    let f64_body = [
        OP_F64_CONST, 0, 0, 0, 0, 0, 0, 0xf0, 0x3f, OP_END,
    ];
    assert!(accepts(&f64_body, &[ValueType::F64]));
}

#[test]
fn a_truncated_float_immediate_is_rejected() {
    assert!(!accepts(&[OP_F32_CONST, 0, 0, 0, OP_END], &[ValueType::F32]));
    assert!(!accepts(&[OP_F64_CONST, 0, 0, 0, 0, OP_END], &[ValueType::F64]));
}

#[test]
fn drop_removes_an_operand() {
    let body = [OP_I32_CONST, 1, OP_I32_CONST, 2, OP_DROP, OP_END];
    assert!(accepts(&body, &[ValueType::I32]));
}

#[test]
fn drop_on_empty_stack_is_rejected() {
    assert!(!accepts(&[OP_DROP, OP_END], &[]));
}

#[test]
fn select_picks_the_common_operand_type() {
    let body = [
        OP_I32_CONST, 0, OP_F64_LOAD, 3, 0, OP_I32_CONST, 0, OP_F64_LOAD, 3, 0,
        OP_I32_CONST, 1, OP_SELECT, OP_END,
    ];
    assert!(accepts(&body, &[ValueType::F64]));
}

#[test]
fn select_with_mismatched_operands_is_rejected() {
    let body = [
        OP_I32_CONST, 1, OP_F32_LOAD, 2, 0, OP_I32_CONST, 1, OP_SELECT, OP_END,
    ];
    assert!(!accepts(&body, &[ValueType::F32]));
}

#[test]
fn select_needs_an_i32_condition() {
    let body = [
        OP_I32_CONST, 1, OP_I32_CONST, 2, OP_F32_LOAD, 2, 0, OP_SELECT, OP_END,
    ];
    assert!(!accepts(&body, &[ValueType::I32]));
}

#[test]
fn select_on_an_empty_reachable_stack_is_rejected() {
    assert!(!accepts(&[OP_SELECT, OP_END], &[]));
}

#[test]
fn select_in_unreachable_code_is_polymorphic() {
    // Nothing is on the stack, so all three operands come off as Bot and the
    // result is Bot, which then satisfies any expected type.
    assert!(accepts(&[OP_UNREACHABLE, OP_SELECT, OP_END], &[ValueType::F64]));
}

#[test]
fn select_in_unreachable_code_keeps_a_known_operand() {
    // One real i32 is visible, the other operand comes off as Bot, so the join
    // is i32 and an f64 result is rejected.
    let body = [OP_UNREACHABLE, OP_I32_CONST, 1, OP_I32_CONST, 2, OP_SELECT, OP_END];
    assert!(accepts(&body, &[ValueType::I32]));
    assert!(!accepts(&body, &[ValueType::F64]));
}

#[test]
fn wrong_result_type_is_rejected() {
    let body = [OP_I32_CONST, 1, OP_END];
    assert!(!accepts(&body, &[ValueType::I64]));
}

// ---- Control frames ----

#[test]
fn empty_block() {
    let body = [OP_BLOCK, 0x40, OP_END, OP_END];
    assert!(accepts(&body, &[]));
}

#[test]
fn block_producing_i32() {
    let body = [OP_BLOCK, 0x7f, OP_I32_CONST, 1, OP_END, OP_END];
    assert!(accepts(&body, &[ValueType::I32]));
}

#[test]
fn block_not_producing_its_result_is_rejected() {
    let body = [OP_BLOCK, 0x7f, OP_END, OP_END];
    assert!(!accepts(&body, &[ValueType::I32]));
}

#[test]
fn block_cannot_see_enclosing_operands() {
    // The i32 pushed outside the block is below the frame base, so i32.add
    // inside the block has nothing to work with.
    let body = [
        OP_I32_CONST, 1, OP_BLOCK, 0x40, OP_I32_CONST, 2, OP_I32_ADD, OP_END, OP_END,
    ];
    assert!(!accepts(&body, &[ValueType::I32]));
}

#[test]
fn unbalanced_block_is_rejected() {
    let body = [OP_BLOCK, 0x40, OP_END];
    assert!(!accepts(&body, &[]));
}

#[test]
fn nested_blocks() {
    let body = [
        OP_BLOCK, 0x40, OP_BLOCK, 0x40, OP_END, OP_END, OP_END,
    ];
    assert!(accepts(&body, &[]));
}

#[test]
fn invalid_block_type_is_rejected() {
    let body = [OP_BLOCK, 0x00, OP_END, OP_END];
    assert!(!accepts(&body, &[]));
}

#[test]
fn empty_loop() {
    let body = [OP_LOOP, 0x40, OP_END, OP_END];
    assert!(accepts(&body, &[]));
}

// ---- if/else ----

#[test]
fn if_without_else_needs_a_condition() {
    let body = [OP_I32_CONST, 0, OP_IF, 0x40, OP_END, OP_END];
    assert!(accepts(&body, &[]));
    assert!(!accepts(&[OP_IF, 0x40, OP_END, OP_END], &[]));
}

#[test]
fn if_without_else_and_no_result() {
    let body = [OP_I32_CONST, 0, OP_IF, 0x40, OP_NOP, OP_END, OP_END];
    assert!(accepts(&body, &[]));
}

#[test]
fn if_without_else_producing_a_result_is_rejected() {
    // Wasm 1.0 requires an `else` whenever the `if` has a result type: the
    // implicit empty else-branch cannot produce it.
    let body = [OP_I32_CONST, 0, OP_IF, 0x7f, OP_I32_CONST, 1, OP_END, OP_END];
    assert!(!accepts(&body, &[ValueType::I32]));
}

#[test]
fn if_else_producing_a_result() {
    let body = [
        OP_I32_CONST, 0, OP_IF, 0x7f, OP_I32_CONST, 1, OP_ELSE, OP_I32_CONST, 2, OP_END,
        OP_END,
    ];
    assert!(accepts(&body, &[ValueType::I32]));
}

#[test]
fn else_branch_must_produce_the_result() {
    let body = [
        OP_I32_CONST, 0, OP_IF, 0x7f, OP_I32_CONST, 1, OP_ELSE, OP_END, OP_END,
    ];
    assert!(!accepts(&body, &[ValueType::I32]));
}

#[test]
fn then_branch_must_produce_the_result() {
    let body = [
        OP_I32_CONST, 0, OP_IF, 0x7f, OP_ELSE, OP_I32_CONST, 1, OP_END, OP_END,
    ];
    assert!(!accepts(&body, &[ValueType::I32]));
}

#[test]
fn else_branch_starts_from_the_ifs_base_not_the_then_branchs_stack() {
    // The then-branch nets to an empty stack before `else`, so the else-branch
    // starts from the same base the then-branch did and has nothing to drop.
    let body = [
        OP_I32_CONST, 0, OP_IF, 0x40, OP_I32_CONST, 1, OP_DROP, OP_ELSE, OP_DROP, OP_END,
        OP_END,
    ];
    assert!(!accepts(&body, &[]));
}

#[test]
fn then_branch_leftover_operand_is_rejected_at_else() {
    let body = [
        OP_I32_CONST, 0, OP_IF, 0x40, OP_I32_CONST, 1, OP_ELSE, OP_DROP, OP_END, OP_END,
    ];
    assert!(!accepts(&body, &[]));
}

#[test]
fn else_without_if_is_rejected() {
    assert!(!accepts(&[OP_ELSE, OP_END], &[]));
}

#[test]
fn double_else_is_rejected() {
    let body = [
        OP_I32_CONST, 0, OP_IF, 0x40, OP_ELSE, OP_ELSE, OP_END, OP_END,
    ];
    assert!(!accepts(&body, &[]));
}

#[test]
fn else_after_block_is_rejected() {
    let body = [OP_BLOCK, 0x40, OP_ELSE, OP_END, OP_END];
    assert!(!accepts(&body, &[]));
}

#[test]
fn nested_if_in_then_branch() {
    let body = [
        OP_I32_CONST, 0, OP_IF, 0x40, OP_I32_CONST, 1, OP_I32_CONST, 1, OP_IF, 0x40, OP_END,
        OP_DROP, OP_END, OP_END,
    ];
    assert!(accepts(&body, &[]));
}

#[test]
fn br_out_of_then_branch() {
    let body = [
        OP_BLOCK, 0x40, OP_I32_CONST, 0, OP_IF, 0x40, OP_BR, 1, OP_ELSE, OP_END, OP_END,
        OP_END,
    ];
    assert!(accepts(&body, &[]));
}

#[test]
fn br_out_of_else_branch_makes_it_unreachable() {
    let body = [
        OP_BLOCK, 0x7f, OP_I32_CONST, 0, OP_IF, 0x7f, OP_I32_CONST, 1, OP_ELSE, OP_I32_CONST,
        2, OP_BR, 1, OP_END, OP_END, OP_DROP, OP_END,
    ];
    assert!(accepts(&body, &[]));
}

#[test]
fn if_with_an_explicit_empty_else() {
    // `if bt in* end` and `if bt in* else end` decode to the same instruction,
    // so both are accepted; only the bytes tell them apart.
    let body = [OP_I32_CONST, 0, OP_IF, 0x40, OP_NOP, OP_ELSE, OP_END, OP_END];
    assert!(accepts(&body, &[]));
}

#[test]
fn bare_if_nested_in_an_else_branch() {
    let body = [
        OP_I32_CONST, 0, OP_IF, 0x40, OP_ELSE, OP_I32_CONST, 1, OP_IF, 0x40, OP_NOP,
        OP_END, OP_END, OP_END,
    ];
    assert!(accepts(&body, &[]));
}

#[test]
fn if_condition_is_polymorphic_in_unreachable_code() {
    let body = [
        OP_UNREACHABLE, OP_IF, 0x40, OP_ELSE, OP_END, OP_END,
    ];
    assert!(accepts(&body, &[]));
}

// ---- Branches and unreachable code ----

#[test]
fn br_to_enclosing_block() {
    let body = [OP_BLOCK, 0x40, OP_BR, 0, OP_END, OP_END];
    assert!(accepts(&body, &[]));
}

#[test]
fn br_past_the_outermost_frame_is_rejected() {
    let body = [OP_BR, 5, OP_END];
    assert!(!accepts(&body, &[]));
}

#[test]
fn br_requires_the_target_result() {
    // Branching to a block that yields i32 needs an i32 on the stack.
    let body = [OP_BLOCK, 0x7f, OP_BR, 0, OP_END, OP_DROP, OP_END];
    assert!(!accepts(&body, &[]));
}

#[test]
fn br_to_loop_needs_nothing() {
    // A loop's branch target is its parameters, which are empty in Wasm 1.0,
    // so this is fine even though the loop yields an i32.
    let body = [OP_LOOP, 0x7f, OP_BR, 0, OP_END, OP_DROP, OP_END];
    assert!(accepts(&body, &[]));
}

#[test]
fn br_if_consumes_a_condition() {
    let body = [OP_BLOCK, 0x40, OP_I32_CONST, 1, OP_BR_IF, 0, OP_END, OP_END];
    assert!(accepts(&body, &[]));
}

#[test]
fn br_if_needs_a_condition() {
    let body = [OP_BLOCK, 0x40, OP_BR_IF, 0, OP_END, OP_END];
    assert!(!accepts(&body, &[]));
}

#[test]
fn br_if_leaves_the_target_types_on_the_stack() {
    // The fall-through path continues, so the block's i32 result is still
    // there and satisfies the block's own end.
    let body = [
        OP_BLOCK, 0x7f, OP_I32_CONST, 7, OP_I32_CONST, 1, OP_BR_IF, 0, OP_END,
        OP_DROP, OP_END,
    ];
    assert!(accepts(&body, &[]));
}

#[test]
fn br_if_requires_the_target_result() {
    let body = [OP_BLOCK, 0x7f, OP_I32_CONST, 1, OP_BR_IF, 0, OP_END, OP_DROP, OP_END];
    assert!(!accepts(&body, &[]));
}

#[test]
fn br_if_does_not_make_the_rest_unreachable() {
    // Unlike br, the code after br_if is reachable, so i32.add there has no
    // operands rather than being polymorphic.
    assert!(!accepts(
        &[OP_I32_CONST, 1, OP_BR_IF, 0, OP_I32_ADD, OP_DROP, OP_END],
        &[]
    ));
    assert!(accepts(&[OP_BR, 0, OP_I32_ADD, OP_DROP, OP_END], &[]));
}

#[test]
fn br_if_past_the_outermost_frame_is_rejected() {
    let body = [OP_I32_CONST, 1, OP_BR_IF, 5, OP_END];
    assert!(!accepts(&body, &[]));
}

#[test]
fn br_table_with_an_empty_table() {
    // Only the default label, which is what `vec(labelidx)` of length zero
    // leaves; the effect is br's.
    let body = [OP_BLOCK, 0x40, OP_I32_CONST, 0, OP_BR_TABLE, 0, 0, OP_END, OP_END];
    assert!(accepts(&body, &[]));
}

#[test]
fn br_table_needs_an_index_operand() {
    let body = [OP_BLOCK, 0x40, OP_BR_TABLE, 0, 0, OP_END, OP_END];
    assert!(!accepts(&body, &[]));
}

#[test]
fn br_table_targets_must_agree() {
    // Depth 0 is the i32 block, depth 1 the empty one, so the two targets
    // disagree and `same_lab` has no common type.
    let body = [
        OP_BLOCK, 0x40, OP_BLOCK, 0x7f, OP_I32_CONST, 0, OP_BR_TABLE, 1, 0, 1,
        OP_END, OP_DROP, OP_END, OP_END,
    ];
    assert!(!accepts(&body, &[]));
}

#[test]
fn br_table_with_agreeing_targets() {
    // Both targets are empty blocks, so the table is well typed.
    let body = [
        OP_BLOCK, 0x40, OP_BLOCK, 0x40, OP_I32_CONST, 0, OP_BR_TABLE, 1, 0, 1,
        OP_END, OP_END, OP_END,
    ];
    assert!(accepts(&body, &[]));
}

#[test]
fn br_table_requires_the_target_result() {
    let body = [
        OP_BLOCK, 0x7f, OP_I32_CONST, 0, OP_BR_TABLE, 0, 0, OP_END, OP_DROP,
        OP_END,
    ];
    assert!(!accepts(&body, &[]));
    let body_ok = [
        OP_BLOCK, 0x7f, OP_I32_CONST, 7, OP_I32_CONST, 0, OP_BR_TABLE, 0, 0,
        OP_END, OP_DROP, OP_END,
    ];
    assert!(accepts(&body_ok, &[]));
}

#[test]
fn br_table_makes_the_rest_unreachable() {
    let body = [OP_I32_CONST, 0, OP_BR_TABLE, 0, 0, OP_I32_ADD, OP_DROP, OP_END];
    assert!(accepts(&body, &[]));
}

#[test]
fn br_table_past_the_outermost_frame_is_rejected() {
    assert!(!accepts(&[OP_I32_CONST, 0, OP_BR_TABLE, 0, 5, OP_END], &[]));
    assert!(!accepts(&[OP_I32_CONST, 0, OP_BR_TABLE, 1, 5, 0, OP_END], &[]));
}

#[test]
fn br_table_truncated_is_rejected() {
    // The count says three labels; only one follows.
    assert!(!accepts(&[OP_I32_CONST, 0, OP_BR_TABLE, 3, 0, OP_END], &[]));
}

#[test]
fn br_table_to_a_loop_needs_nothing() {
    // A loop's branch target is empty, so a table mixing a loop with an empty
    // block agrees.
    let body = [
        OP_BLOCK, 0x40, OP_LOOP, 0x7f, OP_I32_CONST, 0, OP_BR_TABLE, 1, 0, 1,
        OP_END, OP_DROP, OP_END, OP_END,
    ];
    assert!(accepts(&body, &[]));
}

#[test]
fn return_consumes_the_functions_results() {
    assert!(accepts(
        &[OP_I32_CONST, 1, OP_RETURN, OP_END],
        &[ValueType::I32]
    ));
}

#[test]
fn return_needs_the_functions_results() {
    assert!(!accepts(&[OP_RETURN, OP_END], &[ValueType::I32]));
}

#[test]
fn return_makes_the_rest_of_the_frame_unreachable() {
    assert!(accepts(&[OP_RETURN, OP_I32_ADD, OP_DROP, OP_END], &[]));
}

#[test]
fn return_from_a_block_yields_the_functions_results() {
    // Not the block's: the enclosing block declares nothing, so if `return`
    // took its result list instead it would leave the i32 behind and the
    // block's `end` would reject.
    assert!(accepts(
        &[
            OP_BLOCK, 0x40, OP_I32_CONST, 1, OP_RETURN, OP_END, OP_I32_CONST, 2,
            OP_END
        ],
        &[ValueType::I32]
    ));
}

#[test]
fn unreachable_makes_the_rest_of_the_frame_polymorphic() {
    // i32.add after unreachable has no operands, but the frame is polymorphic.
    let body = [OP_UNREACHABLE, OP_I32_ADD, OP_END];
    assert!(accepts(&body, &[ValueType::I32]));
}

#[test]
fn unreachable_satisfies_a_missing_result() {
    assert!(accepts(&[OP_UNREACHABLE, OP_END], &[ValueType::I32]));
}

#[test]
fn unreachable_does_not_leak_past_end() {
    // The block is polymorphic, but the enclosing frame is not, so the outer
    // i32.add still has nothing to work with.
    let body = [
        OP_BLOCK, 0x40, OP_UNREACHABLE, OP_END, OP_I32_ADD, OP_END,
    ];
    assert!(!accepts(&body, &[ValueType::I32]));
}

// ---- Memory ----

#[test]
fn i32_load_requires_a_memory() {
    let body = [OP_I32_CONST, 0, OP_I32_LOAD, 2, 0, OP_END];
    assert!(accepts(&body, &[ValueType::I32]));
    assert!(!accepts_no_mem(&body, &[ValueType::I32]));
}

#[test]
fn i32_load_alignment_must_not_exceed_natural() {
    let ok = [OP_I32_CONST, 0, OP_I32_LOAD, 2, 0, OP_END];
    let bad = [OP_I32_CONST, 0, OP_I32_LOAD, 3, 0, OP_END];
    assert!(accepts(&ok, &[ValueType::I32]));
    assert!(!accepts(&bad, &[ValueType::I32]));
}

#[test]
fn narrow_load_has_smaller_natural_alignment() {
    let ok = [OP_I32_CONST, 0, OP_I32_LOAD8_S, 0, 0, OP_END];
    let bad = [OP_I32_CONST, 0, OP_I32_LOAD8_S, 1, 0, OP_END];
    assert!(accepts(&ok, &[ValueType::I32]));
    assert!(!accepts(&bad, &[ValueType::I32]));
}

#[test]
fn i64_load_yields_i64() {
    let body = [OP_I32_CONST, 0, OP_I64_LOAD, 3, 0, OP_END];
    assert!(accepts(&body, &[ValueType::I64]));
    assert!(!accepts(&body, &[ValueType::I32]));
}

#[test]
fn load_needs_an_i32_address() {
    let body = [OP_I32_LOAD, 2, 0, OP_END];
    assert!(!accepts(&body, &[ValueType::I32]));
}

#[test]
fn i32_store_consumes_address_and_value() {
    let body = [
        OP_I32_CONST, 0, OP_I32_CONST, 7, OP_I32_STORE, 2, 0, OP_END,
    ];
    assert!(accepts(&body, &[]));
}

#[test]
fn i64_store_wants_an_i64_value() {
    let body = [
        OP_I32_CONST, 0, OP_I32_CONST, 7, OP_I64_STORE, 3, 0, OP_END,
    ];
    assert!(!accepts(&body, &[]));
}

#[test]
fn store_leaves_nothing_behind() {
    let body = [
        OP_I32_CONST, 0, OP_I32_CONST, 7, OP_I32_STORE, 2, 0, OP_END,
    ];
    assert!(!accepts(&body, &[ValueType::I32]));
}

#[test]
fn unrecognized_opcode_is_rejected() {
    assert!(!accepts(&[0xfe, OP_END], &[]));
}

// ---- The numeric table: unary operators, eqz and conversions ----

#[test]
fn i32_clz_takes_and_gives_an_i32() {
    assert!(accepts(
        &[OP_I32_CONST, 1, OP_I32_CLZ, OP_END],
        &[ValueType::I32]
    ));
}

#[test]
fn i32_eqz_gives_an_i32() {
    assert!(accepts(
        &[OP_I32_CONST, 1, OP_I32_EQZ, OP_END],
        &[ValueType::I32]
    ));
}

#[test]
fn i64_eqz_takes_an_i64_and_gives_an_i32() {
    // i32.const is the only constant so far, so the i64 comes from a load.
    assert!(accepts(
        &[OP_I32_CONST, 0, OP_I64_LOAD, 3, 0, OP_I64_EQZ, OP_END],
        &[ValueType::I32]
    ));
}

#[test]
fn i64_clz_gives_an_i64() {
    assert!(accepts(
        &[OP_I32_CONST, 0, OP_I64_LOAD, 3, 0, OP_I64_CLZ, OP_END],
        &[ValueType::I64]
    ));
}

#[test]
fn i32_clz_rejects_a_float_operand() {
    assert!(!accepts(
        &[OP_I32_CONST, 0, OP_F32_LOAD, 2, 0, OP_I32_CLZ, OP_END],
        &[ValueType::I32]
    ));
}

#[test]
fn f32_sqrt_takes_and_gives_an_f32() {
    assert!(accepts(
        &[OP_I32_CONST, 0, OP_F32_LOAD, 2, 0, OP_F32_SQRT, OP_END],
        &[ValueType::F32]
    ));
}

#[test]
fn f64_neg_wants_an_f64() {
    assert!(!accepts(
        &[OP_I32_CONST, 0, OP_F32_LOAD, 2, 0, OP_F64_NEG, OP_END],
        &[ValueType::F64]
    ));
}

#[test]
fn i64_extend_i32_u_widens() {
    assert!(accepts(
        &[OP_I32_CONST, 7, OP_I64_EXTEND_I32_U, OP_END],
        &[ValueType::I64]
    ));
}

#[test]
fn f64_convert_i32_s_changes_the_type() {
    assert!(accepts(
        &[OP_I32_CONST, 7, OP_F64_CONVERT_I32_S, OP_END],
        &[ValueType::F64]
    ));
}

#[test]
fn f32_reinterpret_i32_changes_the_type() {
    assert!(accepts(
        &[OP_I32_CONST, 7, OP_F32_REINTERPRET_I32, OP_END],
        &[ValueType::F32]
    ));
}

#[test]
fn i32_wrap_i64_narrows() {
    assert!(accepts(
        &[OP_I32_CONST, 0, OP_I64_LOAD, 3, 0, OP_I32_WRAP_I64, OP_END],
        &[ValueType::I32]
    ));
}

#[test]
fn i32_wrap_i64_rejects_an_i32_operand() {
    assert!(!accepts(
        &[OP_I32_CONST, 1, OP_I32_WRAP_I64, OP_END],
        &[ValueType::I32]
    ));
}

#[test]
fn f32_demote_f64_wants_an_f64() {
    assert!(!accepts(
        &[OP_I32_CONST, 0, OP_F32_LOAD, 2, 0, OP_F32_DEMOTE_F64, OP_END],
        &[ValueType::F32]
    ));
}

#[test]
fn a_unary_operator_needs_an_operand() {
    assert!(!accepts(&[OP_I32_CLZ, OP_END], &[ValueType::I32]));
}

#[test]
fn unary_operators_are_polymorphic_after_unreachable() {
    assert!(accepts(
        &[OP_UNREACHABLE, OP_I32_CLZ, OP_END],
        &[ValueType::I32]
    ));
}

// ---- The numeric table: binary operators and comparisons ----

#[test]
fn i32_sub_takes_two_i32s() {
    assert!(accepts(
        &[OP_I32_CONST, 3, OP_I32_CONST, 1, OP_I32_SUB, OP_END],
        &[ValueType::I32]
    ));
}

#[test]
fn i32_shr_u_is_a_binary_operator() {
    assert!(accepts(
        &[OP_I32_CONST, 8, OP_I32_CONST, 1, OP_I32_SHR_U, OP_END],
        &[ValueType::I32]
    ));
}

#[test]
fn i32_eq_yields_an_i32() {
    assert!(accepts(
        &[OP_I32_CONST, 1, OP_I32_CONST, 1, OP_I32_EQ, OP_END],
        &[ValueType::I32]
    ));
}

#[test]
fn i64_lt_u_takes_two_i64s_and_yields_an_i32() {
    let body = [
        OP_I32_CONST,
        0,
        OP_I64_LOAD,
        3,
        0,
        OP_I32_CONST,
        0,
        OP_I64_LOAD,
        3,
        0,
        OP_I64_LT_U,
        OP_END,
    ];
    assert!(accepts(&body, &[ValueType::I32]));
}

#[test]
fn i64_add_yields_an_i64() {
    let body = [
        OP_I32_CONST,
        0,
        OP_I64_LOAD,
        3,
        0,
        OP_I32_CONST,
        0,
        OP_I64_LOAD,
        3,
        0,
        OP_I64_ADD,
        OP_END,
    ];
    assert!(accepts(&body, &[ValueType::I64]));
}

#[test]
fn f64_ge_yields_an_i32_not_an_f64() {
    let body = [
        OP_I32_CONST,
        0,
        OP_F64_LOAD,
        3,
        0,
        OP_I32_CONST,
        0,
        OP_F64_LOAD,
        3,
        0,
        OP_F64_GE,
        OP_END,
    ];
    assert!(accepts(&body, &[ValueType::I32]));
    assert!(!accepts(&body, &[ValueType::F64]));
}

#[test]
fn f32_min_wants_f32_operands() {
    assert!(!accepts(
        &[OP_I32_CONST, 1, OP_I32_CONST, 1, OP_F32_MIN, OP_END],
        &[ValueType::F32]
    ));
}

#[test]
fn i32_add_still_works_from_the_table() {
    assert!(accepts(
        &[OP_I32_CONST, 1, OP_I32_CONST, 2, OP_I32_ADD, OP_END],
        &[ValueType::I32]
    ));
}

#[test]
fn a_binary_operator_needs_two_operands() {
    assert!(!accepts(
        &[OP_I32_CONST, 1, OP_I32_ADD, OP_END],
        &[ValueType::I32]
    ));
}

// ---- The local operators ----

#[test]
fn local_get_pushes_the_declared_type() {
    assert!(accepts_locals(
        &[OP_LOCAL_GET, 0, OP_END],
        &[ValueType::I32],
        &[ValueType::I32]
    ));
}

#[test]
fn local_get_of_the_wrong_type_is_rejected() {
    assert!(!accepts_locals(
        &[OP_LOCAL_GET, 0, OP_END],
        &[ValueType::I64],
        &[ValueType::I32]
    ));
}

#[test]
fn local_get_indexes_from_zero() {
    assert!(accepts_locals(
        &[OP_LOCAL_GET, 1, OP_END],
        &[ValueType::I32, ValueType::F64],
        &[ValueType::F64]
    ));
}

#[test]
fn local_get_out_of_range_is_rejected() {
    assert!(!accepts_locals(
        &[OP_LOCAL_GET, 1, OP_END],
        &[ValueType::I32],
        &[ValueType::I32]
    ));
}

#[test]
fn local_set_consumes_a_value() {
    assert!(accepts_locals(
        &[OP_I32_CONST, 7, OP_LOCAL_SET, 0, OP_END],
        &[ValueType::I32],
        &[]
    ));
}

#[test]
fn local_set_wants_the_locals_type() {
    assert!(!accepts_locals(
        &[OP_I32_CONST, 7, OP_LOCAL_SET, 0, OP_END],
        &[ValueType::F32],
        &[]
    ));
}

#[test]
fn local_set_needs_an_operand() {
    assert!(!accepts_locals(
        &[OP_LOCAL_SET, 0, OP_END],
        &[ValueType::I32],
        &[]
    ));
}

#[test]
fn local_tee_leaves_the_value_behind() {
    assert!(accepts_locals(
        &[OP_I32_CONST, 7, OP_LOCAL_TEE, 0, OP_END],
        &[ValueType::I32],
        &[ValueType::I32]
    ));
}

#[test]
fn local_tee_is_not_local_set() {
    // set leaves nothing, so the same body with a declared result fails.
    assert!(!accepts_locals(
        &[OP_I32_CONST, 7, OP_LOCAL_SET, 0, OP_END],
        &[ValueType::I32],
        &[ValueType::I32]
    ));
}

#[test]
fn a_local_index_is_a_leb128() {
    // 0x80 0x00 is a non-minimal encoding of 0, which the spec admits.
    assert!(accepts_locals(
        &[OP_LOCAL_GET, 0x80, 0x00, OP_END],
        &[ValueType::I32],
        &[ValueType::I32]
    ));
}

#[test]
fn local_get_is_polymorphic_after_unreachable() {
    assert!(accepts_locals(
        &[OP_UNREACHABLE, OP_LOCAL_SET, 0, OP_END],
        &[ValueType::I32],
        &[]
    ));
}

// ---- The global operators ----

#[test]
fn global_get_pushes_the_declared_type() {
    assert!(accepts_globals(
        &[OP_GLOBAL_GET, 0, OP_END],
        &[global(Mut::Const, ValueType::I32)],
        &[ValueType::I32]
    ));
}

#[test]
fn global_get_of_the_wrong_type_is_rejected() {
    assert!(!accepts_globals(
        &[OP_GLOBAL_GET, 0, OP_END],
        &[global(Mut::Const, ValueType::I64)],
        &[ValueType::I32]
    ));
}

#[test]
fn global_get_indexes_from_zero() {
    assert!(accepts_globals(
        &[OP_GLOBAL_GET, 1, OP_END],
        &[
            global(Mut::Const, ValueType::I32),
            global(Mut::Const, ValueType::F64)
        ],
        &[ValueType::F64]
    ));
}

#[test]
fn global_get_out_of_range_is_rejected() {
    assert!(!accepts_globals(
        &[OP_GLOBAL_GET, 1, OP_END],
        &[global(Mut::Const, ValueType::I32)],
        &[ValueType::I32]
    ));
}

#[test]
fn global_set_consumes_a_value() {
    assert!(accepts_globals(
        &[OP_I32_CONST, 7, OP_GLOBAL_SET, 0, OP_END],
        &[global(Mut::Var, ValueType::I32)],
        &[]
    ));
}

#[test]
fn global_set_of_an_immutable_global_is_rejected() {
    assert!(!accepts_globals(
        &[OP_I32_CONST, 7, OP_GLOBAL_SET, 0, OP_END],
        &[global(Mut::Const, ValueType::I32)],
        &[]
    ));
}

#[test]
fn global_get_of_an_immutable_global_is_fine() {
    // Only the write is guarded, so the same global reads either way.
    assert!(accepts_globals(
        &[OP_GLOBAL_GET, 0, OP_END],
        &[global(Mut::Const, ValueType::I32)],
        &[ValueType::I32]
    ));
}

#[test]
fn global_set_wants_the_globals_type() {
    assert!(!accepts_globals(
        &[OP_I32_CONST, 7, OP_GLOBAL_SET, 0, OP_END],
        &[global(Mut::Var, ValueType::F32)],
        &[]
    ));
}

#[test]
fn global_set_needs_an_operand() {
    assert!(!accepts_globals(
        &[OP_GLOBAL_SET, 0, OP_END],
        &[global(Mut::Var, ValueType::I32)],
        &[]
    ));
}

#[test]
fn global_set_leaves_nothing_behind() {
    assert!(!accepts_globals(
        &[OP_I32_CONST, 7, OP_GLOBAL_SET, 0, OP_END],
        &[global(Mut::Var, ValueType::I32)],
        &[ValueType::I32]
    ));
}

#[test]
fn a_global_index_is_a_leb128() {
    assert!(accepts_globals(
        &[OP_GLOBAL_GET, 0x80, 0x00, OP_END],
        &[global(Mut::Const, ValueType::I32)],
        &[ValueType::I32]
    ));
}

#[test]
fn global_set_is_polymorphic_after_unreachable() {
    assert!(accepts_globals(
        &[OP_UNREACHABLE, OP_GLOBAL_SET, 0, OP_END],
        &[global(Mut::Var, ValueType::I32)],
        &[]
    ));
}

#[test]
fn global_set_of_an_immutable_global_is_rejected_after_unreachable() {
    // The mutability guard is not polymorphic: unreachable code is still
    // checked for it.
    assert!(!accepts_globals(
        &[OP_UNREACHABLE, OP_GLOBAL_SET, 0, OP_END],
        &[global(Mut::Const, ValueType::I32)],
        &[]
    ));
}

// ---- memory.size and memory.grow ----

#[test]
fn memory_size_pushes_an_i32() {
    assert!(accepts(&[OP_MEMORY_SIZE, 0x00, OP_END], &[ValueType::I32]));
}

#[test]
fn memory_size_needs_the_reserved_zero() {
    assert!(!accepts(&[OP_MEMORY_SIZE, OP_END], &[ValueType::I32]));
    assert!(!accepts(&[OP_MEMORY_SIZE, 0x01, OP_END], &[ValueType::I32]));
}

#[test]
fn memory_size_needs_a_memory() {
    assert!(!accepts_no_mem(
        &[OP_MEMORY_SIZE, 0x00, OP_END],
        &[ValueType::I32]
    ));
}

#[test]
fn memory_grow_consumes_and_produces_an_i32() {
    assert!(accepts(
        &[OP_I32_CONST, 1, OP_MEMORY_GROW, 0x00, OP_END],
        &[ValueType::I32]
    ));
}

#[test]
fn memory_grow_needs_an_operand() {
    assert!(!accepts(&[OP_MEMORY_GROW, 0x00, OP_END], &[ValueType::I32]));
}

#[test]
fn memory_grow_needs_a_memory() {
    assert!(!accepts_no_mem(
        &[OP_I32_CONST, 1, OP_MEMORY_GROW, 0x00, OP_END],
        &[ValueType::I32]
    ));
}

// ---- call and call_indirect ----

fn ft(params: &[ValueType], results: &[ValueType]) -> FuncType {
    FuncType {
        params: params.to_vec(),
        results: results.to_vec(),
    }
}

/// One function and one type with the same signature, plus a table, so both
/// call forms can be exercised against the same module.
fn env_with_signature(sig: FuncType) -> Env {
    let mut module = env_with_memory();
    module.func_types.push(sig.clone());
    module.types.push(sig);
    module.table_types.push(TableType {
        limits: Limits { min: 1, max: None },
        elem: ElemType::FuncRef,
    });
    module
}

fn accepts_sig(body: &[u8], sig: FuncType, results: &[ValueType]) -> bool {
    validate_body(body, &env_with_signature(sig), &ctx(&[], results)).is_ok()
}

#[test]
fn call_consumes_its_parameters_and_produces_its_result() {
    assert!(accepts_sig(
        &[OP_I32_CONST, 1, OP_I64_CONST, 2, OP_CALL, 0, OP_END],
        ft(&[ValueType::I32, ValueType::I64], &[ValueType::F32]),
        &[ValueType::F32]
    ));
}

#[test]
fn call_takes_its_parameters_in_order() {
    // The last parameter is on top, so swapping them is a type mismatch.
    assert!(!accepts_sig(
        &[OP_I64_CONST, 2, OP_I32_CONST, 1, OP_CALL, 0, OP_END],
        ft(&[ValueType::I32, ValueType::I64], &[ValueType::F32]),
        &[ValueType::F32]
    ));
}

#[test]
fn call_needs_the_function_to_exist() {
    assert!(!accepts_sig(
        &[OP_CALL, 1, OP_END],
        ft(&[], &[]),
        &[]
    ));
}

#[test]
fn call_rejects_a_multi_value_callee() {
    assert!(matches!(
        validate_body(
            &[OP_CALL, 0, OP_DROP, OP_DROP, OP_END],
            &env_with_signature(ft(&[], &[ValueType::I32, ValueType::I32])),
            &ctx(&[], &[])
        ),
        Err(OpError::TooManyResults)
    ));
}

#[test]
fn call_indirect_takes_the_table_index_on_top() {
    assert!(accepts_sig(
        &[OP_I64_CONST, 2, OP_I32_CONST, 0, OP_CALL_INDIRECT, 0, 0x00, OP_END],
        ft(&[ValueType::I64], &[ValueType::F32]),
        &[ValueType::F32]
    ));
}

#[test]
fn call_indirect_needs_the_table_index_operand() {
    assert!(!accepts_sig(
        &[OP_I64_CONST, 2, OP_CALL_INDIRECT, 0, 0x00, OP_END],
        ft(&[ValueType::I64], &[ValueType::F32]),
        &[ValueType::F32]
    ));
}

#[test]
fn call_indirect_needs_a_table() {
    let mut module = env_with_memory();
    module.types.push(ft(&[], &[]));
    assert!(matches!(
        validate_body(
            &[OP_I32_CONST, 0, OP_CALL_INDIRECT, 0, 0x00, OP_END],
            &module,
            &ctx(&[], &[])
        ),
        Err(OpError::UnknownTable)
    ));
}

#[test]
fn call_indirect_needs_a_zero_table_byte() {
    assert!(matches!(
        validate_body(
            &[OP_I32_CONST, 0, OP_CALL_INDIRECT, 0, 0x01, OP_END],
            &env_with_signature(ft(&[], &[])),
            &ctx(&[], &[])
        ),
        Err(OpError::ReservedByteNotZero)
    ));
}

// ---- Implementation limits ----

#[test]
fn a_body_at_the_size_limit_is_still_validated() {
    // MAX_FUNCTION_BYTES nops followed by the closing end would be one byte
    // over, so stop one short. This is the largest body the validator accepts,
    // and it must be accepted on its merits rather than rejected for size.
    let mut body = vec![OP_NOP; MAX_FUNCTION_BYTES - 1];
    body.push(OP_END);
    assert_eq!(body.len(), MAX_FUNCTION_BYTES);
    assert!(accepts(&body, &[]));
}

#[test]
fn a_body_over_the_size_limit_is_rejected_for_size() {
    let mut body = vec![OP_NOP; MAX_FUNCTION_BYTES];
    body.push(OP_END);
    assert!(matches!(
        validate_body(&body, &env_with_memory(), &ctx(&[], &[])),
        Err(OpError::BodyTooLarge)
    ));
}

#[test]
fn the_size_limit_is_checked_before_anything_else() {
    // An oversized body that is also ill-typed is rejected for size, so the
    // check cannot be reached only on otherwise-valid input.
    let body = vec![OP_I32_ADD; MAX_FUNCTION_BYTES + 1];
    assert!(matches!(
        validate_body(&body, &env_with_memory(), &ctx(&[], &[])),
        Err(OpError::BodyTooLarge)
    ));
}
