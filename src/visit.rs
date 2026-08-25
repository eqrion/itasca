//! The push interface: one hook per validated operator.
//!
//! `opiter` owns the decode and validate loop and calls into a consumer here,
//! which is the whole point: the loop a compiler runs is the loop the theorems
//! are about. A hook receives the operator's immediates already decoded and
//! already checked, plus the validator state, and may decline the body.
//!
//! There is one hook per opcode so a consumer never switches on an opcode the
//! validator has already switched on. The 146 that carry no immediates beyond
//! a `memarg` come from one table each, below, which also generates the two
//! fan-out functions `opiter` dispatches through; the rest have immediates of
//! their own and are written out. `OpIter_Table.v` proves that both tables map
//! an opcode to the hook the specification's instruction table names.
//!
//! Every hook has a default that does nothing, so a consumer writes only the
//! ones it wants, and monomorphisation erases the rest.

use crate::error::VisitError;
use crate::opiter::*;

/// What a hook returns. `Ok` is "carry on", and it is the only answer that
/// lets validation finish.
pub type VisitResult = core::result::Result<(), VisitError>;

/// The numeric operators: 123 rows, no immediates. One table, used twice.
///
/// `#[macro_export]`ed so a consumer building a C ABI on top of this crate --
/// SpiderMonkey's `veriwasm_glue` is one -- can build its vtable from this
/// table rather than transcribing it. This is the only place the
/// opcode-to-hook mapping lives, and `OpIter_Table.v` proves its rows are not
/// off by one, so a second copy would be a copy that proof does not cover.
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
/// Two obligations, both about code this crate does not contain:
///
/// - `OpIter_Visit.hooks_total`: every hook returns. Discharged by not
///   panicking and not looping. Without it nothing says the validator
///   terminates.
/// - `OpIter_Visit.hooks_accept`: every hook returns `Ok`. Without it a
///   well-typed body may be refused, which is reported as
///   `OpError::Visitor` and is not a validity verdict.
///
/// Neither can turn a rejection into an acceptance: `validate_body_with_typed`
/// holds for every consumer, hostile ones included, because acceptance is
/// decided before a hook is consulted. What a bad hook can do is refuse a
/// valid body or fail to terminate.
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

    /// The immediate's bits, not a float: `f32::from_bits` is outside the
    /// Aeneas subset, and a consumer that wants the value can convert.
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
pub struct NopVisitor;

impl OpVisitor for NopVisitor {}

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
