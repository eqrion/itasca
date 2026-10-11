import Itasca.Generated.Types

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

/-- A callback result retains ordinary visitor rejection. -/
abbrev VisitResult := core.result.Result Unit error.VisitError

/-- Numeric callback identities, named by their API mnemonics. -/
inductive NumericHook where
  | i32_eqz
  | i32_eq
  | i32_ne
  | i32_lt_s
  | i32_lt_u
  | i32_gt_s
  | i32_gt_u
  | i32_le_s
  | i32_le_u
  | i32_ge_s
  | i32_ge_u
  | i64_eqz
  | i64_eq
  | i64_ne
  | i64_lt_s
  | i64_lt_u
  | i64_gt_s
  | i64_gt_u
  | i64_le_s
  | i64_le_u
  | i64_ge_s
  | i64_ge_u
  | f32_eq
  | f32_ne
  | f32_lt
  | f32_gt
  | f32_le
  | f32_ge
  | f64_eq
  | f64_ne
  | f64_lt
  | f64_gt
  | f64_le
  | f64_ge
  | i32_sub
  | i32_mul
  | i32_div_s
  | i32_div_u
  | i32_rem_s
  | i32_rem_u
  | i32_and
  | i32_or
  | i32_xor
  | i32_shl
  | i32_shr_s
  | i32_shr_u
  | i32_rotl
  | i32_rotr
  | i64_add
  | i64_sub
  | i64_mul
  | i64_div_s
  | i64_div_u
  | i64_rem_s
  | i64_rem_u
  | i64_and
  | i64_or
  | i64_xor
  | i64_shl
  | i64_shr_s
  | i64_shr_u
  | i64_rotl
  | i64_rotr
  | f32_add
  | f32_sub
  | f32_mul
  | f32_div
  | f32_min
  | f32_max
  | f32_copysign
  | f64_add
  | f64_sub
  | f64_mul
  | f64_div
  | f64_min
  | f64_max
  | f64_copysign
  | i32_clz
  | i32_ctz
  | i32_popcnt
  | i32_add
  | i64_clz
  | i64_ctz
  | i64_popcnt
  | f32_abs
  | f32_neg
  | f32_ceil
  | f32_floor
  | f32_trunc
  | f32_nearest
  | f32_sqrt
  | f64_abs
  | f64_neg
  | f64_ceil
  | f64_floor
  | f64_trunc
  | f64_nearest
  | f64_sqrt
  | i32_wrap_i64
  | i32_trunc_f32_s
  | i32_trunc_f32_u
  | i32_trunc_f64_s
  | i32_trunc_f64_u
  | i64_extend_i32_s
  | i64_extend_i32_u
  | i64_trunc_f32_s
  | i64_trunc_f32_u
  | i64_trunc_f64_s
  | i64_trunc_f64_u
  | f32_convert_i32_s
  | f32_convert_i32_u
  | f32_convert_i64_s
  | f32_convert_i64_u
  | f32_demote_f64
  | f64_convert_i32_s
  | f64_convert_i32_u
  | f64_convert_i64_s
  | f64_convert_i64_u
  | f64_promote_f32
  | i32_reinterpret_f32
  | i64_reinterpret_f64
  | f32_reinterpret_i32
  | f64_reinterpret_i64
  deriving DecidableEq

/-- Memory callback identities, named by their API mnemonics. -/
inductive MemoryHook where
  | i32_load
  | i64_load
  | f32_load
  | f64_load
  | i32_load8_s
  | i32_load8_u
  | i32_load16_s
  | i32_load16_u
  | i64_load8_s
  | i64_load8_u
  | i64_load16_s
  | i64_load16_u
  | i64_load32_s
  | i64_load32_u
  | i32_store
  | i64_store
  | f32_store
  | f64_store
  | i32_store8
  | i32_store16
  | i64_store8
  | i64_store16
  | i64_store32
  deriving DecidableEq

/-- Exact instruction-hook arguments. Floating constants retain every input bit. -/
inductive Action where
  | unreachable
  | nop
  | block : signature.BlockType → Action
  | loop : signature.BlockType → Action
  | if_ : signature.BlockType → Action
  | else_ : signature.BlockType → Action
  | end_ : code.LabelKind → signature.BlockType → Action
  | br : U32 → signature.ResultType → Action
  | br_if : U32 → signature.ResultType → Action
  | br_table_label : U32 → Action
  | br_table : U32 → signature.ResultType → Action
  | return_
  | call : U32 → Action
  | call_indirect : U32 → Action
  | drop : code.StackType → Action
  | select : code.StackType → Action
  | local_get : U32 → Action
  | local_set : U32 → Action
  | local_tee : U32 → Action
  | global_get : U32 → Action
  | global_set : U32 → Action
  | memory_size
  | memory_grow
  | i32_const : I32 → Action
  | i64_const : I64 → Action
  | f32_const : U32 → Action
  | f64_const : U64 → Action
  | numeric : NumericHook → Action
  | memory : MemoryHook → code.MemArg → Action

/-- Every callback argument, including the validator state observed by a hook. -/
inductive Event where
  | functionStart : code.Context → U32 → Usize → Usize → Event
  | op : code.OpIterState → Action → Event

/-- One returned callback, including the callback that rejects a run. -/
structure Observation where
  event : Event
  outcome : VisitResult

/-- Invoke the uniquely named callback represented by an event. -/
def invoke {V : Type} (visitor : code.OpVisitor V) (v : V) :
    Event → Result (VisitResult × V)
  | .functionStart ctx typeidx bodybegin bodyend =>
      visitor.on_function_start v ctx typeidx bodybegin bodyend
  | .op st action =>
    match action with
    | .unreachable => visitor.on_unreachable v st
    | .nop => visitor.on_nop v st
    | .block a0 => visitor.on_block v st a0
    | .loop a0 => visitor.on_loop v st a0
    | .if_ a0 => visitor.on_if v st a0
    | .else_ a0 => visitor.on_else v st a0
    | .end_ a0 a1 => visitor.on_end v st a0 a1
    | .br a0 a1 => visitor.on_br v st a0 a1
    | .br_if a0 a1 => visitor.on_br_if v st a0 a1
    | .br_table_label a0 => visitor.on_br_table_label v st a0
    | .br_table a0 a1 => visitor.on_br_table v st a0 a1
    | .return_ => visitor.on_return v st
    | .call a0 => visitor.on_call v st a0
    | .call_indirect a0 => visitor.on_call_indirect v st a0
    | .drop a0 => visitor.on_drop v st a0
    | .select a0 => visitor.on_select v st a0
    | .local_get a0 => visitor.on_local_get v st a0
    | .local_set a0 => visitor.on_local_set v st a0
    | .local_tee a0 => visitor.on_local_tee v st a0
    | .global_get a0 => visitor.on_global_get v st a0
    | .global_set a0 => visitor.on_global_set v st a0
    | .memory_size => visitor.on_memory_size v st
    | .memory_grow => visitor.on_memory_grow v st
    | .i32_const a0 => visitor.on_i32_const v st a0
    | .i64_const a0 => visitor.on_i64_const v st a0
    | .f32_const a0 => visitor.on_f32_const v st a0
    | .f64_const a0 => visitor.on_f64_const v st a0
    | .numeric hook =>
      match hook with
      | .i32_eqz => visitor.on_i32_eqz v st
      | .i32_eq => visitor.on_i32_eq v st
      | .i32_ne => visitor.on_i32_ne v st
      | .i32_lt_s => visitor.on_i32_lt_s v st
      | .i32_lt_u => visitor.on_i32_lt_u v st
      | .i32_gt_s => visitor.on_i32_gt_s v st
      | .i32_gt_u => visitor.on_i32_gt_u v st
      | .i32_le_s => visitor.on_i32_le_s v st
      | .i32_le_u => visitor.on_i32_le_u v st
      | .i32_ge_s => visitor.on_i32_ge_s v st
      | .i32_ge_u => visitor.on_i32_ge_u v st
      | .i64_eqz => visitor.on_i64_eqz v st
      | .i64_eq => visitor.on_i64_eq v st
      | .i64_ne => visitor.on_i64_ne v st
      | .i64_lt_s => visitor.on_i64_lt_s v st
      | .i64_lt_u => visitor.on_i64_lt_u v st
      | .i64_gt_s => visitor.on_i64_gt_s v st
      | .i64_gt_u => visitor.on_i64_gt_u v st
      | .i64_le_s => visitor.on_i64_le_s v st
      | .i64_le_u => visitor.on_i64_le_u v st
      | .i64_ge_s => visitor.on_i64_ge_s v st
      | .i64_ge_u => visitor.on_i64_ge_u v st
      | .f32_eq => visitor.on_f32_eq v st
      | .f32_ne => visitor.on_f32_ne v st
      | .f32_lt => visitor.on_f32_lt v st
      | .f32_gt => visitor.on_f32_gt v st
      | .f32_le => visitor.on_f32_le v st
      | .f32_ge => visitor.on_f32_ge v st
      | .f64_eq => visitor.on_f64_eq v st
      | .f64_ne => visitor.on_f64_ne v st
      | .f64_lt => visitor.on_f64_lt v st
      | .f64_gt => visitor.on_f64_gt v st
      | .f64_le => visitor.on_f64_le v st
      | .f64_ge => visitor.on_f64_ge v st
      | .i32_sub => visitor.on_i32_sub v st
      | .i32_mul => visitor.on_i32_mul v st
      | .i32_div_s => visitor.on_i32_div_s v st
      | .i32_div_u => visitor.on_i32_div_u v st
      | .i32_rem_s => visitor.on_i32_rem_s v st
      | .i32_rem_u => visitor.on_i32_rem_u v st
      | .i32_and => visitor.on_i32_and v st
      | .i32_or => visitor.on_i32_or v st
      | .i32_xor => visitor.on_i32_xor v st
      | .i32_shl => visitor.on_i32_shl v st
      | .i32_shr_s => visitor.on_i32_shr_s v st
      | .i32_shr_u => visitor.on_i32_shr_u v st
      | .i32_rotl => visitor.on_i32_rotl v st
      | .i32_rotr => visitor.on_i32_rotr v st
      | .i64_add => visitor.on_i64_add v st
      | .i64_sub => visitor.on_i64_sub v st
      | .i64_mul => visitor.on_i64_mul v st
      | .i64_div_s => visitor.on_i64_div_s v st
      | .i64_div_u => visitor.on_i64_div_u v st
      | .i64_rem_s => visitor.on_i64_rem_s v st
      | .i64_rem_u => visitor.on_i64_rem_u v st
      | .i64_and => visitor.on_i64_and v st
      | .i64_or => visitor.on_i64_or v st
      | .i64_xor => visitor.on_i64_xor v st
      | .i64_shl => visitor.on_i64_shl v st
      | .i64_shr_s => visitor.on_i64_shr_s v st
      | .i64_shr_u => visitor.on_i64_shr_u v st
      | .i64_rotl => visitor.on_i64_rotl v st
      | .i64_rotr => visitor.on_i64_rotr v st
      | .f32_add => visitor.on_f32_add v st
      | .f32_sub => visitor.on_f32_sub v st
      | .f32_mul => visitor.on_f32_mul v st
      | .f32_div => visitor.on_f32_div v st
      | .f32_min => visitor.on_f32_min v st
      | .f32_max => visitor.on_f32_max v st
      | .f32_copysign => visitor.on_f32_copysign v st
      | .f64_add => visitor.on_f64_add v st
      | .f64_sub => visitor.on_f64_sub v st
      | .f64_mul => visitor.on_f64_mul v st
      | .f64_div => visitor.on_f64_div v st
      | .f64_min => visitor.on_f64_min v st
      | .f64_max => visitor.on_f64_max v st
      | .f64_copysign => visitor.on_f64_copysign v st
      | .i32_clz => visitor.on_i32_clz v st
      | .i32_ctz => visitor.on_i32_ctz v st
      | .i32_popcnt => visitor.on_i32_popcnt v st
      | .i32_add => visitor.on_i32_add v st
      | .i64_clz => visitor.on_i64_clz v st
      | .i64_ctz => visitor.on_i64_ctz v st
      | .i64_popcnt => visitor.on_i64_popcnt v st
      | .f32_abs => visitor.on_f32_abs v st
      | .f32_neg => visitor.on_f32_neg v st
      | .f32_ceil => visitor.on_f32_ceil v st
      | .f32_floor => visitor.on_f32_floor v st
      | .f32_trunc => visitor.on_f32_trunc v st
      | .f32_nearest => visitor.on_f32_nearest v st
      | .f32_sqrt => visitor.on_f32_sqrt v st
      | .f64_abs => visitor.on_f64_abs v st
      | .f64_neg => visitor.on_f64_neg v st
      | .f64_ceil => visitor.on_f64_ceil v st
      | .f64_floor => visitor.on_f64_floor v st
      | .f64_trunc => visitor.on_f64_trunc v st
      | .f64_nearest => visitor.on_f64_nearest v st
      | .f64_sqrt => visitor.on_f64_sqrt v st
      | .i32_wrap_i64 => visitor.on_i32_wrap_i64 v st
      | .i32_trunc_f32_s => visitor.on_i32_trunc_f32_s v st
      | .i32_trunc_f32_u => visitor.on_i32_trunc_f32_u v st
      | .i32_trunc_f64_s => visitor.on_i32_trunc_f64_s v st
      | .i32_trunc_f64_u => visitor.on_i32_trunc_f64_u v st
      | .i64_extend_i32_s => visitor.on_i64_extend_i32_s v st
      | .i64_extend_i32_u => visitor.on_i64_extend_i32_u v st
      | .i64_trunc_f32_s => visitor.on_i64_trunc_f32_s v st
      | .i64_trunc_f32_u => visitor.on_i64_trunc_f32_u v st
      | .i64_trunc_f64_s => visitor.on_i64_trunc_f64_s v st
      | .i64_trunc_f64_u => visitor.on_i64_trunc_f64_u v st
      | .f32_convert_i32_s => visitor.on_f32_convert_i32_s v st
      | .f32_convert_i32_u => visitor.on_f32_convert_i32_u v st
      | .f32_convert_i64_s => visitor.on_f32_convert_i64_s v st
      | .f32_convert_i64_u => visitor.on_f32_convert_i64_u v st
      | .f32_demote_f64 => visitor.on_f32_demote_f64 v st
      | .f64_convert_i32_s => visitor.on_f64_convert_i32_s v st
      | .f64_convert_i32_u => visitor.on_f64_convert_i32_u v st
      | .f64_convert_i64_s => visitor.on_f64_convert_i64_s v st
      | .f64_convert_i64_u => visitor.on_f64_convert_i64_u v st
      | .f64_promote_f32 => visitor.on_f64_promote_f32 v st
      | .i32_reinterpret_f32 => visitor.on_i32_reinterpret_f32 v st
      | .i64_reinterpret_f64 => visitor.on_i64_reinterpret_f64 v st
      | .f32_reinterpret_i32 => visitor.on_f32_reinterpret_i32 v st
      | .f64_reinterpret_i64 => visitor.on_f64_reinterpret_i64 v st
    | .memory hook arg =>
      match hook with
      | .i32_load => visitor.on_i32_load v st arg
      | .i64_load => visitor.on_i64_load v st arg
      | .f32_load => visitor.on_f32_load v st arg
      | .f64_load => visitor.on_f64_load v st arg
      | .i32_load8_s => visitor.on_i32_load8_s v st arg
      | .i32_load8_u => visitor.on_i32_load8_u v st arg
      | .i32_load16_s => visitor.on_i32_load16_s v st arg
      | .i32_load16_u => visitor.on_i32_load16_u v st arg
      | .i64_load8_s => visitor.on_i64_load8_s v st arg
      | .i64_load8_u => visitor.on_i64_load8_u v st arg
      | .i64_load16_s => visitor.on_i64_load16_s v st arg
      | .i64_load16_u => visitor.on_i64_load16_u v st arg
      | .i64_load32_s => visitor.on_i64_load32_s v st arg
      | .i64_load32_u => visitor.on_i64_load32_u v st arg
      | .i32_store => visitor.on_i32_store v st arg
      | .i64_store => visitor.on_i64_store v st arg
      | .f32_store => visitor.on_f32_store v st arg
      | .f64_store => visitor.on_f64_store v st arg
      | .i32_store8 => visitor.on_i32_store8 v st arg
      | .i32_store16 => visitor.on_i32_store16 v st arg
      | .i64_store8 => visitor.on_i64_store8 v st arg
      | .i64_store16 => visitor.on_i64_store16 v st arg
      | .i64_store32 => visitor.on_i64_store32 v st arg

/-- Build all hooks from one event handler, with hook identities fixed by field names. -/
def ofHandler {V : Type} (handler : V → Event → Result (VisitResult × V)) :
    code.OpVisitor V where
  on_function_start v ctx typeidx bodybegin bodyend :=
    handler v (.functionStart ctx typeidx bodybegin bodyend)
  on_unreachable v st := handler v (.op st (.unreachable))
  on_nop v st := handler v (.op st (.nop))
  on_block v st a0 := handler v (.op st (.block a0))
  on_loop v st a0 := handler v (.op st (.loop a0))
  on_if v st a0 := handler v (.op st (.if_ a0))
  on_else v st a0 := handler v (.op st (.else_ a0))
  on_end v st a0 a1 := handler v (.op st (.end_ a0 a1))
  on_br v st a0 a1 := handler v (.op st (.br a0 a1))
  on_br_if v st a0 a1 := handler v (.op st (.br_if a0 a1))
  on_br_table_label v st a0 := handler v (.op st (.br_table_label a0))
  on_br_table v st a0 a1 := handler v (.op st (.br_table a0 a1))
  on_return v st := handler v (.op st (.return_))
  on_call v st a0 := handler v (.op st (.call a0))
  on_call_indirect v st a0 := handler v (.op st (.call_indirect a0))
  on_drop v st a0 := handler v (.op st (.drop a0))
  on_select v st a0 := handler v (.op st (.select a0))
  on_local_get v st a0 := handler v (.op st (.local_get a0))
  on_local_set v st a0 := handler v (.op st (.local_set a0))
  on_local_tee v st a0 := handler v (.op st (.local_tee a0))
  on_global_get v st a0 := handler v (.op st (.global_get a0))
  on_global_set v st a0 := handler v (.op st (.global_set a0))
  on_memory_size v st := handler v (.op st (.memory_size))
  on_memory_grow v st := handler v (.op st (.memory_grow))
  on_i32_const v st a0 := handler v (.op st (.i32_const a0))
  on_i64_const v st a0 := handler v (.op st (.i64_const a0))
  on_f32_const v st a0 := handler v (.op st (.f32_const a0))
  on_f64_const v st a0 := handler v (.op st (.f64_const a0))
  on_i32_load v st arg := handler v (.op st (.memory .i32_load arg))
  on_i64_load v st arg := handler v (.op st (.memory .i64_load arg))
  on_f32_load v st arg := handler v (.op st (.memory .f32_load arg))
  on_f64_load v st arg := handler v (.op st (.memory .f64_load arg))
  on_i32_load8_s v st arg := handler v (.op st (.memory .i32_load8_s arg))
  on_i32_load8_u v st arg := handler v (.op st (.memory .i32_load8_u arg))
  on_i32_load16_s v st arg := handler v (.op st (.memory .i32_load16_s arg))
  on_i32_load16_u v st arg := handler v (.op st (.memory .i32_load16_u arg))
  on_i64_load8_s v st arg := handler v (.op st (.memory .i64_load8_s arg))
  on_i64_load8_u v st arg := handler v (.op st (.memory .i64_load8_u arg))
  on_i64_load16_s v st arg := handler v (.op st (.memory .i64_load16_s arg))
  on_i64_load16_u v st arg := handler v (.op st (.memory .i64_load16_u arg))
  on_i64_load32_s v st arg := handler v (.op st (.memory .i64_load32_s arg))
  on_i64_load32_u v st arg := handler v (.op st (.memory .i64_load32_u arg))
  on_i32_store v st arg := handler v (.op st (.memory .i32_store arg))
  on_i64_store v st arg := handler v (.op st (.memory .i64_store arg))
  on_f32_store v st arg := handler v (.op st (.memory .f32_store arg))
  on_f64_store v st arg := handler v (.op st (.memory .f64_store arg))
  on_i32_store8 v st arg := handler v (.op st (.memory .i32_store8 arg))
  on_i32_store16 v st arg := handler v (.op st (.memory .i32_store16 arg))
  on_i64_store8 v st arg := handler v (.op st (.memory .i64_store8 arg))
  on_i64_store16 v st arg := handler v (.op st (.memory .i64_store16 arg))
  on_i64_store32 v st arg := handler v (.op st (.memory .i64_store32 arg))
  on_i32_eqz v st := handler v (.op st (.numeric .i32_eqz))
  on_i32_eq v st := handler v (.op st (.numeric .i32_eq))
  on_i32_ne v st := handler v (.op st (.numeric .i32_ne))
  on_i32_lt_s v st := handler v (.op st (.numeric .i32_lt_s))
  on_i32_lt_u v st := handler v (.op st (.numeric .i32_lt_u))
  on_i32_gt_s v st := handler v (.op st (.numeric .i32_gt_s))
  on_i32_gt_u v st := handler v (.op st (.numeric .i32_gt_u))
  on_i32_le_s v st := handler v (.op st (.numeric .i32_le_s))
  on_i32_le_u v st := handler v (.op st (.numeric .i32_le_u))
  on_i32_ge_s v st := handler v (.op st (.numeric .i32_ge_s))
  on_i32_ge_u v st := handler v (.op st (.numeric .i32_ge_u))
  on_i64_eqz v st := handler v (.op st (.numeric .i64_eqz))
  on_i64_eq v st := handler v (.op st (.numeric .i64_eq))
  on_i64_ne v st := handler v (.op st (.numeric .i64_ne))
  on_i64_lt_s v st := handler v (.op st (.numeric .i64_lt_s))
  on_i64_lt_u v st := handler v (.op st (.numeric .i64_lt_u))
  on_i64_gt_s v st := handler v (.op st (.numeric .i64_gt_s))
  on_i64_gt_u v st := handler v (.op st (.numeric .i64_gt_u))
  on_i64_le_s v st := handler v (.op st (.numeric .i64_le_s))
  on_i64_le_u v st := handler v (.op st (.numeric .i64_le_u))
  on_i64_ge_s v st := handler v (.op st (.numeric .i64_ge_s))
  on_i64_ge_u v st := handler v (.op st (.numeric .i64_ge_u))
  on_f32_eq v st := handler v (.op st (.numeric .f32_eq))
  on_f32_ne v st := handler v (.op st (.numeric .f32_ne))
  on_f32_lt v st := handler v (.op st (.numeric .f32_lt))
  on_f32_gt v st := handler v (.op st (.numeric .f32_gt))
  on_f32_le v st := handler v (.op st (.numeric .f32_le))
  on_f32_ge v st := handler v (.op st (.numeric .f32_ge))
  on_f64_eq v st := handler v (.op st (.numeric .f64_eq))
  on_f64_ne v st := handler v (.op st (.numeric .f64_ne))
  on_f64_lt v st := handler v (.op st (.numeric .f64_lt))
  on_f64_gt v st := handler v (.op st (.numeric .f64_gt))
  on_f64_le v st := handler v (.op st (.numeric .f64_le))
  on_f64_ge v st := handler v (.op st (.numeric .f64_ge))
  on_i32_sub v st := handler v (.op st (.numeric .i32_sub))
  on_i32_mul v st := handler v (.op st (.numeric .i32_mul))
  on_i32_div_s v st := handler v (.op st (.numeric .i32_div_s))
  on_i32_div_u v st := handler v (.op st (.numeric .i32_div_u))
  on_i32_rem_s v st := handler v (.op st (.numeric .i32_rem_s))
  on_i32_rem_u v st := handler v (.op st (.numeric .i32_rem_u))
  on_i32_and v st := handler v (.op st (.numeric .i32_and))
  on_i32_or v st := handler v (.op st (.numeric .i32_or))
  on_i32_xor v st := handler v (.op st (.numeric .i32_xor))
  on_i32_shl v st := handler v (.op st (.numeric .i32_shl))
  on_i32_shr_s v st := handler v (.op st (.numeric .i32_shr_s))
  on_i32_shr_u v st := handler v (.op st (.numeric .i32_shr_u))
  on_i32_rotl v st := handler v (.op st (.numeric .i32_rotl))
  on_i32_rotr v st := handler v (.op st (.numeric .i32_rotr))
  on_i64_add v st := handler v (.op st (.numeric .i64_add))
  on_i64_sub v st := handler v (.op st (.numeric .i64_sub))
  on_i64_mul v st := handler v (.op st (.numeric .i64_mul))
  on_i64_div_s v st := handler v (.op st (.numeric .i64_div_s))
  on_i64_div_u v st := handler v (.op st (.numeric .i64_div_u))
  on_i64_rem_s v st := handler v (.op st (.numeric .i64_rem_s))
  on_i64_rem_u v st := handler v (.op st (.numeric .i64_rem_u))
  on_i64_and v st := handler v (.op st (.numeric .i64_and))
  on_i64_or v st := handler v (.op st (.numeric .i64_or))
  on_i64_xor v st := handler v (.op st (.numeric .i64_xor))
  on_i64_shl v st := handler v (.op st (.numeric .i64_shl))
  on_i64_shr_s v st := handler v (.op st (.numeric .i64_shr_s))
  on_i64_shr_u v st := handler v (.op st (.numeric .i64_shr_u))
  on_i64_rotl v st := handler v (.op st (.numeric .i64_rotl))
  on_i64_rotr v st := handler v (.op st (.numeric .i64_rotr))
  on_f32_add v st := handler v (.op st (.numeric .f32_add))
  on_f32_sub v st := handler v (.op st (.numeric .f32_sub))
  on_f32_mul v st := handler v (.op st (.numeric .f32_mul))
  on_f32_div v st := handler v (.op st (.numeric .f32_div))
  on_f32_min v st := handler v (.op st (.numeric .f32_min))
  on_f32_max v st := handler v (.op st (.numeric .f32_max))
  on_f32_copysign v st := handler v (.op st (.numeric .f32_copysign))
  on_f64_add v st := handler v (.op st (.numeric .f64_add))
  on_f64_sub v st := handler v (.op st (.numeric .f64_sub))
  on_f64_mul v st := handler v (.op st (.numeric .f64_mul))
  on_f64_div v st := handler v (.op st (.numeric .f64_div))
  on_f64_min v st := handler v (.op st (.numeric .f64_min))
  on_f64_max v st := handler v (.op st (.numeric .f64_max))
  on_f64_copysign v st := handler v (.op st (.numeric .f64_copysign))
  on_i32_clz v st := handler v (.op st (.numeric .i32_clz))
  on_i32_ctz v st := handler v (.op st (.numeric .i32_ctz))
  on_i32_popcnt v st := handler v (.op st (.numeric .i32_popcnt))
  on_i32_add v st := handler v (.op st (.numeric .i32_add))
  on_i64_clz v st := handler v (.op st (.numeric .i64_clz))
  on_i64_ctz v st := handler v (.op st (.numeric .i64_ctz))
  on_i64_popcnt v st := handler v (.op st (.numeric .i64_popcnt))
  on_f32_abs v st := handler v (.op st (.numeric .f32_abs))
  on_f32_neg v st := handler v (.op st (.numeric .f32_neg))
  on_f32_ceil v st := handler v (.op st (.numeric .f32_ceil))
  on_f32_floor v st := handler v (.op st (.numeric .f32_floor))
  on_f32_trunc v st := handler v (.op st (.numeric .f32_trunc))
  on_f32_nearest v st := handler v (.op st (.numeric .f32_nearest))
  on_f32_sqrt v st := handler v (.op st (.numeric .f32_sqrt))
  on_f64_abs v st := handler v (.op st (.numeric .f64_abs))
  on_f64_neg v st := handler v (.op st (.numeric .f64_neg))
  on_f64_ceil v st := handler v (.op st (.numeric .f64_ceil))
  on_f64_floor v st := handler v (.op st (.numeric .f64_floor))
  on_f64_trunc v st := handler v (.op st (.numeric .f64_trunc))
  on_f64_nearest v st := handler v (.op st (.numeric .f64_nearest))
  on_f64_sqrt v st := handler v (.op st (.numeric .f64_sqrt))
  on_i32_wrap_i64 v st := handler v (.op st (.numeric .i32_wrap_i64))
  on_i32_trunc_f32_s v st := handler v (.op st (.numeric .i32_trunc_f32_s))
  on_i32_trunc_f32_u v st := handler v (.op st (.numeric .i32_trunc_f32_u))
  on_i32_trunc_f64_s v st := handler v (.op st (.numeric .i32_trunc_f64_s))
  on_i32_trunc_f64_u v st := handler v (.op st (.numeric .i32_trunc_f64_u))
  on_i64_extend_i32_s v st := handler v (.op st (.numeric .i64_extend_i32_s))
  on_i64_extend_i32_u v st := handler v (.op st (.numeric .i64_extend_i32_u))
  on_i64_trunc_f32_s v st := handler v (.op st (.numeric .i64_trunc_f32_s))
  on_i64_trunc_f32_u v st := handler v (.op st (.numeric .i64_trunc_f32_u))
  on_i64_trunc_f64_s v st := handler v (.op st (.numeric .i64_trunc_f64_s))
  on_i64_trunc_f64_u v st := handler v (.op st (.numeric .i64_trunc_f64_u))
  on_f32_convert_i32_s v st := handler v (.op st (.numeric .f32_convert_i32_s))
  on_f32_convert_i32_u v st := handler v (.op st (.numeric .f32_convert_i32_u))
  on_f32_convert_i64_s v st := handler v (.op st (.numeric .f32_convert_i64_s))
  on_f32_convert_i64_u v st := handler v (.op st (.numeric .f32_convert_i64_u))
  on_f32_demote_f64 v st := handler v (.op st (.numeric .f32_demote_f64))
  on_f64_convert_i32_s v st := handler v (.op st (.numeric .f64_convert_i32_s))
  on_f64_convert_i32_u v st := handler v (.op st (.numeric .f64_convert_i32_u))
  on_f64_convert_i64_s v st := handler v (.op st (.numeric .f64_convert_i64_s))
  on_f64_convert_i64_u v st := handler v (.op st (.numeric .f64_convert_i64_u))
  on_f64_promote_f32 v st := handler v (.op st (.numeric .f64_promote_f32))
  on_i32_reinterpret_f32 v st := handler v (.op st (.numeric .i32_reinterpret_f32))
  on_i64_reinterpret_f64 v st := handler v (.op st (.numeric .i64_reinterpret_f64))
  on_f32_reinterpret_i32 v st := handler v (.op st (.numeric .f32_reinterpret_i32))
  on_f64_reinterpret_i64 v st := handler v (.op st (.numeric .f64_reinterpret_i64))

/-- Event dispatch and handler construction are exact inverses. -/
@[simp] theorem invoke_ofHandler {V : Type}
    (handler : V → Event → Result (VisitResult × V)) (v : V) (event : Event) :
    invoke (ofHandler handler) v event = handler v event := by
  cases event with
  | functionStart ctx typeidx bodybegin bodyend => rfl
  | op st action =>
    cases action <;> try rfl
    all_goals first | (cases ‹NumericHook› <;> rfl) | (cases ‹MemoryHook› <;> rfl)

end Itasca.VisitorTrace
