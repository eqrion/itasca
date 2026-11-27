import Aeneas
import ItascaRust.Funs
import Itasca.Results.Definitions.Binary
import WebAssembly

/-!
# Callback events and return contracts

Events enumerate every callback and its arguments; invoke identifies the exact extracted
hook. Total and Accepts quantify this vocabulary once, including inputs no particular run
reaches. Total permits ordinary rejection, while Accepts is the stronger premise needed
for completeness. Recording describes the observable sequence of returned calls, including
a final rejection; it does not claim that callbacks terminate unless the appropriate
contract is supplied.

-/

section VisitorEvents

/-!
## Callback observations

Hook classifications, actions, events and state observations describe what each callback means independently of validator dispatch.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor.Trace

/-- The result of a visitor callback: acceptance, or a rejection with a visitor error. -/
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

/-- Wasm 2.0 scalar callback identities: sign extension and saturating truncation. -/
inductive ExtendedNumericHook where
  | i32_extend8_s
  | i32_extend16_s
  | i64_extend8_s
  | i64_extend16_s
  | i64_extend32_s
  | i32_trunc_sat_f32_s
  | i32_trunc_sat_f32_u
  | i32_trunc_sat_f64_s
  | i32_trunc_sat_f64_u
  | i64_trunc_sat_f32_s
  | i64_trunc_sat_f32_u
  | i64_trunc_sat_f64_s
  | i64_trunc_sat_f64_u

/-- The arguments of an instruction hook. Floating-point constants keep every input bit. -/
inductive Action where
  | unreachable
  | nop
  | block (blockType : signature.BlockType) : Action
  | loop (blockType : signature.BlockType) : Action
  | if_ (blockType : signature.BlockType) : Action
  | else_ (blockType : signature.BlockType) : Action
  | end_ (kind : code.LabelKind) (blockType : signature.BlockType) : Action
  | br (depth : U32) (resultTypes : signature.ResultType) : Action
  | br_if (depth : U32) (resultTypes : signature.ResultType) : Action
  | br_table_label (depth : U32) : Action
  | br_table (fallback : U32) (resultTypes : signature.ResultType) : Action
  | return_
  | call (index : U32) : Action
  | call_indirect (typeIndex : U32) (tableIndex : U32) : Action
  | drop (valueType : code.StackType) : Action
  | select (valueType : code.StackType) : Action
  | local_get (index : U32) : Action
  | local_set (index : U32) : Action
  | local_tee (index : U32) : Action
  | global_get (index : U32) : Action
  | global_set (index : U32) : Action
  | memory_size
  | memory_grow
  | i32_const (value : I32) : Action
  | i64_const (value : I64) : Action
  | f32_const (bits : U32) : Action
  | f64_const (bits : U64) : Action
  | numeric (operation : NumericHook) : Action
  | extendedNumeric (operation : ExtendedNumericHook) : Action
  | ref_null (valueType : wasm_types.ElemType) : Action
  | ref_is_null
  | ref_func (index : U32) : Action
  | select_typed (valueType : wasm_types.ValueType) : Action
  | table_get (index : U32) : Action
  | table_set (index : U32) : Action
  | memory_init (dataIndex : U32) : Action
  | data_drop (dataIndex : U32) : Action
  | memory_copy
  | memory_fill
  | table_init (elementIndex : U32) (tableIndex : U32) : Action
  | elem_drop (elementIndex : U32) : Action
  | table_copy (destinationTable : U32) (sourceTable : U32) : Action
  | table_grow (tableIndex : U32) : Action
  | table_size (tableIndex : U32) : Action
  | table_fill (tableIndex : U32) : Action
  | simd (subopcode : U32) : Action
  | simd_lane (subopcode : U32) (lane : U8) : Action
  | simd_memory (subopcode : U32) (argument : code.MemArg) : Action
  | simd_memory_lane (subopcode : U32) (argument : code.MemArg) (lane : U8) : Action
  | simd_const (lowBits : U64) (highBits : U64) : Action
  | simd_shuffle (lowBits : U64) (highBits : U64) : Action
  | memory (operation : MemoryHook) (argument : code.MemArg) : Action

/-- All arguments of a callback, including the validator state the hook observes.
Function-start endpoints are relative to `CodeBatch.code`, excluding locals;
operator-state cursors are relative to that instruction body. -/
inductive Event where
  | functionStart (context : code.Context) (typeIndex : U32) (bodyStart bodyEnd : Usize) : Event
  | op (state : code.OpIterState) (action : Action) : Event

/-- One returned callback, including the callback that rejects a run. -/
structure Observation where
  event : Event
  outcome : VisitResult

/-- Calls the hook that an event names. -/
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
    | .call_indirect a0 a1 => visitor.on_call_indirect v st a0 a1
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
    | .ref_null a0 => visitor.on_ref_null v st a0
    | .ref_is_null => visitor.on_ref_is_null v st
    | .ref_func a0 => visitor.on_ref_func v st a0
    | .select_typed a0 => visitor.on_select_typed v st a0
    | .table_get a0 => visitor.on_table_get v st a0
    | .table_set a0 => visitor.on_table_set v st a0
    | .memory_init a0 => visitor.on_memory_init v st a0
    | .data_drop a0 => visitor.on_data_drop v st a0
    | .memory_copy => visitor.on_memory_copy v st
    | .memory_fill => visitor.on_memory_fill v st
    | .table_init a0 a1 => visitor.on_table_init v st a0 a1
    | .elem_drop a0 => visitor.on_elem_drop v st a0
    | .table_copy a0 a1 => visitor.on_table_copy v st a0 a1
    | .table_grow a0 => visitor.on_table_grow v st a0
    | .table_size a0 => visitor.on_table_size v st a0
    | .table_fill a0 => visitor.on_table_fill v st a0
    | .simd a0 => visitor.on_simd v st a0
    | .simd_lane a0 a1 => visitor.on_simd_lane v st a0 a1
    | .simd_memory a0 a1 => visitor.on_simd_memory v st a0 a1
    | .simd_memory_lane a0 a1 a2 => visitor.on_simd_memory_lane v st a0 a1 a2
    | .simd_const a0 a1 => visitor.on_simd_const v st a0 a1
    | .simd_shuffle a0 a1 => visitor.on_simd_shuffle v st a0 a1
    | .extendedNumeric hook =>
      match hook with
      | .i32_extend8_s => visitor.on_i32_extend8_s v st
      | .i32_extend16_s => visitor.on_i32_extend16_s v st
      | .i64_extend8_s => visitor.on_i64_extend8_s v st
      | .i64_extend16_s => visitor.on_i64_extend16_s v st
      | .i64_extend32_s => visitor.on_i64_extend32_s v st
      | .i32_trunc_sat_f32_s => visitor.on_i32_trunc_sat_f32_s v st
      | .i32_trunc_sat_f32_u => visitor.on_i32_trunc_sat_f32_u v st
      | .i32_trunc_sat_f64_s => visitor.on_i32_trunc_sat_f64_s v st
      | .i32_trunc_sat_f64_u => visitor.on_i32_trunc_sat_f64_u v st
      | .i64_trunc_sat_f32_s => visitor.on_i64_trunc_sat_f32_s v st
      | .i64_trunc_sat_f32_u => visitor.on_i64_trunc_sat_f32_u v st
      | .i64_trunc_sat_f64_s => visitor.on_i64_trunc_sat_f64_s v st
      | .i64_trunc_sat_f64_u => visitor.on_i64_trunc_sat_f64_u v st
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

end Itasca.Visitor.Trace

end VisitorEvents

section VisitorBodyReplay

/-!
## Returning callback runs

Body results, accepted outcomes, label positions and partial branch tables describe replay of actual callback-bearing validation computations.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor.Trace

/-- The result of validating an instruction or a body. -/
abbrev BodyResult := core.result.Result Unit error.OpError

/-- Every observation in the list was accepted. -/
def AllAccepted (observations : List Observation) : Prop :=
  ∀ observation ∈ observations, observation.outcome = .Ok ()

/-- The observations are consistent with a result. A success has only accepted callbacks. A visitor
error is either the reply of a rejecting last callback that follows accepted ones, or follows only
accepted callbacks. Any other error follows only accepted callbacks. -/
def Outcomes (observations : List Observation) : BodyResult → Prop
  | .Ok () => AllAccepted observations
  | .Err (.Visitor e) => AllAccepted observations ∨ ∃ before event,
      observations = before ++ [⟨event, .Err e⟩] ∧ AllAccepted before
  | .Err _ => AllAccepted observations

/-- The observations of the `br_table` vector entries, with their label depths in order and the
byte cursor after each entry. The relation is defined by the binary encoding alone. -/
inductive LabelsAt (data : Slice U8) : Usize → List Observation → List U32 → Usize → Prop where
  | nil (pos : Usize) : LabelsAt data pos [] [] pos
  | cons {pos depth st reply observations depths last} :
      Binary.Leb128.Decoded data pos depth st.pos →
      LabelsAt data st.pos observations depths last →
      LabelsAt data pos (⟨.op st (.br_table_label depth), reply⟩ :: observations)
        (depth :: depths) last

/-- The callbacks of a `br_table` that stopped before its closing callback. They cover some or all
of the vector entries, including an entry whose target merge failed after its callback ran. -/
def PartialTable (data : Slice U8) (start : Usize) (observations : List Observation) : Prop :=
  ∃ pos count first depths last,
    Body.Scalar.BytesAt data start [0x0E#u8] pos ∧
    Binary.Leb128.Decoded data pos count first ∧
    LabelsAt data first observations depths last ∧ depths.length ≤ count.val

end Itasca.Visitor.Trace

end VisitorBodyReplay

section VisitorContracts

/-!
## Callback return contracts

The event vocabulary lists every callback and all of its arguments. Quantifying
an event therefore quantifies all callback inputs, including inputs no particular
validation run reaches. `Trace.invoke` is the explicit dispatcher from an event
to the corresponding extracted callback; it is shared with trace recording.

`Total` excludes modeled divergence and panic but permits ordinary visitor
rejection. `Accepts` additionally excludes rejection, as required for completeness.
Neither contract requires the visitor's state to remain unchanged.
-/

namespace Itasca.Visitor

/-- Every callback returns normally, possibly rejecting the input. -/
def Total {V : Type} (visitor : code.OpVisitor V) : Prop :=
  ∀ state event, ∃ reply nextState, Trace.invoke visitor state event = .ok (reply, nextState)

/-- Every callback returns successfully. The resulting visitor state is unrestricted. -/
def Accepts {V : Type} (visitor : code.OpVisitor V) : Prop :=
  ∀ state event, ∃ nextState, Trace.invoke visitor state event = .ok (.Ok (), nextState)

end Itasca.Visitor

end VisitorContracts

section VisitorRunTrace

/-!
## Operator recording

`Records` states that each returning callback appends its event and reply to the
observed log. It does not prescribe a recorder implementation. Logging adapters
and their construction proofs live in Visitor/Events and Visitor/RunTrace.
-/

open Aeneas Aeneas.Std

namespace Itasca.Visitor.Trace

/-- Every callback of the visitor that returns normally appends exactly its event and reply to the
observed log, including a rejection. -/
def Records {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) : Prop :=
  ∀ v event reply v', invoke visitor v event = .ok (reply, v') →
    observe v' = observe v ++ [⟨event, reply⟩]

end Itasca.Visitor.Trace

end VisitorRunTrace
