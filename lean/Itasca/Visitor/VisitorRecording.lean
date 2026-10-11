import Itasca.Support.Result
import Itasca.Visitor.VisitorEvents
import Itasca.Visitor.FullVisitorAccept
import Itasca.Visitor.VisitorErasure

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

/-- Every returned callback appends exactly its event and outcome, including rejection. -/
def Records {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) : Prop :=
  ∀ v event reply v', invoke visitor v event = .ok (reply, v') →
    observe v' = observe v ++ [⟨event, reply⟩]

/-- Add a returned callback to a log, preserving the wrapped visitor's result and state. -/
def record {V : Type} (log : List Observation) (event : Event)
    (action : Result (VisitResult × V)) : Result (VisitResult × (V × List Observation)) := do
  let (reply, v') ← action
  .ok (reply, (v', log ++ [⟨event, reply⟩]))

@[simp] theorem record_ok {V : Type} (log : List Observation) (event : Event)
    (reply : VisitResult) (v' : V) :
    record log event (.ok (reply, v')) = .ok (reply, (v', log ++ [⟨event, reply⟩])) := by
  simp [record]

theorem record_ok_iff {V : Type} (log : List Observation) (event : Event)
    (action : Result (VisitResult × V)) (reply : VisitResult) (v' : V)
    (log' : List Observation) :
    record log event action = .ok (reply, (v', log')) ↔
      action = .ok (reply, v') ∧ log' = log ++ [⟨event, reply⟩] := by
  constructor
  · intro h
    unfold record at h
    obtain ⟨⟨r, w⟩, ha, hb⟩ := ResultFacts.bind_ok_inv _ _ _ h
    simp at hb
    rcases hb with ⟨rfl, rfl, rfl⟩
    exact ⟨ha, rfl⟩
  · rintro ⟨h, rfl⟩
    simp [h]

/-- Instrument an arbitrary visitor; the underlying visitor still decides every outcome. -/
def instrument {V : Type} (visitor : code.OpVisitor V) :
    code.OpVisitor (V × List Observation) :=
  ofHandler fun state event => record state.2 event (invoke visitor state.1 event)

@[simp] theorem invoke_instrument {V : Type} (visitor : code.OpVisitor V)
    (v : V) (log : List Observation) (event : Event) :
    invoke (instrument visitor) (v, log) event = record log event (invoke visitor v event) := by
  simp [instrument]

theorem instrument_records {V : Type} (visitor : code.OpVisitor V) :
    Records (instrument visitor) Prod.snd := by
  rintro ⟨v, log⟩ event reply ⟨v', log'⟩ h
  exact ((record_ok_iff log event _ reply v' log').mp (by simpa using h)).2

theorem total_invoke {V : Type} {visitor : code.OpVisitor V}
    (h : FullVisitor.Total visitor) (v : V) (event : Event) :
    ∃ reply v', invoke visitor v event = .ok (reply, v') := by
  cases event with
  | functionStart ctx idx first last => exact h.on_function_start v ctx idx first last
  | op st action =>
    cases action with
    | unreachable => exact h.on_unreachable v st
    | nop => exact h.on_nop v st
    | block a0 => exact h.on_block v st a0
    | loop a0 => exact h.on_loop v st a0
    | if_ a0 => exact h.on_if v st a0
    | else_ a0 => exact h.on_else v st a0
    | end_ a0 a1 => exact h.on_end v st a0 a1
    | br a0 a1 => exact h.on_br v st a0 a1
    | br_if a0 a1 => exact h.on_br_if v st a0 a1
    | br_table_label a0 => exact h.on_br_table_label v st a0
    | br_table a0 a1 => exact h.on_br_table v st a0 a1
    | return_ => exact h.on_return v st
    | call a0 => exact h.on_call v st a0
    | call_indirect a0 a1 => exact h.on_call_indirect v st a0 a1
    | drop a0 => exact h.on_drop v st a0
    | select a0 => exact h.on_select v st a0
    | local_get a0 => exact h.on_local_get v st a0
    | local_set a0 => exact h.on_local_set v st a0
    | local_tee a0 => exact h.on_local_tee v st a0
    | global_get a0 => exact h.on_global_get v st a0
    | global_set a0 => exact h.on_global_set v st a0
    | memory_size => exact h.on_memory_size v st
    | memory_grow => exact h.on_memory_grow v st
    | i32_const a0 => exact h.on_i32_const v st a0
    | i64_const a0 => exact h.on_i64_const v st a0
    | f32_const a0 => exact h.on_f32_const v st a0
    | f64_const a0 => exact h.on_f64_const v st a0
    | ref_null a0 => exact h.on_ref_null v st a0
    | ref_is_null => exact h.on_ref_is_null v st
    | ref_func a0 => exact h.on_ref_func v st a0
    | select_typed a0 => exact h.on_select_typed v st a0
    | table_get a0 => exact h.on_table_get v st a0
    | table_set a0 => exact h.on_table_set v st a0
    | memory_init a0 => exact h.on_memory_init v st a0
    | data_drop a0 => exact h.on_data_drop v st a0
    | memory_copy => exact h.on_memory_copy v st
    | memory_fill => exact h.on_memory_fill v st
    | table_init a0 a1 => exact h.on_table_init v st a0 a1
    | elem_drop a0 => exact h.on_elem_drop v st a0
    | table_copy a0 a1 => exact h.on_table_copy v st a0 a1
    | table_grow a0 => exact h.on_table_grow v st a0
    | table_size a0 => exact h.on_table_size v st a0
    | table_fill a0 => exact h.on_table_fill v st a0
    | simd a0 => exact h.on_simd v st a0
    | simd_lane a0 a1 => exact h.on_simd_lane v st a0 a1
    | simd_memory a0 a1 => exact h.on_simd_memory v st a0 a1
    | simd_memory_lane a0 a1 a2 => exact h.on_simd_memory_lane v st a0 a1 a2
    | simd_const a0 a1 => exact h.on_simd_const v st a0 a1
    | simd_shuffle a0 a1 => exact h.on_simd_shuffle v st a0 a1
    | extendedNumeric hook =>
      cases hook with
      | i32_extend8_s => exact h.on_i32_extend8_s v st
      | i32_extend16_s => exact h.on_i32_extend16_s v st
      | i64_extend8_s => exact h.on_i64_extend8_s v st
      | i64_extend16_s => exact h.on_i64_extend16_s v st
      | i64_extend32_s => exact h.on_i64_extend32_s v st
      | i32_trunc_sat_f32_s => exact h.on_i32_trunc_sat_f32_s v st
      | i32_trunc_sat_f32_u => exact h.on_i32_trunc_sat_f32_u v st
      | i32_trunc_sat_f64_s => exact h.on_i32_trunc_sat_f64_s v st
      | i32_trunc_sat_f64_u => exact h.on_i32_trunc_sat_f64_u v st
      | i64_trunc_sat_f32_s => exact h.on_i64_trunc_sat_f32_s v st
      | i64_trunc_sat_f32_u => exact h.on_i64_trunc_sat_f32_u v st
      | i64_trunc_sat_f64_s => exact h.on_i64_trunc_sat_f64_s v st
      | i64_trunc_sat_f64_u => exact h.on_i64_trunc_sat_f64_u v st
    | numeric hook =>
      cases hook with
      | i32_eqz => exact h.on_i32_eqz v st
      | i32_eq => exact h.on_i32_eq v st
      | i32_ne => exact h.on_i32_ne v st
      | i32_lt_s => exact h.on_i32_lt_s v st
      | i32_lt_u => exact h.on_i32_lt_u v st
      | i32_gt_s => exact h.on_i32_gt_s v st
      | i32_gt_u => exact h.on_i32_gt_u v st
      | i32_le_s => exact h.on_i32_le_s v st
      | i32_le_u => exact h.on_i32_le_u v st
      | i32_ge_s => exact h.on_i32_ge_s v st
      | i32_ge_u => exact h.on_i32_ge_u v st
      | i64_eqz => exact h.on_i64_eqz v st
      | i64_eq => exact h.on_i64_eq v st
      | i64_ne => exact h.on_i64_ne v st
      | i64_lt_s => exact h.on_i64_lt_s v st
      | i64_lt_u => exact h.on_i64_lt_u v st
      | i64_gt_s => exact h.on_i64_gt_s v st
      | i64_gt_u => exact h.on_i64_gt_u v st
      | i64_le_s => exact h.on_i64_le_s v st
      | i64_le_u => exact h.on_i64_le_u v st
      | i64_ge_s => exact h.on_i64_ge_s v st
      | i64_ge_u => exact h.on_i64_ge_u v st
      | f32_eq => exact h.on_f32_eq v st
      | f32_ne => exact h.on_f32_ne v st
      | f32_lt => exact h.on_f32_lt v st
      | f32_gt => exact h.on_f32_gt v st
      | f32_le => exact h.on_f32_le v st
      | f32_ge => exact h.on_f32_ge v st
      | f64_eq => exact h.on_f64_eq v st
      | f64_ne => exact h.on_f64_ne v st
      | f64_lt => exact h.on_f64_lt v st
      | f64_gt => exact h.on_f64_gt v st
      | f64_le => exact h.on_f64_le v st
      | f64_ge => exact h.on_f64_ge v st
      | i32_sub => exact h.on_i32_sub v st
      | i32_mul => exact h.on_i32_mul v st
      | i32_div_s => exact h.on_i32_div_s v st
      | i32_div_u => exact h.on_i32_div_u v st
      | i32_rem_s => exact h.on_i32_rem_s v st
      | i32_rem_u => exact h.on_i32_rem_u v st
      | i32_and => exact h.on_i32_and v st
      | i32_or => exact h.on_i32_or v st
      | i32_xor => exact h.on_i32_xor v st
      | i32_shl => exact h.on_i32_shl v st
      | i32_shr_s => exact h.on_i32_shr_s v st
      | i32_shr_u => exact h.on_i32_shr_u v st
      | i32_rotl => exact h.on_i32_rotl v st
      | i32_rotr => exact h.on_i32_rotr v st
      | i64_add => exact h.on_i64_add v st
      | i64_sub => exact h.on_i64_sub v st
      | i64_mul => exact h.on_i64_mul v st
      | i64_div_s => exact h.on_i64_div_s v st
      | i64_div_u => exact h.on_i64_div_u v st
      | i64_rem_s => exact h.on_i64_rem_s v st
      | i64_rem_u => exact h.on_i64_rem_u v st
      | i64_and => exact h.on_i64_and v st
      | i64_or => exact h.on_i64_or v st
      | i64_xor => exact h.on_i64_xor v st
      | i64_shl => exact h.on_i64_shl v st
      | i64_shr_s => exact h.on_i64_shr_s v st
      | i64_shr_u => exact h.on_i64_shr_u v st
      | i64_rotl => exact h.on_i64_rotl v st
      | i64_rotr => exact h.on_i64_rotr v st
      | f32_add => exact h.on_f32_add v st
      | f32_sub => exact h.on_f32_sub v st
      | f32_mul => exact h.on_f32_mul v st
      | f32_div => exact h.on_f32_div v st
      | f32_min => exact h.on_f32_min v st
      | f32_max => exact h.on_f32_max v st
      | f32_copysign => exact h.on_f32_copysign v st
      | f64_add => exact h.on_f64_add v st
      | f64_sub => exact h.on_f64_sub v st
      | f64_mul => exact h.on_f64_mul v st
      | f64_div => exact h.on_f64_div v st
      | f64_min => exact h.on_f64_min v st
      | f64_max => exact h.on_f64_max v st
      | f64_copysign => exact h.on_f64_copysign v st
      | i32_clz => exact h.on_i32_clz v st
      | i32_ctz => exact h.on_i32_ctz v st
      | i32_popcnt => exact h.on_i32_popcnt v st
      | i32_add => exact h.on_i32_add v st
      | i64_clz => exact h.on_i64_clz v st
      | i64_ctz => exact h.on_i64_ctz v st
      | i64_popcnt => exact h.on_i64_popcnt v st
      | f32_abs => exact h.on_f32_abs v st
      | f32_neg => exact h.on_f32_neg v st
      | f32_ceil => exact h.on_f32_ceil v st
      | f32_floor => exact h.on_f32_floor v st
      | f32_trunc => exact h.on_f32_trunc v st
      | f32_nearest => exact h.on_f32_nearest v st
      | f32_sqrt => exact h.on_f32_sqrt v st
      | f64_abs => exact h.on_f64_abs v st
      | f64_neg => exact h.on_f64_neg v st
      | f64_ceil => exact h.on_f64_ceil v st
      | f64_floor => exact h.on_f64_floor v st
      | f64_trunc => exact h.on_f64_trunc v st
      | f64_nearest => exact h.on_f64_nearest v st
      | f64_sqrt => exact h.on_f64_sqrt v st
      | i32_wrap_i64 => exact h.on_i32_wrap_i64 v st
      | i32_trunc_f32_s => exact h.on_i32_trunc_f32_s v st
      | i32_trunc_f32_u => exact h.on_i32_trunc_f32_u v st
      | i32_trunc_f64_s => exact h.on_i32_trunc_f64_s v st
      | i32_trunc_f64_u => exact h.on_i32_trunc_f64_u v st
      | i64_extend_i32_s => exact h.on_i64_extend_i32_s v st
      | i64_extend_i32_u => exact h.on_i64_extend_i32_u v st
      | i64_trunc_f32_s => exact h.on_i64_trunc_f32_s v st
      | i64_trunc_f32_u => exact h.on_i64_trunc_f32_u v st
      | i64_trunc_f64_s => exact h.on_i64_trunc_f64_s v st
      | i64_trunc_f64_u => exact h.on_i64_trunc_f64_u v st
      | f32_convert_i32_s => exact h.on_f32_convert_i32_s v st
      | f32_convert_i32_u => exact h.on_f32_convert_i32_u v st
      | f32_convert_i64_s => exact h.on_f32_convert_i64_s v st
      | f32_convert_i64_u => exact h.on_f32_convert_i64_u v st
      | f32_demote_f64 => exact h.on_f32_demote_f64 v st
      | f64_convert_i32_s => exact h.on_f64_convert_i32_s v st
      | f64_convert_i32_u => exact h.on_f64_convert_i32_u v st
      | f64_convert_i64_s => exact h.on_f64_convert_i64_s v st
      | f64_convert_i64_u => exact h.on_f64_convert_i64_u v st
      | f64_promote_f32 => exact h.on_f64_promote_f32 v st
      | i32_reinterpret_f32 => exact h.on_i32_reinterpret_f32 v st
      | i64_reinterpret_f64 => exact h.on_i64_reinterpret_f64 v st
      | f32_reinterpret_i32 => exact h.on_f32_reinterpret_i32 v st
      | f64_reinterpret_i64 => exact h.on_f64_reinterpret_i64 v st
    | memory hook arg =>
      cases hook with
      | i32_load => exact h.on_i32_load v st arg
      | i64_load => exact h.on_i64_load v st arg
      | f32_load => exact h.on_f32_load v st arg
      | f64_load => exact h.on_f64_load v st arg
      | i32_load8_s => exact h.on_i32_load8_s v st arg
      | i32_load8_u => exact h.on_i32_load8_u v st arg
      | i32_load16_s => exact h.on_i32_load16_s v st arg
      | i32_load16_u => exact h.on_i32_load16_u v st arg
      | i64_load8_s => exact h.on_i64_load8_s v st arg
      | i64_load8_u => exact h.on_i64_load8_u v st arg
      | i64_load16_s => exact h.on_i64_load16_s v st arg
      | i64_load16_u => exact h.on_i64_load16_u v st arg
      | i64_load32_s => exact h.on_i64_load32_s v st arg
      | i64_load32_u => exact h.on_i64_load32_u v st arg
      | i32_store => exact h.on_i32_store v st arg
      | i64_store => exact h.on_i64_store v st arg
      | f32_store => exact h.on_f32_store v st arg
      | f64_store => exact h.on_f64_store v st arg
      | i32_store8 => exact h.on_i32_store8 v st arg
      | i32_store16 => exact h.on_i32_store16 v st arg
      | i64_store8 => exact h.on_i64_store8 v st arg
      | i64_store16 => exact h.on_i64_store16 v st arg
      | i64_store32 => exact h.on_i64_store32 v st arg

theorem accepts_invoke {V : Type} {visitor : code.OpVisitor V}
    (h : FullVisitor.Accepts visitor) (v : V) (event : Event) :
    ∃ v', invoke visitor v event = .ok (.Ok (), v') := by
  cases event with
  | functionStart ctx idx first last => exact h.on_function_start v ctx idx first last
  | op st action =>
    cases action with
    | unreachable => exact h.on_unreachable v st
    | nop => exact h.on_nop v st
    | block a0 => exact h.on_block v st a0
    | loop a0 => exact h.on_loop v st a0
    | if_ a0 => exact h.on_if v st a0
    | else_ a0 => exact h.on_else v st a0
    | end_ a0 a1 => exact h.on_end v st a0 a1
    | br a0 a1 => exact h.on_br v st a0 a1
    | br_if a0 a1 => exact h.on_br_if v st a0 a1
    | br_table_label a0 => exact h.on_br_table_label v st a0
    | br_table a0 a1 => exact h.on_br_table v st a0 a1
    | return_ => exact h.on_return v st
    | call a0 => exact h.on_call v st a0
    | call_indirect a0 a1 => exact h.on_call_indirect v st a0 a1
    | drop a0 => exact h.on_drop v st a0
    | select a0 => exact h.on_select v st a0
    | local_get a0 => exact h.on_local_get v st a0
    | local_set a0 => exact h.on_local_set v st a0
    | local_tee a0 => exact h.on_local_tee v st a0
    | global_get a0 => exact h.on_global_get v st a0
    | global_set a0 => exact h.on_global_set v st a0
    | memory_size => exact h.on_memory_size v st
    | memory_grow => exact h.on_memory_grow v st
    | i32_const a0 => exact h.on_i32_const v st a0
    | i64_const a0 => exact h.on_i64_const v st a0
    | f32_const a0 => exact h.on_f32_const v st a0
    | f64_const a0 => exact h.on_f64_const v st a0
    | ref_null a0 => exact h.on_ref_null v st a0
    | ref_is_null => exact h.on_ref_is_null v st
    | ref_func a0 => exact h.on_ref_func v st a0
    | select_typed a0 => exact h.on_select_typed v st a0
    | table_get a0 => exact h.on_table_get v st a0
    | table_set a0 => exact h.on_table_set v st a0
    | memory_init a0 => exact h.on_memory_init v st a0
    | data_drop a0 => exact h.on_data_drop v st a0
    | memory_copy => exact h.on_memory_copy v st
    | memory_fill => exact h.on_memory_fill v st
    | table_init a0 a1 => exact h.on_table_init v st a0 a1
    | elem_drop a0 => exact h.on_elem_drop v st a0
    | table_copy a0 a1 => exact h.on_table_copy v st a0 a1
    | table_grow a0 => exact h.on_table_grow v st a0
    | table_size a0 => exact h.on_table_size v st a0
    | table_fill a0 => exact h.on_table_fill v st a0
    | simd a0 => exact h.on_simd v st a0
    | simd_lane a0 a1 => exact h.on_simd_lane v st a0 a1
    | simd_memory a0 a1 => exact h.on_simd_memory v st a0 a1
    | simd_memory_lane a0 a1 a2 => exact h.on_simd_memory_lane v st a0 a1 a2
    | simd_const a0 a1 => exact h.on_simd_const v st a0 a1
    | simd_shuffle a0 a1 => exact h.on_simd_shuffle v st a0 a1
    | extendedNumeric hook =>
      cases hook with
      | i32_extend8_s => exact h.on_i32_extend8_s v st
      | i32_extend16_s => exact h.on_i32_extend16_s v st
      | i64_extend8_s => exact h.on_i64_extend8_s v st
      | i64_extend16_s => exact h.on_i64_extend16_s v st
      | i64_extend32_s => exact h.on_i64_extend32_s v st
      | i32_trunc_sat_f32_s => exact h.on_i32_trunc_sat_f32_s v st
      | i32_trunc_sat_f32_u => exact h.on_i32_trunc_sat_f32_u v st
      | i32_trunc_sat_f64_s => exact h.on_i32_trunc_sat_f64_s v st
      | i32_trunc_sat_f64_u => exact h.on_i32_trunc_sat_f64_u v st
      | i64_trunc_sat_f32_s => exact h.on_i64_trunc_sat_f32_s v st
      | i64_trunc_sat_f32_u => exact h.on_i64_trunc_sat_f32_u v st
      | i64_trunc_sat_f64_s => exact h.on_i64_trunc_sat_f64_s v st
      | i64_trunc_sat_f64_u => exact h.on_i64_trunc_sat_f64_u v st
    | numeric hook =>
      cases hook with
      | i32_eqz => exact h.on_i32_eqz v st
      | i32_eq => exact h.on_i32_eq v st
      | i32_ne => exact h.on_i32_ne v st
      | i32_lt_s => exact h.on_i32_lt_s v st
      | i32_lt_u => exact h.on_i32_lt_u v st
      | i32_gt_s => exact h.on_i32_gt_s v st
      | i32_gt_u => exact h.on_i32_gt_u v st
      | i32_le_s => exact h.on_i32_le_s v st
      | i32_le_u => exact h.on_i32_le_u v st
      | i32_ge_s => exact h.on_i32_ge_s v st
      | i32_ge_u => exact h.on_i32_ge_u v st
      | i64_eqz => exact h.on_i64_eqz v st
      | i64_eq => exact h.on_i64_eq v st
      | i64_ne => exact h.on_i64_ne v st
      | i64_lt_s => exact h.on_i64_lt_s v st
      | i64_lt_u => exact h.on_i64_lt_u v st
      | i64_gt_s => exact h.on_i64_gt_s v st
      | i64_gt_u => exact h.on_i64_gt_u v st
      | i64_le_s => exact h.on_i64_le_s v st
      | i64_le_u => exact h.on_i64_le_u v st
      | i64_ge_s => exact h.on_i64_ge_s v st
      | i64_ge_u => exact h.on_i64_ge_u v st
      | f32_eq => exact h.on_f32_eq v st
      | f32_ne => exact h.on_f32_ne v st
      | f32_lt => exact h.on_f32_lt v st
      | f32_gt => exact h.on_f32_gt v st
      | f32_le => exact h.on_f32_le v st
      | f32_ge => exact h.on_f32_ge v st
      | f64_eq => exact h.on_f64_eq v st
      | f64_ne => exact h.on_f64_ne v st
      | f64_lt => exact h.on_f64_lt v st
      | f64_gt => exact h.on_f64_gt v st
      | f64_le => exact h.on_f64_le v st
      | f64_ge => exact h.on_f64_ge v st
      | i32_sub => exact h.on_i32_sub v st
      | i32_mul => exact h.on_i32_mul v st
      | i32_div_s => exact h.on_i32_div_s v st
      | i32_div_u => exact h.on_i32_div_u v st
      | i32_rem_s => exact h.on_i32_rem_s v st
      | i32_rem_u => exact h.on_i32_rem_u v st
      | i32_and => exact h.on_i32_and v st
      | i32_or => exact h.on_i32_or v st
      | i32_xor => exact h.on_i32_xor v st
      | i32_shl => exact h.on_i32_shl v st
      | i32_shr_s => exact h.on_i32_shr_s v st
      | i32_shr_u => exact h.on_i32_shr_u v st
      | i32_rotl => exact h.on_i32_rotl v st
      | i32_rotr => exact h.on_i32_rotr v st
      | i64_add => exact h.on_i64_add v st
      | i64_sub => exact h.on_i64_sub v st
      | i64_mul => exact h.on_i64_mul v st
      | i64_div_s => exact h.on_i64_div_s v st
      | i64_div_u => exact h.on_i64_div_u v st
      | i64_rem_s => exact h.on_i64_rem_s v st
      | i64_rem_u => exact h.on_i64_rem_u v st
      | i64_and => exact h.on_i64_and v st
      | i64_or => exact h.on_i64_or v st
      | i64_xor => exact h.on_i64_xor v st
      | i64_shl => exact h.on_i64_shl v st
      | i64_shr_s => exact h.on_i64_shr_s v st
      | i64_shr_u => exact h.on_i64_shr_u v st
      | i64_rotl => exact h.on_i64_rotl v st
      | i64_rotr => exact h.on_i64_rotr v st
      | f32_add => exact h.on_f32_add v st
      | f32_sub => exact h.on_f32_sub v st
      | f32_mul => exact h.on_f32_mul v st
      | f32_div => exact h.on_f32_div v st
      | f32_min => exact h.on_f32_min v st
      | f32_max => exact h.on_f32_max v st
      | f32_copysign => exact h.on_f32_copysign v st
      | f64_add => exact h.on_f64_add v st
      | f64_sub => exact h.on_f64_sub v st
      | f64_mul => exact h.on_f64_mul v st
      | f64_div => exact h.on_f64_div v st
      | f64_min => exact h.on_f64_min v st
      | f64_max => exact h.on_f64_max v st
      | f64_copysign => exact h.on_f64_copysign v st
      | i32_clz => exact h.on_i32_clz v st
      | i32_ctz => exact h.on_i32_ctz v st
      | i32_popcnt => exact h.on_i32_popcnt v st
      | i32_add => exact h.on_i32_add v st
      | i64_clz => exact h.on_i64_clz v st
      | i64_ctz => exact h.on_i64_ctz v st
      | i64_popcnt => exact h.on_i64_popcnt v st
      | f32_abs => exact h.on_f32_abs v st
      | f32_neg => exact h.on_f32_neg v st
      | f32_ceil => exact h.on_f32_ceil v st
      | f32_floor => exact h.on_f32_floor v st
      | f32_trunc => exact h.on_f32_trunc v st
      | f32_nearest => exact h.on_f32_nearest v st
      | f32_sqrt => exact h.on_f32_sqrt v st
      | f64_abs => exact h.on_f64_abs v st
      | f64_neg => exact h.on_f64_neg v st
      | f64_ceil => exact h.on_f64_ceil v st
      | f64_floor => exact h.on_f64_floor v st
      | f64_trunc => exact h.on_f64_trunc v st
      | f64_nearest => exact h.on_f64_nearest v st
      | f64_sqrt => exact h.on_f64_sqrt v st
      | i32_wrap_i64 => exact h.on_i32_wrap_i64 v st
      | i32_trunc_f32_s => exact h.on_i32_trunc_f32_s v st
      | i32_trunc_f32_u => exact h.on_i32_trunc_f32_u v st
      | i32_trunc_f64_s => exact h.on_i32_trunc_f64_s v st
      | i32_trunc_f64_u => exact h.on_i32_trunc_f64_u v st
      | i64_extend_i32_s => exact h.on_i64_extend_i32_s v st
      | i64_extend_i32_u => exact h.on_i64_extend_i32_u v st
      | i64_trunc_f32_s => exact h.on_i64_trunc_f32_s v st
      | i64_trunc_f32_u => exact h.on_i64_trunc_f32_u v st
      | i64_trunc_f64_s => exact h.on_i64_trunc_f64_s v st
      | i64_trunc_f64_u => exact h.on_i64_trunc_f64_u v st
      | f32_convert_i32_s => exact h.on_f32_convert_i32_s v st
      | f32_convert_i32_u => exact h.on_f32_convert_i32_u v st
      | f32_convert_i64_s => exact h.on_f32_convert_i64_s v st
      | f32_convert_i64_u => exact h.on_f32_convert_i64_u v st
      | f32_demote_f64 => exact h.on_f32_demote_f64 v st
      | f64_convert_i32_s => exact h.on_f64_convert_i32_s v st
      | f64_convert_i32_u => exact h.on_f64_convert_i32_u v st
      | f64_convert_i64_s => exact h.on_f64_convert_i64_s v st
      | f64_convert_i64_u => exact h.on_f64_convert_i64_u v st
      | f64_promote_f32 => exact h.on_f64_promote_f32 v st
      | i32_reinterpret_f32 => exact h.on_i32_reinterpret_f32 v st
      | i64_reinterpret_f64 => exact h.on_i64_reinterpret_f64 v st
      | f32_reinterpret_i32 => exact h.on_f32_reinterpret_i32 v st
      | f64_reinterpret_i64 => exact h.on_f64_reinterpret_i64 v st
    | memory hook arg =>
      cases hook with
      | i32_load => exact h.on_i32_load v st arg
      | i64_load => exact h.on_i64_load v st arg
      | f32_load => exact h.on_f32_load v st arg
      | f64_load => exact h.on_f64_load v st arg
      | i32_load8_s => exact h.on_i32_load8_s v st arg
      | i32_load8_u => exact h.on_i32_load8_u v st arg
      | i32_load16_s => exact h.on_i32_load16_s v st arg
      | i32_load16_u => exact h.on_i32_load16_u v st arg
      | i64_load8_s => exact h.on_i64_load8_s v st arg
      | i64_load8_u => exact h.on_i64_load8_u v st arg
      | i64_load16_s => exact h.on_i64_load16_s v st arg
      | i64_load16_u => exact h.on_i64_load16_u v st arg
      | i64_load32_s => exact h.on_i64_load32_s v st arg
      | i64_load32_u => exact h.on_i64_load32_u v st arg
      | i32_store => exact h.on_i32_store v st arg
      | i64_store => exact h.on_i64_store v st arg
      | f32_store => exact h.on_f32_store v st arg
      | f64_store => exact h.on_f64_store v st arg
      | i32_store8 => exact h.on_i32_store8 v st arg
      | i32_store16 => exact h.on_i32_store16 v st arg
      | i64_store8 => exact h.on_i64_store8 v st arg
      | i64_store16 => exact h.on_i64_store16 v st arg
      | i64_store32 => exact h.on_i64_store32 v st arg

theorem total_of_invoke {V : Type} (visitor : code.OpVisitor V)
    (h : ∀ v event, ∃ reply v', invoke visitor v event = .ok (reply, v')) : FullVisitor.Total visitor where
  on_function_start v ctx typeidx bodybegin bodyend := h v (.functionStart ctx typeidx bodybegin bodyend)
  on_unreachable v st := h v (.op st (.unreachable))
  on_nop v st := h v (.op st (.nop))
  on_block v st a0 := h v (.op st (.block a0))
  on_loop v st a0 := h v (.op st (.loop a0))
  on_if v st a0 := h v (.op st (.if_ a0))
  on_else v st a0 := h v (.op st (.else_ a0))
  on_end v st a0 a1 := h v (.op st (.end_ a0 a1))
  on_br v st a0 a1 := h v (.op st (.br a0 a1))
  on_br_if v st a0 a1 := h v (.op st (.br_if a0 a1))
  on_br_table_label v st a0 := h v (.op st (.br_table_label a0))
  on_br_table v st a0 a1 := h v (.op st (.br_table a0 a1))
  on_return v st := h v (.op st (.return_))
  on_call v st a0 := h v (.op st (.call a0))
  on_call_indirect v st a0 a1 := h v (.op st (.call_indirect a0 a1))
  on_drop v st a0 := h v (.op st (.drop a0))
  on_select v st a0 := h v (.op st (.select a0))
  on_local_get v st a0 := h v (.op st (.local_get a0))
  on_local_set v st a0 := h v (.op st (.local_set a0))
  on_local_tee v st a0 := h v (.op st (.local_tee a0))
  on_global_get v st a0 := h v (.op st (.global_get a0))
  on_global_set v st a0 := h v (.op st (.global_set a0))
  on_memory_size v st := h v (.op st (.memory_size))
  on_memory_grow v st := h v (.op st (.memory_grow))
  on_i32_const v st a0 := h v (.op st (.i32_const a0))
  on_i64_const v st a0 := h v (.op st (.i64_const a0))
  on_f32_const v st a0 := h v (.op st (.f32_const a0))
  on_f64_const v st a0 := h v (.op st (.f64_const a0))
  on_i32_load v st arg := h v (.op st (.memory .i32_load arg))
  on_i64_load v st arg := h v (.op st (.memory .i64_load arg))
  on_f32_load v st arg := h v (.op st (.memory .f32_load arg))
  on_f64_load v st arg := h v (.op st (.memory .f64_load arg))
  on_i32_load8_s v st arg := h v (.op st (.memory .i32_load8_s arg))
  on_i32_load8_u v st arg := h v (.op st (.memory .i32_load8_u arg))
  on_i32_load16_s v st arg := h v (.op st (.memory .i32_load16_s arg))
  on_i32_load16_u v st arg := h v (.op st (.memory .i32_load16_u arg))
  on_i64_load8_s v st arg := h v (.op st (.memory .i64_load8_s arg))
  on_i64_load8_u v st arg := h v (.op st (.memory .i64_load8_u arg))
  on_i64_load16_s v st arg := h v (.op st (.memory .i64_load16_s arg))
  on_i64_load16_u v st arg := h v (.op st (.memory .i64_load16_u arg))
  on_i64_load32_s v st arg := h v (.op st (.memory .i64_load32_s arg))
  on_i64_load32_u v st arg := h v (.op st (.memory .i64_load32_u arg))
  on_i32_store v st arg := h v (.op st (.memory .i32_store arg))
  on_i64_store v st arg := h v (.op st (.memory .i64_store arg))
  on_f32_store v st arg := h v (.op st (.memory .f32_store arg))
  on_f64_store v st arg := h v (.op st (.memory .f64_store arg))
  on_i32_store8 v st arg := h v (.op st (.memory .i32_store8 arg))
  on_i32_store16 v st arg := h v (.op st (.memory .i32_store16 arg))
  on_i64_store8 v st arg := h v (.op st (.memory .i64_store8 arg))
  on_i64_store16 v st arg := h v (.op st (.memory .i64_store16 arg))
  on_i64_store32 v st arg := h v (.op st (.memory .i64_store32 arg))
  on_i32_eqz v st := h v (.op st (.numeric .i32_eqz))
  on_i32_eq v st := h v (.op st (.numeric .i32_eq))
  on_i32_ne v st := h v (.op st (.numeric .i32_ne))
  on_i32_lt_s v st := h v (.op st (.numeric .i32_lt_s))
  on_i32_lt_u v st := h v (.op st (.numeric .i32_lt_u))
  on_i32_gt_s v st := h v (.op st (.numeric .i32_gt_s))
  on_i32_gt_u v st := h v (.op st (.numeric .i32_gt_u))
  on_i32_le_s v st := h v (.op st (.numeric .i32_le_s))
  on_i32_le_u v st := h v (.op st (.numeric .i32_le_u))
  on_i32_ge_s v st := h v (.op st (.numeric .i32_ge_s))
  on_i32_ge_u v st := h v (.op st (.numeric .i32_ge_u))
  on_i64_eqz v st := h v (.op st (.numeric .i64_eqz))
  on_i64_eq v st := h v (.op st (.numeric .i64_eq))
  on_i64_ne v st := h v (.op st (.numeric .i64_ne))
  on_i64_lt_s v st := h v (.op st (.numeric .i64_lt_s))
  on_i64_lt_u v st := h v (.op st (.numeric .i64_lt_u))
  on_i64_gt_s v st := h v (.op st (.numeric .i64_gt_s))
  on_i64_gt_u v st := h v (.op st (.numeric .i64_gt_u))
  on_i64_le_s v st := h v (.op st (.numeric .i64_le_s))
  on_i64_le_u v st := h v (.op st (.numeric .i64_le_u))
  on_i64_ge_s v st := h v (.op st (.numeric .i64_ge_s))
  on_i64_ge_u v st := h v (.op st (.numeric .i64_ge_u))
  on_f32_eq v st := h v (.op st (.numeric .f32_eq))
  on_f32_ne v st := h v (.op st (.numeric .f32_ne))
  on_f32_lt v st := h v (.op st (.numeric .f32_lt))
  on_f32_gt v st := h v (.op st (.numeric .f32_gt))
  on_f32_le v st := h v (.op st (.numeric .f32_le))
  on_f32_ge v st := h v (.op st (.numeric .f32_ge))
  on_f64_eq v st := h v (.op st (.numeric .f64_eq))
  on_f64_ne v st := h v (.op st (.numeric .f64_ne))
  on_f64_lt v st := h v (.op st (.numeric .f64_lt))
  on_f64_gt v st := h v (.op st (.numeric .f64_gt))
  on_f64_le v st := h v (.op st (.numeric .f64_le))
  on_f64_ge v st := h v (.op st (.numeric .f64_ge))
  on_i32_sub v st := h v (.op st (.numeric .i32_sub))
  on_i32_mul v st := h v (.op st (.numeric .i32_mul))
  on_i32_div_s v st := h v (.op st (.numeric .i32_div_s))
  on_i32_div_u v st := h v (.op st (.numeric .i32_div_u))
  on_i32_rem_s v st := h v (.op st (.numeric .i32_rem_s))
  on_i32_rem_u v st := h v (.op st (.numeric .i32_rem_u))
  on_i32_and v st := h v (.op st (.numeric .i32_and))
  on_i32_or v st := h v (.op st (.numeric .i32_or))
  on_i32_xor v st := h v (.op st (.numeric .i32_xor))
  on_i32_shl v st := h v (.op st (.numeric .i32_shl))
  on_i32_shr_s v st := h v (.op st (.numeric .i32_shr_s))
  on_i32_shr_u v st := h v (.op st (.numeric .i32_shr_u))
  on_i32_rotl v st := h v (.op st (.numeric .i32_rotl))
  on_i32_rotr v st := h v (.op st (.numeric .i32_rotr))
  on_i64_add v st := h v (.op st (.numeric .i64_add))
  on_i64_sub v st := h v (.op st (.numeric .i64_sub))
  on_i64_mul v st := h v (.op st (.numeric .i64_mul))
  on_i64_div_s v st := h v (.op st (.numeric .i64_div_s))
  on_i64_div_u v st := h v (.op st (.numeric .i64_div_u))
  on_i64_rem_s v st := h v (.op st (.numeric .i64_rem_s))
  on_i64_rem_u v st := h v (.op st (.numeric .i64_rem_u))
  on_i64_and v st := h v (.op st (.numeric .i64_and))
  on_i64_or v st := h v (.op st (.numeric .i64_or))
  on_i64_xor v st := h v (.op st (.numeric .i64_xor))
  on_i64_shl v st := h v (.op st (.numeric .i64_shl))
  on_i64_shr_s v st := h v (.op st (.numeric .i64_shr_s))
  on_i64_shr_u v st := h v (.op st (.numeric .i64_shr_u))
  on_i64_rotl v st := h v (.op st (.numeric .i64_rotl))
  on_i64_rotr v st := h v (.op st (.numeric .i64_rotr))
  on_f32_add v st := h v (.op st (.numeric .f32_add))
  on_f32_sub v st := h v (.op st (.numeric .f32_sub))
  on_f32_mul v st := h v (.op st (.numeric .f32_mul))
  on_f32_div v st := h v (.op st (.numeric .f32_div))
  on_f32_min v st := h v (.op st (.numeric .f32_min))
  on_f32_max v st := h v (.op st (.numeric .f32_max))
  on_f32_copysign v st := h v (.op st (.numeric .f32_copysign))
  on_f64_add v st := h v (.op st (.numeric .f64_add))
  on_f64_sub v st := h v (.op st (.numeric .f64_sub))
  on_f64_mul v st := h v (.op st (.numeric .f64_mul))
  on_f64_div v st := h v (.op st (.numeric .f64_div))
  on_f64_min v st := h v (.op st (.numeric .f64_min))
  on_f64_max v st := h v (.op st (.numeric .f64_max))
  on_f64_copysign v st := h v (.op st (.numeric .f64_copysign))
  on_i32_clz v st := h v (.op st (.numeric .i32_clz))
  on_i32_ctz v st := h v (.op st (.numeric .i32_ctz))
  on_i32_popcnt v st := h v (.op st (.numeric .i32_popcnt))
  on_i32_add v st := h v (.op st (.numeric .i32_add))
  on_i64_clz v st := h v (.op st (.numeric .i64_clz))
  on_i64_ctz v st := h v (.op st (.numeric .i64_ctz))
  on_i64_popcnt v st := h v (.op st (.numeric .i64_popcnt))
  on_f32_abs v st := h v (.op st (.numeric .f32_abs))
  on_f32_neg v st := h v (.op st (.numeric .f32_neg))
  on_f32_ceil v st := h v (.op st (.numeric .f32_ceil))
  on_f32_floor v st := h v (.op st (.numeric .f32_floor))
  on_f32_trunc v st := h v (.op st (.numeric .f32_trunc))
  on_f32_nearest v st := h v (.op st (.numeric .f32_nearest))
  on_f32_sqrt v st := h v (.op st (.numeric .f32_sqrt))
  on_f64_abs v st := h v (.op st (.numeric .f64_abs))
  on_f64_neg v st := h v (.op st (.numeric .f64_neg))
  on_f64_ceil v st := h v (.op st (.numeric .f64_ceil))
  on_f64_floor v st := h v (.op st (.numeric .f64_floor))
  on_f64_trunc v st := h v (.op st (.numeric .f64_trunc))
  on_f64_nearest v st := h v (.op st (.numeric .f64_nearest))
  on_f64_sqrt v st := h v (.op st (.numeric .f64_sqrt))
  on_i32_wrap_i64 v st := h v (.op st (.numeric .i32_wrap_i64))
  on_i32_trunc_f32_s v st := h v (.op st (.numeric .i32_trunc_f32_s))
  on_i32_trunc_f32_u v st := h v (.op st (.numeric .i32_trunc_f32_u))
  on_i32_trunc_f64_s v st := h v (.op st (.numeric .i32_trunc_f64_s))
  on_i32_trunc_f64_u v st := h v (.op st (.numeric .i32_trunc_f64_u))
  on_i64_extend_i32_s v st := h v (.op st (.numeric .i64_extend_i32_s))
  on_i64_extend_i32_u v st := h v (.op st (.numeric .i64_extend_i32_u))
  on_i64_trunc_f32_s v st := h v (.op st (.numeric .i64_trunc_f32_s))
  on_i64_trunc_f32_u v st := h v (.op st (.numeric .i64_trunc_f32_u))
  on_i64_trunc_f64_s v st := h v (.op st (.numeric .i64_trunc_f64_s))
  on_i64_trunc_f64_u v st := h v (.op st (.numeric .i64_trunc_f64_u))
  on_f32_convert_i32_s v st := h v (.op st (.numeric .f32_convert_i32_s))
  on_f32_convert_i32_u v st := h v (.op st (.numeric .f32_convert_i32_u))
  on_f32_convert_i64_s v st := h v (.op st (.numeric .f32_convert_i64_s))
  on_f32_convert_i64_u v st := h v (.op st (.numeric .f32_convert_i64_u))
  on_f32_demote_f64 v st := h v (.op st (.numeric .f32_demote_f64))
  on_f64_convert_i32_s v st := h v (.op st (.numeric .f64_convert_i32_s))
  on_f64_convert_i32_u v st := h v (.op st (.numeric .f64_convert_i32_u))
  on_f64_convert_i64_s v st := h v (.op st (.numeric .f64_convert_i64_s))
  on_f64_convert_i64_u v st := h v (.op st (.numeric .f64_convert_i64_u))
  on_f64_promote_f32 v st := h v (.op st (.numeric .f64_promote_f32))
  on_i32_reinterpret_f32 v st := h v (.op st (.numeric .i32_reinterpret_f32))
  on_i64_reinterpret_f64 v st := h v (.op st (.numeric .i64_reinterpret_f64))
  on_f32_reinterpret_i32 v st := h v (.op st (.numeric .f32_reinterpret_i32))
  on_f64_reinterpret_i64 v st := h v (.op st (.numeric .f64_reinterpret_i64))
  on_i32_extend8_s v st := h v (.op st (.extendedNumeric .i32_extend8_s))
  on_i32_extend16_s v st := h v (.op st (.extendedNumeric .i32_extend16_s))
  on_i64_extend8_s v st := h v (.op st (.extendedNumeric .i64_extend8_s))
  on_i64_extend16_s v st := h v (.op st (.extendedNumeric .i64_extend16_s))
  on_i64_extend32_s v st := h v (.op st (.extendedNumeric .i64_extend32_s))
  on_i32_trunc_sat_f32_s v st := h v (.op st (.extendedNumeric .i32_trunc_sat_f32_s))
  on_i32_trunc_sat_f32_u v st := h v (.op st (.extendedNumeric .i32_trunc_sat_f32_u))
  on_i32_trunc_sat_f64_s v st := h v (.op st (.extendedNumeric .i32_trunc_sat_f64_s))
  on_i32_trunc_sat_f64_u v st := h v (.op st (.extendedNumeric .i32_trunc_sat_f64_u))
  on_i64_trunc_sat_f32_s v st := h v (.op st (.extendedNumeric .i64_trunc_sat_f32_s))
  on_i64_trunc_sat_f32_u v st := h v (.op st (.extendedNumeric .i64_trunc_sat_f32_u))
  on_i64_trunc_sat_f64_s v st := h v (.op st (.extendedNumeric .i64_trunc_sat_f64_s))
  on_i64_trunc_sat_f64_u v st := h v (.op st (.extendedNumeric .i64_trunc_sat_f64_u))
  on_ref_null v st a0 := h v (.op st (.ref_null a0))
  on_ref_is_null v st := h v (.op st (.ref_is_null))
  on_ref_func v st a0 := h v (.op st (.ref_func a0))
  on_select_typed v st a0 := h v (.op st (.select_typed a0))
  on_table_get v st a0 := h v (.op st (.table_get a0))
  on_table_set v st a0 := h v (.op st (.table_set a0))
  on_memory_init v st a0 := h v (.op st (.memory_init a0))
  on_data_drop v st a0 := h v (.op st (.data_drop a0))
  on_memory_copy v st := h v (.op st (.memory_copy))
  on_memory_fill v st := h v (.op st (.memory_fill))
  on_table_init v st a0 a1 := h v (.op st (.table_init a0 a1))
  on_elem_drop v st a0 := h v (.op st (.elem_drop a0))
  on_table_copy v st a0 a1 := h v (.op st (.table_copy a0 a1))
  on_table_grow v st a0 := h v (.op st (.table_grow a0))
  on_table_size v st a0 := h v (.op st (.table_size a0))
  on_table_fill v st a0 := h v (.op st (.table_fill a0))
  on_simd v st a0 := h v (.op st (.simd a0))
  on_simd_lane v st a0 a1 := h v (.op st (.simd_lane a0 a1))
  on_simd_memory v st a0 a1 := h v (.op st (.simd_memory a0 a1))
  on_simd_memory_lane v st a0 a1 a2 := h v (.op st (.simd_memory_lane a0 a1 a2))
  on_simd_const v st a0 a1 := h v (.op st (.simd_const a0 a1))
  on_simd_shuffle v st a0 a1 := h v (.op st (.simd_shuffle a0 a1))

theorem accepts_of_invoke {V : Type} (visitor : code.OpVisitor V)
    (h : ∀ v event, ∃ v', invoke visitor v event = .ok (.Ok (), v')) : FullVisitor.Accepts visitor where
  on_function_start v ctx typeidx bodybegin bodyend := h v (.functionStart ctx typeidx bodybegin bodyend)
  on_unreachable v st := h v (.op st (.unreachable))
  on_nop v st := h v (.op st (.nop))
  on_block v st a0 := h v (.op st (.block a0))
  on_loop v st a0 := h v (.op st (.loop a0))
  on_if v st a0 := h v (.op st (.if_ a0))
  on_else v st a0 := h v (.op st (.else_ a0))
  on_end v st a0 a1 := h v (.op st (.end_ a0 a1))
  on_br v st a0 a1 := h v (.op st (.br a0 a1))
  on_br_if v st a0 a1 := h v (.op st (.br_if a0 a1))
  on_br_table_label v st a0 := h v (.op st (.br_table_label a0))
  on_br_table v st a0 a1 := h v (.op st (.br_table a0 a1))
  on_return v st := h v (.op st (.return_))
  on_call v st a0 := h v (.op st (.call a0))
  on_call_indirect v st a0 a1 := h v (.op st (.call_indirect a0 a1))
  on_drop v st a0 := h v (.op st (.drop a0))
  on_select v st a0 := h v (.op st (.select a0))
  on_local_get v st a0 := h v (.op st (.local_get a0))
  on_local_set v st a0 := h v (.op st (.local_set a0))
  on_local_tee v st a0 := h v (.op st (.local_tee a0))
  on_global_get v st a0 := h v (.op st (.global_get a0))
  on_global_set v st a0 := h v (.op st (.global_set a0))
  on_memory_size v st := h v (.op st (.memory_size))
  on_memory_grow v st := h v (.op st (.memory_grow))
  on_i32_const v st a0 := h v (.op st (.i32_const a0))
  on_i64_const v st a0 := h v (.op st (.i64_const a0))
  on_f32_const v st a0 := h v (.op st (.f32_const a0))
  on_f64_const v st a0 := h v (.op st (.f64_const a0))
  on_i32_load v st arg := h v (.op st (.memory .i32_load arg))
  on_i64_load v st arg := h v (.op st (.memory .i64_load arg))
  on_f32_load v st arg := h v (.op st (.memory .f32_load arg))
  on_f64_load v st arg := h v (.op st (.memory .f64_load arg))
  on_i32_load8_s v st arg := h v (.op st (.memory .i32_load8_s arg))
  on_i32_load8_u v st arg := h v (.op st (.memory .i32_load8_u arg))
  on_i32_load16_s v st arg := h v (.op st (.memory .i32_load16_s arg))
  on_i32_load16_u v st arg := h v (.op st (.memory .i32_load16_u arg))
  on_i64_load8_s v st arg := h v (.op st (.memory .i64_load8_s arg))
  on_i64_load8_u v st arg := h v (.op st (.memory .i64_load8_u arg))
  on_i64_load16_s v st arg := h v (.op st (.memory .i64_load16_s arg))
  on_i64_load16_u v st arg := h v (.op st (.memory .i64_load16_u arg))
  on_i64_load32_s v st arg := h v (.op st (.memory .i64_load32_s arg))
  on_i64_load32_u v st arg := h v (.op st (.memory .i64_load32_u arg))
  on_i32_store v st arg := h v (.op st (.memory .i32_store arg))
  on_i64_store v st arg := h v (.op st (.memory .i64_store arg))
  on_f32_store v st arg := h v (.op st (.memory .f32_store arg))
  on_f64_store v st arg := h v (.op st (.memory .f64_store arg))
  on_i32_store8 v st arg := h v (.op st (.memory .i32_store8 arg))
  on_i32_store16 v st arg := h v (.op st (.memory .i32_store16 arg))
  on_i64_store8 v st arg := h v (.op st (.memory .i64_store8 arg))
  on_i64_store16 v st arg := h v (.op st (.memory .i64_store16 arg))
  on_i64_store32 v st arg := h v (.op st (.memory .i64_store32 arg))
  on_i32_eqz v st := h v (.op st (.numeric .i32_eqz))
  on_i32_eq v st := h v (.op st (.numeric .i32_eq))
  on_i32_ne v st := h v (.op st (.numeric .i32_ne))
  on_i32_lt_s v st := h v (.op st (.numeric .i32_lt_s))
  on_i32_lt_u v st := h v (.op st (.numeric .i32_lt_u))
  on_i32_gt_s v st := h v (.op st (.numeric .i32_gt_s))
  on_i32_gt_u v st := h v (.op st (.numeric .i32_gt_u))
  on_i32_le_s v st := h v (.op st (.numeric .i32_le_s))
  on_i32_le_u v st := h v (.op st (.numeric .i32_le_u))
  on_i32_ge_s v st := h v (.op st (.numeric .i32_ge_s))
  on_i32_ge_u v st := h v (.op st (.numeric .i32_ge_u))
  on_i64_eqz v st := h v (.op st (.numeric .i64_eqz))
  on_i64_eq v st := h v (.op st (.numeric .i64_eq))
  on_i64_ne v st := h v (.op st (.numeric .i64_ne))
  on_i64_lt_s v st := h v (.op st (.numeric .i64_lt_s))
  on_i64_lt_u v st := h v (.op st (.numeric .i64_lt_u))
  on_i64_gt_s v st := h v (.op st (.numeric .i64_gt_s))
  on_i64_gt_u v st := h v (.op st (.numeric .i64_gt_u))
  on_i64_le_s v st := h v (.op st (.numeric .i64_le_s))
  on_i64_le_u v st := h v (.op st (.numeric .i64_le_u))
  on_i64_ge_s v st := h v (.op st (.numeric .i64_ge_s))
  on_i64_ge_u v st := h v (.op st (.numeric .i64_ge_u))
  on_f32_eq v st := h v (.op st (.numeric .f32_eq))
  on_f32_ne v st := h v (.op st (.numeric .f32_ne))
  on_f32_lt v st := h v (.op st (.numeric .f32_lt))
  on_f32_gt v st := h v (.op st (.numeric .f32_gt))
  on_f32_le v st := h v (.op st (.numeric .f32_le))
  on_f32_ge v st := h v (.op st (.numeric .f32_ge))
  on_f64_eq v st := h v (.op st (.numeric .f64_eq))
  on_f64_ne v st := h v (.op st (.numeric .f64_ne))
  on_f64_lt v st := h v (.op st (.numeric .f64_lt))
  on_f64_gt v st := h v (.op st (.numeric .f64_gt))
  on_f64_le v st := h v (.op st (.numeric .f64_le))
  on_f64_ge v st := h v (.op st (.numeric .f64_ge))
  on_i32_sub v st := h v (.op st (.numeric .i32_sub))
  on_i32_mul v st := h v (.op st (.numeric .i32_mul))
  on_i32_div_s v st := h v (.op st (.numeric .i32_div_s))
  on_i32_div_u v st := h v (.op st (.numeric .i32_div_u))
  on_i32_rem_s v st := h v (.op st (.numeric .i32_rem_s))
  on_i32_rem_u v st := h v (.op st (.numeric .i32_rem_u))
  on_i32_and v st := h v (.op st (.numeric .i32_and))
  on_i32_or v st := h v (.op st (.numeric .i32_or))
  on_i32_xor v st := h v (.op st (.numeric .i32_xor))
  on_i32_shl v st := h v (.op st (.numeric .i32_shl))
  on_i32_shr_s v st := h v (.op st (.numeric .i32_shr_s))
  on_i32_shr_u v st := h v (.op st (.numeric .i32_shr_u))
  on_i32_rotl v st := h v (.op st (.numeric .i32_rotl))
  on_i32_rotr v st := h v (.op st (.numeric .i32_rotr))
  on_i64_add v st := h v (.op st (.numeric .i64_add))
  on_i64_sub v st := h v (.op st (.numeric .i64_sub))
  on_i64_mul v st := h v (.op st (.numeric .i64_mul))
  on_i64_div_s v st := h v (.op st (.numeric .i64_div_s))
  on_i64_div_u v st := h v (.op st (.numeric .i64_div_u))
  on_i64_rem_s v st := h v (.op st (.numeric .i64_rem_s))
  on_i64_rem_u v st := h v (.op st (.numeric .i64_rem_u))
  on_i64_and v st := h v (.op st (.numeric .i64_and))
  on_i64_or v st := h v (.op st (.numeric .i64_or))
  on_i64_xor v st := h v (.op st (.numeric .i64_xor))
  on_i64_shl v st := h v (.op st (.numeric .i64_shl))
  on_i64_shr_s v st := h v (.op st (.numeric .i64_shr_s))
  on_i64_shr_u v st := h v (.op st (.numeric .i64_shr_u))
  on_i64_rotl v st := h v (.op st (.numeric .i64_rotl))
  on_i64_rotr v st := h v (.op st (.numeric .i64_rotr))
  on_f32_add v st := h v (.op st (.numeric .f32_add))
  on_f32_sub v st := h v (.op st (.numeric .f32_sub))
  on_f32_mul v st := h v (.op st (.numeric .f32_mul))
  on_f32_div v st := h v (.op st (.numeric .f32_div))
  on_f32_min v st := h v (.op st (.numeric .f32_min))
  on_f32_max v st := h v (.op st (.numeric .f32_max))
  on_f32_copysign v st := h v (.op st (.numeric .f32_copysign))
  on_f64_add v st := h v (.op st (.numeric .f64_add))
  on_f64_sub v st := h v (.op st (.numeric .f64_sub))
  on_f64_mul v st := h v (.op st (.numeric .f64_mul))
  on_f64_div v st := h v (.op st (.numeric .f64_div))
  on_f64_min v st := h v (.op st (.numeric .f64_min))
  on_f64_max v st := h v (.op st (.numeric .f64_max))
  on_f64_copysign v st := h v (.op st (.numeric .f64_copysign))
  on_i32_clz v st := h v (.op st (.numeric .i32_clz))
  on_i32_ctz v st := h v (.op st (.numeric .i32_ctz))
  on_i32_popcnt v st := h v (.op st (.numeric .i32_popcnt))
  on_i32_add v st := h v (.op st (.numeric .i32_add))
  on_i64_clz v st := h v (.op st (.numeric .i64_clz))
  on_i64_ctz v st := h v (.op st (.numeric .i64_ctz))
  on_i64_popcnt v st := h v (.op st (.numeric .i64_popcnt))
  on_f32_abs v st := h v (.op st (.numeric .f32_abs))
  on_f32_neg v st := h v (.op st (.numeric .f32_neg))
  on_f32_ceil v st := h v (.op st (.numeric .f32_ceil))
  on_f32_floor v st := h v (.op st (.numeric .f32_floor))
  on_f32_trunc v st := h v (.op st (.numeric .f32_trunc))
  on_f32_nearest v st := h v (.op st (.numeric .f32_nearest))
  on_f32_sqrt v st := h v (.op st (.numeric .f32_sqrt))
  on_f64_abs v st := h v (.op st (.numeric .f64_abs))
  on_f64_neg v st := h v (.op st (.numeric .f64_neg))
  on_f64_ceil v st := h v (.op st (.numeric .f64_ceil))
  on_f64_floor v st := h v (.op st (.numeric .f64_floor))
  on_f64_trunc v st := h v (.op st (.numeric .f64_trunc))
  on_f64_nearest v st := h v (.op st (.numeric .f64_nearest))
  on_f64_sqrt v st := h v (.op st (.numeric .f64_sqrt))
  on_i32_wrap_i64 v st := h v (.op st (.numeric .i32_wrap_i64))
  on_i32_trunc_f32_s v st := h v (.op st (.numeric .i32_trunc_f32_s))
  on_i32_trunc_f32_u v st := h v (.op st (.numeric .i32_trunc_f32_u))
  on_i32_trunc_f64_s v st := h v (.op st (.numeric .i32_trunc_f64_s))
  on_i32_trunc_f64_u v st := h v (.op st (.numeric .i32_trunc_f64_u))
  on_i64_extend_i32_s v st := h v (.op st (.numeric .i64_extend_i32_s))
  on_i64_extend_i32_u v st := h v (.op st (.numeric .i64_extend_i32_u))
  on_i64_trunc_f32_s v st := h v (.op st (.numeric .i64_trunc_f32_s))
  on_i64_trunc_f32_u v st := h v (.op st (.numeric .i64_trunc_f32_u))
  on_i64_trunc_f64_s v st := h v (.op st (.numeric .i64_trunc_f64_s))
  on_i64_trunc_f64_u v st := h v (.op st (.numeric .i64_trunc_f64_u))
  on_f32_convert_i32_s v st := h v (.op st (.numeric .f32_convert_i32_s))
  on_f32_convert_i32_u v st := h v (.op st (.numeric .f32_convert_i32_u))
  on_f32_convert_i64_s v st := h v (.op st (.numeric .f32_convert_i64_s))
  on_f32_convert_i64_u v st := h v (.op st (.numeric .f32_convert_i64_u))
  on_f32_demote_f64 v st := h v (.op st (.numeric .f32_demote_f64))
  on_f64_convert_i32_s v st := h v (.op st (.numeric .f64_convert_i32_s))
  on_f64_convert_i32_u v st := h v (.op st (.numeric .f64_convert_i32_u))
  on_f64_convert_i64_s v st := h v (.op st (.numeric .f64_convert_i64_s))
  on_f64_convert_i64_u v st := h v (.op st (.numeric .f64_convert_i64_u))
  on_f64_promote_f32 v st := h v (.op st (.numeric .f64_promote_f32))
  on_i32_reinterpret_f32 v st := h v (.op st (.numeric .i32_reinterpret_f32))
  on_i64_reinterpret_f64 v st := h v (.op st (.numeric .i64_reinterpret_f64))
  on_f32_reinterpret_i32 v st := h v (.op st (.numeric .f32_reinterpret_i32))
  on_f64_reinterpret_i64 v st := h v (.op st (.numeric .f64_reinterpret_i64))
  on_i32_extend8_s v st := h v (.op st (.extendedNumeric .i32_extend8_s))
  on_i32_extend16_s v st := h v (.op st (.extendedNumeric .i32_extend16_s))
  on_i64_extend8_s v st := h v (.op st (.extendedNumeric .i64_extend8_s))
  on_i64_extend16_s v st := h v (.op st (.extendedNumeric .i64_extend16_s))
  on_i64_extend32_s v st := h v (.op st (.extendedNumeric .i64_extend32_s))
  on_i32_trunc_sat_f32_s v st := h v (.op st (.extendedNumeric .i32_trunc_sat_f32_s))
  on_i32_trunc_sat_f32_u v st := h v (.op st (.extendedNumeric .i32_trunc_sat_f32_u))
  on_i32_trunc_sat_f64_s v st := h v (.op st (.extendedNumeric .i32_trunc_sat_f64_s))
  on_i32_trunc_sat_f64_u v st := h v (.op st (.extendedNumeric .i32_trunc_sat_f64_u))
  on_i64_trunc_sat_f32_s v st := h v (.op st (.extendedNumeric .i64_trunc_sat_f32_s))
  on_i64_trunc_sat_f32_u v st := h v (.op st (.extendedNumeric .i64_trunc_sat_f32_u))
  on_i64_trunc_sat_f64_s v st := h v (.op st (.extendedNumeric .i64_trunc_sat_f64_s))
  on_i64_trunc_sat_f64_u v st := h v (.op st (.extendedNumeric .i64_trunc_sat_f64_u))
  on_ref_null v st a0 := h v (.op st (.ref_null a0))
  on_ref_is_null v st := h v (.op st (.ref_is_null))
  on_ref_func v st a0 := h v (.op st (.ref_func a0))
  on_select_typed v st a0 := h v (.op st (.select_typed a0))
  on_table_get v st a0 := h v (.op st (.table_get a0))
  on_table_set v st a0 := h v (.op st (.table_set a0))
  on_memory_init v st a0 := h v (.op st (.memory_init a0))
  on_data_drop v st a0 := h v (.op st (.data_drop a0))
  on_memory_copy v st := h v (.op st (.memory_copy))
  on_memory_fill v st := h v (.op st (.memory_fill))
  on_table_init v st a0 a1 := h v (.op st (.table_init a0 a1))
  on_elem_drop v st a0 := h v (.op st (.elem_drop a0))
  on_table_copy v st a0 a1 := h v (.op st (.table_copy a0 a1))
  on_table_grow v st a0 := h v (.op st (.table_grow a0))
  on_table_size v st a0 := h v (.op st (.table_size a0))
  on_table_fill v st a0 := h v (.op st (.table_fill a0))
  on_simd v st a0 := h v (.op st (.simd a0))
  on_simd_lane v st a0 a1 := h v (.op st (.simd_lane a0 a1))
  on_simd_memory v st a0 a1 := h v (.op st (.simd_memory a0 a1))
  on_simd_memory_lane v st a0 a1 a2 := h v (.op st (.simd_memory_lane a0 a1 a2))
  on_simd_const v st a0 a1 := h v (.op st (.simd_const a0 a1))
  on_simd_shuffle v st a0 a1 := h v (.op st (.simd_shuffle a0 a1))

theorem instrument_total {V : Type} {visitor : code.OpVisitor V}
    (h : FullVisitor.Total visitor) : FullVisitor.Total (instrument visitor) := by
  apply total_of_invoke
  rintro ⟨v, log⟩ event
  obtain ⟨reply, v', hv⟩ := total_invoke h v event
  exact ⟨reply, (v', log ++ [⟨event, reply⟩]), by simp [hv]⟩

theorem instrument_accepts {V : Type} {visitor : code.OpVisitor V}
    (h : FullVisitor.Accepts visitor) : FullVisitor.Accepts (instrument visitor) := by
  apply accepts_of_invoke
  rintro ⟨v, log⟩ event
  obtain ⟨v', hv⟩ := accepts_invoke h v event
  exact ⟨(v', log ++ [⟨event, .Ok ()⟩]), by simp [hv]⟩

/-- A recorder that always accepts. -/
def recorder : code.OpVisitor (List Observation) :=
  ofHandler fun log event => .ok (.Ok (), log ++ [⟨event, .Ok ()⟩])

theorem recorder_records : Records recorder id := by
  intro log event reply log' h
  simp [recorder] at h
  rcases h with ⟨rfl, rfl⟩
  rfl

theorem recorder_accepts : FullVisitor.Accepts recorder := by
  apply accepts_of_invoke
  intro log event
  exact ⟨log ++ [⟨event, .Ok ()⟩], by simp [recorder]⟩

theorem recorder_total : FullVisitor.Total recorder :=
  recorder_accepts.toTotal

/-- A deterministic recorder that rejects precisely at the requested zero-based
callback index. The rejecting callback itself remains in the trace. -/
def rejectAt (index : Nat) (err : error.VisitError) : code.OpVisitor (List Observation) :=
  ofHandler fun log event =>
    let reply : VisitResult := if log.length = index then .Err err else .Ok ()
    .ok (reply, log ++ [⟨event, reply⟩])

theorem rejectAt_records (index : Nat) (err : error.VisitError) :
    Records (rejectAt index err) id := by
  intro log event reply log' h
  simp only [rejectAt, invoke_ofHandler, Result.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem rejectAt_total (index : Nat) (err : error.VisitError) :
    FullVisitor.Total (rejectAt index err) := by
  apply total_of_invoke
  intro log event
  let reply : VisitResult := if log.length = index then .Err err else .Ok ()
  exact ⟨reply, log ++ [⟨event, reply⟩], by simp [rejectAt, reply]⟩

@[simp] theorem invoke_rejectAt (index : Nat) (err : error.VisitError)
    (log : List Observation) (event : Event) :
    invoke (rejectAt index err) log event =
      let reply : VisitResult := if log.length = index then .Err err else .Ok ()
      .ok (reply, log ++ [⟨event, reply⟩]) := by
  simp [rejectAt]

end Itasca.VisitorTrace
