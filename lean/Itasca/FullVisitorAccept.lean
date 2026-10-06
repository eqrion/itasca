import Itasca.FullVisitor

open Aeneas Aeneas.Std

namespace Itasca.FullVisitor

/-- Every actual hook terminates successfully. Visitor state may change freely. -/
structure Accepts {V : Type} (visitor : code.OpVisitor V) : Prop where
  on_function_start : ∀ (v : V) (a1 : _root_.Itasca.code.Context) (a2 : Std.U32) (a3 : Std.Usize) (a4 : Std.Usize), ∃ v', visitor.on_function_start v a1 a2 a3 a4 = .ok (.Ok (), v')
  on_unreachable : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_unreachable v a1 = .ok (.Ok (), v')
  on_nop : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_nop v a1 = .ok (.Ok (), v')
  on_block : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.BlockType), ∃ v', visitor.on_block v a1 a2 = .ok (.Ok (), v')
  on_loop : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.BlockType), ∃ v', visitor.on_loop v a1 a2 = .ok (.Ok (), v')
  on_if : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.BlockType), ∃ v', visitor.on_if v a1 a2 = .ok (.Ok (), v')
  on_else : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.BlockType), ∃ v', visitor.on_else v a1 a2 = .ok (.Ok (), v')
  on_end : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.LabelKind) (a3 : _root_.Itasca.code.BlockType), ∃ v', visitor.on_end v a1 a2 a3 = .ok (.Ok (), v')
  on_br : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32) (a3 : _root_.Itasca.code.BlockType), ∃ v', visitor.on_br v a1 a2 a3 = .ok (.Ok (), v')
  on_br_if : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32) (a3 : _root_.Itasca.code.BlockType), ∃ v', visitor.on_br_if v a1 a2 a3 = .ok (.Ok (), v')
  on_br_table_label : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_br_table_label v a1 a2 = .ok (.Ok (), v')
  on_br_table : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32) (a3 : _root_.Itasca.code.BlockType), ∃ v', visitor.on_br_table v a1 a2 a3 = .ok (.Ok (), v')
  on_return : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_return v a1 = .ok (.Ok (), v')
  on_call : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_call v a1 a2 = .ok (.Ok (), v')
  on_call_indirect : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_call_indirect v a1 a2 = .ok (.Ok (), v')
  on_drop : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.StackType), ∃ v', visitor.on_drop v a1 a2 = .ok (.Ok (), v')
  on_select : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.StackType), ∃ v', visitor.on_select v a1 a2 = .ok (.Ok (), v')
  on_local_get : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_local_get v a1 a2 = .ok (.Ok (), v')
  on_local_set : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_local_set v a1 a2 = .ok (.Ok (), v')
  on_local_tee : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_local_tee v a1 a2 = .ok (.Ok (), v')
  on_global_get : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_global_get v a1 a2 = .ok (.Ok (), v')
  on_global_set : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_global_set v a1 a2 = .ok (.Ok (), v')
  on_memory_size : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_memory_size v a1 = .ok (.Ok (), v')
  on_memory_grow : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_memory_grow v a1 = .ok (.Ok (), v')
  on_i32_const : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.I32), ∃ v', visitor.on_i32_const v a1 a2 = .ok (.Ok (), v')
  on_i64_const : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.I64), ∃ v', visitor.on_i64_const v a1 a2 = .ok (.Ok (), v')
  on_f32_const : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_f32_const v a1 a2 = .ok (.Ok (), v')
  on_f64_const : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U64), ∃ v', visitor.on_f64_const v a1 a2 = .ok (.Ok (), v')
  on_i32_load : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i32_load v a1 a2 = .ok (.Ok (), v')
  on_i64_load : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i64_load v a1 a2 = .ok (.Ok (), v')
  on_f32_load : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_f32_load v a1 a2 = .ok (.Ok (), v')
  on_f64_load : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_f64_load v a1 a2 = .ok (.Ok (), v')
  on_i32_load8_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i32_load8_s v a1 a2 = .ok (.Ok (), v')
  on_i32_load8_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i32_load8_u v a1 a2 = .ok (.Ok (), v')
  on_i32_load16_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i32_load16_s v a1 a2 = .ok (.Ok (), v')
  on_i32_load16_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i32_load16_u v a1 a2 = .ok (.Ok (), v')
  on_i64_load8_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i64_load8_s v a1 a2 = .ok (.Ok (), v')
  on_i64_load8_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i64_load8_u v a1 a2 = .ok (.Ok (), v')
  on_i64_load16_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i64_load16_s v a1 a2 = .ok (.Ok (), v')
  on_i64_load16_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i64_load16_u v a1 a2 = .ok (.Ok (), v')
  on_i64_load32_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i64_load32_s v a1 a2 = .ok (.Ok (), v')
  on_i64_load32_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i64_load32_u v a1 a2 = .ok (.Ok (), v')
  on_i32_store : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i32_store v a1 a2 = .ok (.Ok (), v')
  on_i64_store : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i64_store v a1 a2 = .ok (.Ok (), v')
  on_f32_store : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_f32_store v a1 a2 = .ok (.Ok (), v')
  on_f64_store : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_f64_store v a1 a2 = .ok (.Ok (), v')
  on_i32_store8 : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i32_store8 v a1 a2 = .ok (.Ok (), v')
  on_i32_store16 : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i32_store16 v a1 a2 = .ok (.Ok (), v')
  on_i64_store8 : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i64_store8 v a1 a2 = .ok (.Ok (), v')
  on_i64_store16 : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i64_store16 v a1 a2 = .ok (.Ok (), v')
  on_i64_store32 : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.MemArg), ∃ v', visitor.on_i64_store32 v a1 a2 = .ok (.Ok (), v')
  on_i32_eqz : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_eqz v a1 = .ok (.Ok (), v')
  on_i32_eq : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_eq v a1 = .ok (.Ok (), v')
  on_i32_ne : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_ne v a1 = .ok (.Ok (), v')
  on_i32_lt_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_lt_s v a1 = .ok (.Ok (), v')
  on_i32_lt_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_lt_u v a1 = .ok (.Ok (), v')
  on_i32_gt_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_gt_s v a1 = .ok (.Ok (), v')
  on_i32_gt_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_gt_u v a1 = .ok (.Ok (), v')
  on_i32_le_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_le_s v a1 = .ok (.Ok (), v')
  on_i32_le_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_le_u v a1 = .ok (.Ok (), v')
  on_i32_ge_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_ge_s v a1 = .ok (.Ok (), v')
  on_i32_ge_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_ge_u v a1 = .ok (.Ok (), v')
  on_i64_eqz : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_eqz v a1 = .ok (.Ok (), v')
  on_i64_eq : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_eq v a1 = .ok (.Ok (), v')
  on_i64_ne : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_ne v a1 = .ok (.Ok (), v')
  on_i64_lt_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_lt_s v a1 = .ok (.Ok (), v')
  on_i64_lt_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_lt_u v a1 = .ok (.Ok (), v')
  on_i64_gt_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_gt_s v a1 = .ok (.Ok (), v')
  on_i64_gt_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_gt_u v a1 = .ok (.Ok (), v')
  on_i64_le_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_le_s v a1 = .ok (.Ok (), v')
  on_i64_le_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_le_u v a1 = .ok (.Ok (), v')
  on_i64_ge_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_ge_s v a1 = .ok (.Ok (), v')
  on_i64_ge_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_ge_u v a1 = .ok (.Ok (), v')
  on_f32_eq : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_eq v a1 = .ok (.Ok (), v')
  on_f32_ne : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_ne v a1 = .ok (.Ok (), v')
  on_f32_lt : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_lt v a1 = .ok (.Ok (), v')
  on_f32_gt : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_gt v a1 = .ok (.Ok (), v')
  on_f32_le : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_le v a1 = .ok (.Ok (), v')
  on_f32_ge : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_ge v a1 = .ok (.Ok (), v')
  on_f64_eq : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_eq v a1 = .ok (.Ok (), v')
  on_f64_ne : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_ne v a1 = .ok (.Ok (), v')
  on_f64_lt : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_lt v a1 = .ok (.Ok (), v')
  on_f64_gt : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_gt v a1 = .ok (.Ok (), v')
  on_f64_le : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_le v a1 = .ok (.Ok (), v')
  on_f64_ge : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_ge v a1 = .ok (.Ok (), v')
  on_i32_sub : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_sub v a1 = .ok (.Ok (), v')
  on_i32_mul : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_mul v a1 = .ok (.Ok (), v')
  on_i32_div_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_div_s v a1 = .ok (.Ok (), v')
  on_i32_div_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_div_u v a1 = .ok (.Ok (), v')
  on_i32_rem_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_rem_s v a1 = .ok (.Ok (), v')
  on_i32_rem_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_rem_u v a1 = .ok (.Ok (), v')
  on_i32_and : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_and v a1 = .ok (.Ok (), v')
  on_i32_or : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_or v a1 = .ok (.Ok (), v')
  on_i32_xor : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_xor v a1 = .ok (.Ok (), v')
  on_i32_shl : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_shl v a1 = .ok (.Ok (), v')
  on_i32_shr_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_shr_s v a1 = .ok (.Ok (), v')
  on_i32_shr_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_shr_u v a1 = .ok (.Ok (), v')
  on_i32_rotl : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_rotl v a1 = .ok (.Ok (), v')
  on_i32_rotr : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_rotr v a1 = .ok (.Ok (), v')
  on_i64_add : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_add v a1 = .ok (.Ok (), v')
  on_i64_sub : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_sub v a1 = .ok (.Ok (), v')
  on_i64_mul : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_mul v a1 = .ok (.Ok (), v')
  on_i64_div_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_div_s v a1 = .ok (.Ok (), v')
  on_i64_div_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_div_u v a1 = .ok (.Ok (), v')
  on_i64_rem_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_rem_s v a1 = .ok (.Ok (), v')
  on_i64_rem_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_rem_u v a1 = .ok (.Ok (), v')
  on_i64_and : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_and v a1 = .ok (.Ok (), v')
  on_i64_or : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_or v a1 = .ok (.Ok (), v')
  on_i64_xor : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_xor v a1 = .ok (.Ok (), v')
  on_i64_shl : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_shl v a1 = .ok (.Ok (), v')
  on_i64_shr_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_shr_s v a1 = .ok (.Ok (), v')
  on_i64_shr_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_shr_u v a1 = .ok (.Ok (), v')
  on_i64_rotl : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_rotl v a1 = .ok (.Ok (), v')
  on_i64_rotr : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_rotr v a1 = .ok (.Ok (), v')
  on_f32_add : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_add v a1 = .ok (.Ok (), v')
  on_f32_sub : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_sub v a1 = .ok (.Ok (), v')
  on_f32_mul : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_mul v a1 = .ok (.Ok (), v')
  on_f32_div : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_div v a1 = .ok (.Ok (), v')
  on_f32_min : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_min v a1 = .ok (.Ok (), v')
  on_f32_max : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_max v a1 = .ok (.Ok (), v')
  on_f32_copysign : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_copysign v a1 = .ok (.Ok (), v')
  on_f64_add : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_add v a1 = .ok (.Ok (), v')
  on_f64_sub : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_sub v a1 = .ok (.Ok (), v')
  on_f64_mul : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_mul v a1 = .ok (.Ok (), v')
  on_f64_div : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_div v a1 = .ok (.Ok (), v')
  on_f64_min : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_min v a1 = .ok (.Ok (), v')
  on_f64_max : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_max v a1 = .ok (.Ok (), v')
  on_f64_copysign : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_copysign v a1 = .ok (.Ok (), v')
  on_i32_clz : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_clz v a1 = .ok (.Ok (), v')
  on_i32_ctz : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_ctz v a1 = .ok (.Ok (), v')
  on_i32_popcnt : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_popcnt v a1 = .ok (.Ok (), v')
  on_i32_add : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_add v a1 = .ok (.Ok (), v')
  on_i64_clz : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_clz v a1 = .ok (.Ok (), v')
  on_i64_ctz : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_ctz v a1 = .ok (.Ok (), v')
  on_i64_popcnt : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_popcnt v a1 = .ok (.Ok (), v')
  on_f32_abs : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_abs v a1 = .ok (.Ok (), v')
  on_f32_neg : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_neg v a1 = .ok (.Ok (), v')
  on_f32_ceil : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_ceil v a1 = .ok (.Ok (), v')
  on_f32_floor : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_floor v a1 = .ok (.Ok (), v')
  on_f32_trunc : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_trunc v a1 = .ok (.Ok (), v')
  on_f32_nearest : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_nearest v a1 = .ok (.Ok (), v')
  on_f32_sqrt : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_sqrt v a1 = .ok (.Ok (), v')
  on_f64_abs : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_abs v a1 = .ok (.Ok (), v')
  on_f64_neg : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_neg v a1 = .ok (.Ok (), v')
  on_f64_ceil : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_ceil v a1 = .ok (.Ok (), v')
  on_f64_floor : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_floor v a1 = .ok (.Ok (), v')
  on_f64_trunc : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_trunc v a1 = .ok (.Ok (), v')
  on_f64_nearest : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_nearest v a1 = .ok (.Ok (), v')
  on_f64_sqrt : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_sqrt v a1 = .ok (.Ok (), v')
  on_i32_wrap_i64 : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_wrap_i64 v a1 = .ok (.Ok (), v')
  on_i32_trunc_f32_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_trunc_f32_s v a1 = .ok (.Ok (), v')
  on_i32_trunc_f32_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_trunc_f32_u v a1 = .ok (.Ok (), v')
  on_i32_trunc_f64_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_trunc_f64_s v a1 = .ok (.Ok (), v')
  on_i32_trunc_f64_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_trunc_f64_u v a1 = .ok (.Ok (), v')
  on_i64_extend_i32_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_extend_i32_s v a1 = .ok (.Ok (), v')
  on_i64_extend_i32_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_extend_i32_u v a1 = .ok (.Ok (), v')
  on_i64_trunc_f32_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_trunc_f32_s v a1 = .ok (.Ok (), v')
  on_i64_trunc_f32_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_trunc_f32_u v a1 = .ok (.Ok (), v')
  on_i64_trunc_f64_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_trunc_f64_s v a1 = .ok (.Ok (), v')
  on_i64_trunc_f64_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_trunc_f64_u v a1 = .ok (.Ok (), v')
  on_f32_convert_i32_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_convert_i32_s v a1 = .ok (.Ok (), v')
  on_f32_convert_i32_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_convert_i32_u v a1 = .ok (.Ok (), v')
  on_f32_convert_i64_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_convert_i64_s v a1 = .ok (.Ok (), v')
  on_f32_convert_i64_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_convert_i64_u v a1 = .ok (.Ok (), v')
  on_f32_demote_f64 : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_demote_f64 v a1 = .ok (.Ok (), v')
  on_f64_convert_i32_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_convert_i32_s v a1 = .ok (.Ok (), v')
  on_f64_convert_i32_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_convert_i32_u v a1 = .ok (.Ok (), v')
  on_f64_convert_i64_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_convert_i64_s v a1 = .ok (.Ok (), v')
  on_f64_convert_i64_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_convert_i64_u v a1 = .ok (.Ok (), v')
  on_f64_promote_f32 : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_promote_f32 v a1 = .ok (.Ok (), v')
  on_i32_reinterpret_f32 : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_reinterpret_f32 v a1 = .ok (.Ok (), v')
  on_i64_reinterpret_f64 : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_reinterpret_f64 v a1 = .ok (.Ok (), v')
  on_f32_reinterpret_i32 : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f32_reinterpret_i32 v a1 = .ok (.Ok (), v')
  on_f64_reinterpret_i64 : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_f64_reinterpret_i64 v a1 = .ok (.Ok (), v')

theorem empty_accepts : Accepts code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor := by
  constructor <;> intros <;> exact ⟨_, rfl⟩

theorem Accepts.toTotal {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor) :
    Total visitor := by
  constructor
  · intro v a1 a2 a3 a4
    obtain ⟨v', hv⟩ := h.on_function_start v a1 a2 a3 a4
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_unreachable v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_nop v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_block v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_loop v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_if v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_else v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2 a3
    obtain ⟨v', hv⟩ := h.on_end v a1 a2 a3
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2 a3
    obtain ⟨v', hv⟩ := h.on_br v a1 a2 a3
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2 a3
    obtain ⟨v', hv⟩ := h.on_br_if v a1 a2 a3
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_br_table_label v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2 a3
    obtain ⟨v', hv⟩ := h.on_br_table v a1 a2 a3
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_return v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_call v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_call_indirect v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_drop v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_select v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_local_get v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_local_set v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_local_tee v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_global_get v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_global_set v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_memory_size v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_memory_grow v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i32_const v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i64_const v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_f32_const v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_f64_const v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i32_load v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i64_load v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_f32_load v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_f64_load v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i32_load8_s v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i32_load8_u v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i32_load16_s v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i32_load16_u v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i64_load8_s v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i64_load8_u v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i64_load16_s v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i64_load16_u v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i64_load32_s v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i64_load32_u v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i32_store v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i64_store v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_f32_store v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_f64_store v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i32_store8 v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i32_store16 v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i64_store8 v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i64_store16 v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_i64_store32 v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_eqz v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_eq v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_ne v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_lt_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_lt_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_gt_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_gt_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_le_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_le_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_ge_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_ge_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_eqz v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_eq v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_ne v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_lt_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_lt_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_gt_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_gt_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_le_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_le_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_ge_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_ge_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_eq v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_ne v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_lt v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_gt v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_le v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_ge v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_eq v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_ne v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_lt v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_gt v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_le v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_ge v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_sub v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_mul v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_div_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_div_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_rem_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_rem_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_and v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_or v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_xor v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_shl v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_shr_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_shr_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_rotl v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_rotr v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_add v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_sub v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_mul v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_div_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_div_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_rem_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_rem_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_and v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_or v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_xor v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_shl v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_shr_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_shr_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_rotl v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_rotr v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_add v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_sub v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_mul v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_div v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_min v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_max v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_copysign v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_add v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_sub v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_mul v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_div v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_min v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_max v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_copysign v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_clz v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_ctz v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_popcnt v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_add v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_clz v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_ctz v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_popcnt v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_abs v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_neg v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_ceil v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_floor v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_trunc v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_nearest v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_sqrt v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_abs v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_neg v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_ceil v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_floor v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_trunc v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_nearest v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_sqrt v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_wrap_i64 v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_trunc_f32_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_trunc_f32_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_trunc_f64_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_trunc_f64_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_extend_i32_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_extend_i32_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_trunc_f32_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_trunc_f32_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_trunc_f64_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_trunc_f64_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_convert_i32_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_convert_i32_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_convert_i64_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_convert_i64_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_demote_f64 v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_convert_i32_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_convert_i32_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_convert_i64_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_convert_i64_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_promote_f32 v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_reinterpret_f32 v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_reinterpret_f64 v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f32_reinterpret_i32 v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_f64_reinterpret_i64 v a1
    exact ⟨.Ok (), v', hv⟩

/-- Numeric dispatch invokes only one of the explicitly total hooks. -/
theorem Accepts.visit_numeric {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor)
    (v : V) (st : code.OpIterState) (opcode : U8) :
    ∃ v', code.visit_numeric visitor v st opcode = .ok (.Ok (), v') := by
  unfold code.visit_numeric
  by_cases hop : opcode = code.OP_I32_EQZ
  · rw [if_pos hop]
    exact h.on_i32_eqz v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_EQ
  · rw [if_pos hop]
    exact h.on_i32_eq v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_NE
  · rw [if_pos hop]
    exact h.on_i32_ne v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_LT_S
  · rw [if_pos hop]
    exact h.on_i32_lt_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_LT_U
  · rw [if_pos hop]
    exact h.on_i32_lt_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_GT_S
  · rw [if_pos hop]
    exact h.on_i32_gt_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_GT_U
  · rw [if_pos hop]
    exact h.on_i32_gt_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_LE_S
  · rw [if_pos hop]
    exact h.on_i32_le_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_LE_U
  · rw [if_pos hop]
    exact h.on_i32_le_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_GE_S
  · rw [if_pos hop]
    exact h.on_i32_ge_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_GE_U
  · rw [if_pos hop]
    exact h.on_i32_ge_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_EQZ
  · rw [if_pos hop]
    exact h.on_i64_eqz v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_EQ
  · rw [if_pos hop]
    exact h.on_i64_eq v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_NE
  · rw [if_pos hop]
    exact h.on_i64_ne v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_LT_S
  · rw [if_pos hop]
    exact h.on_i64_lt_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_LT_U
  · rw [if_pos hop]
    exact h.on_i64_lt_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_GT_S
  · rw [if_pos hop]
    exact h.on_i64_gt_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_GT_U
  · rw [if_pos hop]
    exact h.on_i64_gt_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_LE_S
  · rw [if_pos hop]
    exact h.on_i64_le_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_LE_U
  · rw [if_pos hop]
    exact h.on_i64_le_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_GE_S
  · rw [if_pos hop]
    exact h.on_i64_ge_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_GE_U
  · rw [if_pos hop]
    exact h.on_i64_ge_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_EQ
  · rw [if_pos hop]
    exact h.on_f32_eq v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_NE
  · rw [if_pos hop]
    exact h.on_f32_ne v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_LT
  · rw [if_pos hop]
    exact h.on_f32_lt v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_GT
  · rw [if_pos hop]
    exact h.on_f32_gt v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_LE
  · rw [if_pos hop]
    exact h.on_f32_le v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_GE
  · rw [if_pos hop]
    exact h.on_f32_ge v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_EQ
  · rw [if_pos hop]
    exact h.on_f64_eq v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_NE
  · rw [if_pos hop]
    exact h.on_f64_ne v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_LT
  · rw [if_pos hop]
    exact h.on_f64_lt v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_GT
  · rw [if_pos hop]
    exact h.on_f64_gt v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_LE
  · rw [if_pos hop]
    exact h.on_f64_le v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_GE
  · rw [if_pos hop]
    exact h.on_f64_ge v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_SUB
  · rw [if_pos hop]
    exact h.on_i32_sub v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_MUL
  · rw [if_pos hop]
    exact h.on_i32_mul v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_DIV_S
  · rw [if_pos hop]
    exact h.on_i32_div_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_DIV_U
  · rw [if_pos hop]
    exact h.on_i32_div_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_REM_S
  · rw [if_pos hop]
    exact h.on_i32_rem_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_REM_U
  · rw [if_pos hop]
    exact h.on_i32_rem_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_AND
  · rw [if_pos hop]
    exact h.on_i32_and v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_OR
  · rw [if_pos hop]
    exact h.on_i32_or v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_XOR
  · rw [if_pos hop]
    exact h.on_i32_xor v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_SHL
  · rw [if_pos hop]
    exact h.on_i32_shl v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_SHR_S
  · rw [if_pos hop]
    exact h.on_i32_shr_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_SHR_U
  · rw [if_pos hop]
    exact h.on_i32_shr_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_ROTL
  · rw [if_pos hop]
    exact h.on_i32_rotl v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_ROTR
  · rw [if_pos hop]
    exact h.on_i32_rotr v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_ADD
  · rw [if_pos hop]
    exact h.on_i64_add v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_SUB
  · rw [if_pos hop]
    exact h.on_i64_sub v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_MUL
  · rw [if_pos hop]
    exact h.on_i64_mul v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_DIV_S
  · rw [if_pos hop]
    exact h.on_i64_div_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_DIV_U
  · rw [if_pos hop]
    exact h.on_i64_div_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_REM_S
  · rw [if_pos hop]
    exact h.on_i64_rem_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_REM_U
  · rw [if_pos hop]
    exact h.on_i64_rem_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_AND
  · rw [if_pos hop]
    exact h.on_i64_and v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_OR
  · rw [if_pos hop]
    exact h.on_i64_or v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_XOR
  · rw [if_pos hop]
    exact h.on_i64_xor v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_SHL
  · rw [if_pos hop]
    exact h.on_i64_shl v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_SHR_S
  · rw [if_pos hop]
    exact h.on_i64_shr_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_SHR_U
  · rw [if_pos hop]
    exact h.on_i64_shr_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_ROTL
  · rw [if_pos hop]
    exact h.on_i64_rotl v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_ROTR
  · rw [if_pos hop]
    exact h.on_i64_rotr v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_ADD
  · rw [if_pos hop]
    exact h.on_f32_add v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_SUB
  · rw [if_pos hop]
    exact h.on_f32_sub v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_MUL
  · rw [if_pos hop]
    exact h.on_f32_mul v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_DIV
  · rw [if_pos hop]
    exact h.on_f32_div v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_MIN
  · rw [if_pos hop]
    exact h.on_f32_min v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_MAX
  · rw [if_pos hop]
    exact h.on_f32_max v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_COPYSIGN
  · rw [if_pos hop]
    exact h.on_f32_copysign v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_ADD
  · rw [if_pos hop]
    exact h.on_f64_add v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_SUB
  · rw [if_pos hop]
    exact h.on_f64_sub v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_MUL
  · rw [if_pos hop]
    exact h.on_f64_mul v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_DIV
  · rw [if_pos hop]
    exact h.on_f64_div v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_MIN
  · rw [if_pos hop]
    exact h.on_f64_min v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_MAX
  · rw [if_pos hop]
    exact h.on_f64_max v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_COPYSIGN
  · rw [if_pos hop]
    exact h.on_f64_copysign v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_CLZ
  · rw [if_pos hop]
    exact h.on_i32_clz v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_CTZ
  · rw [if_pos hop]
    exact h.on_i32_ctz v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_POPCNT
  · rw [if_pos hop]
    exact h.on_i32_popcnt v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_ADD
  · rw [if_pos hop]
    exact h.on_i32_add v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_CLZ
  · rw [if_pos hop]
    exact h.on_i64_clz v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_CTZ
  · rw [if_pos hop]
    exact h.on_i64_ctz v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_POPCNT
  · rw [if_pos hop]
    exact h.on_i64_popcnt v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_ABS
  · rw [if_pos hop]
    exact h.on_f32_abs v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_NEG
  · rw [if_pos hop]
    exact h.on_f32_neg v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_CEIL
  · rw [if_pos hop]
    exact h.on_f32_ceil v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_FLOOR
  · rw [if_pos hop]
    exact h.on_f32_floor v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_TRUNC
  · rw [if_pos hop]
    exact h.on_f32_trunc v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_NEAREST
  · rw [if_pos hop]
    exact h.on_f32_nearest v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_SQRT
  · rw [if_pos hop]
    exact h.on_f32_sqrt v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_ABS
  · rw [if_pos hop]
    exact h.on_f64_abs v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_NEG
  · rw [if_pos hop]
    exact h.on_f64_neg v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_CEIL
  · rw [if_pos hop]
    exact h.on_f64_ceil v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_FLOOR
  · rw [if_pos hop]
    exact h.on_f64_floor v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_TRUNC
  · rw [if_pos hop]
    exact h.on_f64_trunc v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_NEAREST
  · rw [if_pos hop]
    exact h.on_f64_nearest v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_SQRT
  · rw [if_pos hop]
    exact h.on_f64_sqrt v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_WRAP_I64
  · rw [if_pos hop]
    exact h.on_i32_wrap_i64 v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_TRUNC_F32_S
  · rw [if_pos hop]
    exact h.on_i32_trunc_f32_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_TRUNC_F32_U
  · rw [if_pos hop]
    exact h.on_i32_trunc_f32_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_TRUNC_F64_S
  · rw [if_pos hop]
    exact h.on_i32_trunc_f64_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_TRUNC_F64_U
  · rw [if_pos hop]
    exact h.on_i32_trunc_f64_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_EXTEND_I32_S
  · rw [if_pos hop]
    exact h.on_i64_extend_i32_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_EXTEND_I32_U
  · rw [if_pos hop]
    exact h.on_i64_extend_i32_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_TRUNC_F32_S
  · rw [if_pos hop]
    exact h.on_i64_trunc_f32_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_TRUNC_F32_U
  · rw [if_pos hop]
    exact h.on_i64_trunc_f32_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_TRUNC_F64_S
  · rw [if_pos hop]
    exact h.on_i64_trunc_f64_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_TRUNC_F64_U
  · rw [if_pos hop]
    exact h.on_i64_trunc_f64_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_CONVERT_I32_S
  · rw [if_pos hop]
    exact h.on_f32_convert_i32_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_CONVERT_I32_U
  · rw [if_pos hop]
    exact h.on_f32_convert_i32_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_CONVERT_I64_S
  · rw [if_pos hop]
    exact h.on_f32_convert_i64_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_CONVERT_I64_U
  · rw [if_pos hop]
    exact h.on_f32_convert_i64_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_DEMOTE_F64
  · rw [if_pos hop]
    exact h.on_f32_demote_f64 v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_CONVERT_I32_S
  · rw [if_pos hop]
    exact h.on_f64_convert_i32_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_CONVERT_I32_U
  · rw [if_pos hop]
    exact h.on_f64_convert_i32_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_CONVERT_I64_S
  · rw [if_pos hop]
    exact h.on_f64_convert_i64_s v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_CONVERT_I64_U
  · rw [if_pos hop]
    exact h.on_f64_convert_i64_u v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_PROMOTE_F32
  · rw [if_pos hop]
    exact h.on_f64_promote_f32 v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_REINTERPRET_F32
  · rw [if_pos hop]
    exact h.on_i32_reinterpret_f32 v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_REINTERPRET_F64
  · rw [if_pos hop]
    exact h.on_i64_reinterpret_f64 v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_REINTERPRET_I32
  · rw [if_pos hop]
    exact h.on_f32_reinterpret_i32 v st
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_REINTERPRET_I64
  · rw [if_pos hop]
    exact h.on_f64_reinterpret_i64 v st
  rw [if_neg hop]
  exact ⟨v, rfl⟩

/-- Memory dispatch invokes only one of the explicitly total hooks. -/
theorem Accepts.visit_memory {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor)
    (v : V) (st : code.OpIterState) (opcode : U8) (memarg : code.MemArg) :
    ∃ v', code.visit_memory visitor v st opcode memarg = .ok (.Ok (), v') := by
  unfold code.visit_memory
  by_cases hop : opcode = code.OP_I32_LOAD
  · rw [if_pos hop]
    exact h.on_i32_load v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_LOAD
  · rw [if_pos hop]
    exact h.on_i64_load v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_LOAD
  · rw [if_pos hop]
    exact h.on_f32_load v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_LOAD
  · rw [if_pos hop]
    exact h.on_f64_load v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_LOAD8_S
  · rw [if_pos hop]
    exact h.on_i32_load8_s v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_LOAD8_U
  · rw [if_pos hop]
    exact h.on_i32_load8_u v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_LOAD16_S
  · rw [if_pos hop]
    exact h.on_i32_load16_s v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_LOAD16_U
  · rw [if_pos hop]
    exact h.on_i32_load16_u v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_LOAD8_S
  · rw [if_pos hop]
    exact h.on_i64_load8_s v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_LOAD8_U
  · rw [if_pos hop]
    exact h.on_i64_load8_u v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_LOAD16_S
  · rw [if_pos hop]
    exact h.on_i64_load16_s v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_LOAD16_U
  · rw [if_pos hop]
    exact h.on_i64_load16_u v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_LOAD32_S
  · rw [if_pos hop]
    exact h.on_i64_load32_s v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_LOAD32_U
  · rw [if_pos hop]
    exact h.on_i64_load32_u v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_STORE
  · rw [if_pos hop]
    exact h.on_i32_store v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_STORE
  · rw [if_pos hop]
    exact h.on_i64_store v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F32_STORE
  · rw [if_pos hop]
    exact h.on_f32_store v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_F64_STORE
  · rw [if_pos hop]
    exact h.on_f64_store v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_STORE8
  · rw [if_pos hop]
    exact h.on_i32_store8 v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I32_STORE16
  · rw [if_pos hop]
    exact h.on_i32_store16 v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_STORE8
  · rw [if_pos hop]
    exact h.on_i64_store8 v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_STORE16
  · rw [if_pos hop]
    exact h.on_i64_store16 v st memarg
  rw [if_neg hop]
  by_cases hop : opcode = code.OP_I64_STORE32
  · rw [if_pos hop]
    exact h.on_i64_store32 v st memarg
  rw [if_neg hop]
  exact ⟨v, rfl⟩

end Itasca.FullVisitor
