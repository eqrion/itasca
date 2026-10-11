import Itasca.Visitor.FullVisitor

open Aeneas Aeneas.Std

namespace Itasca.FullVisitor

/-- Every actual hook terminates successfully. Visitor state may change freely. -/
structure Accepts {V : Type} (visitor : code.OpVisitor V) : Prop where
  on_function_start : ∀ (v : V) (a1 : _root_.Itasca.code.Context) (a2 : Std.U32) (a3 : Std.Usize) (a4 : Std.Usize), ∃ v', visitor.on_function_start v a1 a2 a3 a4 = .ok (.Ok (), v')
  on_unreachable : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_unreachable v a1 = .ok (.Ok (), v')
  on_nop : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_nop v a1 = .ok (.Ok (), v')
  on_block : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.signature.BlockType), ∃ v', visitor.on_block v a1 a2 = .ok (.Ok (), v')
  on_loop : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.signature.BlockType), ∃ v', visitor.on_loop v a1 a2 = .ok (.Ok (), v')
  on_if : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.signature.BlockType), ∃ v', visitor.on_if v a1 a2 = .ok (.Ok (), v')
  on_else : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.signature.BlockType), ∃ v', visitor.on_else v a1 a2 = .ok (.Ok (), v')
  on_end : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : _root_.Itasca.code.LabelKind) (a3 : _root_.Itasca.signature.BlockType), ∃ v', visitor.on_end v a1 a2 a3 = .ok (.Ok (), v')
  on_br : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32) (a3 : _root_.Itasca.signature.ResultType), ∃ v', visitor.on_br v a1 a2 a3 = .ok (.Ok (), v')
  on_br_if : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32) (a3 : _root_.Itasca.signature.ResultType), ∃ v', visitor.on_br_if v a1 a2 a3 = .ok (.Ok (), v')
  on_br_table_label : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_br_table_label v a1 a2 = .ok (.Ok (), v')
  on_br_table : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32) (a3 : _root_.Itasca.signature.ResultType), ∃ v', visitor.on_br_table v a1 a2 a3 = .ok (.Ok (), v')
  on_return : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_return v a1 = .ok (.Ok (), v')
  on_call : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_call v a1 a2 = .ok (.Ok (), v')
  on_call_indirect : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState) (a2 : Std.U32) (a3 : Std.U32), ∃ v', visitor.on_call_indirect v a1 a2 a3 = .ok (.Ok (), v')
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
  on_i32_extend8_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_extend8_s v a1 = .ok (.Ok (), v')
  on_i32_extend16_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_extend16_s v a1 = .ok (.Ok (), v')
  on_i64_extend8_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_extend8_s v a1 = .ok (.Ok (), v')
  on_i64_extend16_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_extend16_s v a1 = .ok (.Ok (), v')
  on_i64_extend32_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_extend32_s v a1 = .ok (.Ok (), v')
  on_i32_trunc_sat_f32_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_trunc_sat_f32_s v a1 = .ok (.Ok (), v')
  on_i32_trunc_sat_f32_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_trunc_sat_f32_u v a1 = .ok (.Ok (), v')
  on_i32_trunc_sat_f64_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_trunc_sat_f64_s v a1 = .ok (.Ok (), v')
  on_i32_trunc_sat_f64_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i32_trunc_sat_f64_u v a1 = .ok (.Ok (), v')
  on_i64_trunc_sat_f32_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_trunc_sat_f32_s v a1 = .ok (.Ok (), v')
  on_i64_trunc_sat_f32_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_trunc_sat_f32_u v a1 = .ok (.Ok (), v')
  on_i64_trunc_sat_f64_s : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_trunc_sat_f64_s v a1 = .ok (.Ok (), v')
  on_i64_trunc_sat_f64_u : ∀ (v : V) (a1 : _root_.Itasca.code.OpIterState), ∃ v', visitor.on_i64_trunc_sat_f64_u v a1 = .ok (.Ok (), v')
  on_ref_null : ∀ (v : V) (a1 : code.OpIterState) (a2 : types.ElemType), ∃ v', visitor.on_ref_null v a1 a2 = .ok (.Ok (), v')
  on_ref_is_null : ∀ (v : V) (a1 : code.OpIterState), ∃ v', visitor.on_ref_is_null v a1 = .ok (.Ok (), v')
  on_ref_func : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_ref_func v a1 a2 = .ok (.Ok (), v')
  on_select_typed : ∀ (v : V) (a1 : code.OpIterState) (a2 : types.ValueType), ∃ v', visitor.on_select_typed v a1 a2 = .ok (.Ok (), v')
  on_table_get : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_table_get v a1 a2 = .ok (.Ok (), v')
  on_table_set : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_table_set v a1 a2 = .ok (.Ok (), v')
  on_memory_init : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_memory_init v a1 a2 = .ok (.Ok (), v')
  on_data_drop : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_data_drop v a1 a2 = .ok (.Ok (), v')
  on_memory_copy : ∀ (v : V) (a1 : code.OpIterState), ∃ v', visitor.on_memory_copy v a1 = .ok (.Ok (), v')
  on_memory_fill : ∀ (v : V) (a1 : code.OpIterState), ∃ v', visitor.on_memory_fill v a1 = .ok (.Ok (), v')
  on_table_init : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U32) (a3 : Std.U32), ∃ v', visitor.on_table_init v a1 a2 a3 = .ok (.Ok (), v')
  on_elem_drop : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_elem_drop v a1 a2 = .ok (.Ok (), v')
  on_table_copy : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U32) (a3 : Std.U32), ∃ v', visitor.on_table_copy v a1 a2 a3 = .ok (.Ok (), v')
  on_table_grow : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_table_grow v a1 a2 = .ok (.Ok (), v')
  on_table_size : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_table_size v a1 a2 = .ok (.Ok (), v')
  on_table_fill : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_table_fill v a1 a2 = .ok (.Ok (), v')
  on_simd : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U32), ∃ v', visitor.on_simd v a1 a2 = .ok (.Ok (), v')
  on_simd_lane : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U32) (a3 : Std.U8), ∃ v', visitor.on_simd_lane v a1 a2 a3 = .ok (.Ok (), v')
  on_simd_memory : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U32) (a3 : code.MemArg), ∃ v', visitor.on_simd_memory v a1 a2 a3 = .ok (.Ok (), v')
  on_simd_memory_lane : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U32) (a3 : code.MemArg) (a4 : Std.U8), ∃ v', visitor.on_simd_memory_lane v a1 a2 a3 a4 = .ok (.Ok (), v')
  on_simd_const : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U64) (a3 : Std.U64), ∃ v', visitor.on_simd_const v a1 a2 a3 = .ok (.Ok (), v')
  on_simd_shuffle : ∀ (v : V) (a1 : code.OpIterState) (a2 : Std.U64) (a3 : Std.U64), ∃ v', visitor.on_simd_shuffle v a1 a2 a3 = .ok (.Ok (), v')

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
  · intro v a1 a2 a3
    obtain ⟨v', hv⟩ := h.on_call_indirect v a1 a2 a3
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
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_extend8_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_extend16_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_extend8_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_extend16_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_extend32_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_trunc_sat_f32_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_trunc_sat_f32_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_trunc_sat_f64_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i32_trunc_sat_f64_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_trunc_sat_f32_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_trunc_sat_f32_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_trunc_sat_f64_s v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_i64_trunc_sat_f64_u v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_ref_null v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_ref_is_null v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_ref_func v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_select_typed v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_table_get v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_table_set v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_memory_init v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_data_drop v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_memory_copy v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1
    obtain ⟨v', hv⟩ := h.on_memory_fill v a1
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2 a3
    obtain ⟨v', hv⟩ := h.on_table_init v a1 a2 a3
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_elem_drop v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2 a3
    obtain ⟨v', hv⟩ := h.on_table_copy v a1 a2 a3
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_table_grow v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_table_size v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_table_fill v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2
    obtain ⟨v', hv⟩ := h.on_simd v a1 a2
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2 a3
    obtain ⟨v', hv⟩ := h.on_simd_lane v a1 a2 a3
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2 a3
    obtain ⟨v', hv⟩ := h.on_simd_memory v a1 a2 a3
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2 a3 a4
    obtain ⟨v', hv⟩ := h.on_simd_memory_lane v a1 a2 a3 a4
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2 a3
    obtain ⟨v', hv⟩ := h.on_simd_const v a1 a2 a3
    exact ⟨.Ok (), v', hv⟩
  · intro v a1 a2 a3
    obtain ⟨v', hv⟩ := h.on_simd_shuffle v a1 a2 a3
    exact ⟨.Ok (), v', hv⟩

set_option maxHeartbeats 4000000 in
/-- Numeric dispatch invokes only one of the explicitly total hooks. -/
theorem Accepts.visit_numeric {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor)
    (v : V) (st : code.OpIterState) (opcode : U8) :
    ∃ v', code.visit_numeric visitor v st opcode = .ok (.Ok (), v') := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n
  case «69» => exact h.on_i32_eqz v st
  case «70» => exact h.on_i32_eq v st
  case «71» => exact h.on_i32_ne v st
  case «72» => exact h.on_i32_lt_s v st
  case «73» => exact h.on_i32_lt_u v st
  case «74» => exact h.on_i32_gt_s v st
  case «75» => exact h.on_i32_gt_u v st
  case «76» => exact h.on_i32_le_s v st
  case «77» => exact h.on_i32_le_u v st
  case «78» => exact h.on_i32_ge_s v st
  case «79» => exact h.on_i32_ge_u v st
  case «80» => exact h.on_i64_eqz v st
  case «81» => exact h.on_i64_eq v st
  case «82» => exact h.on_i64_ne v st
  case «83» => exact h.on_i64_lt_s v st
  case «84» => exact h.on_i64_lt_u v st
  case «85» => exact h.on_i64_gt_s v st
  case «86» => exact h.on_i64_gt_u v st
  case «87» => exact h.on_i64_le_s v st
  case «88» => exact h.on_i64_le_u v st
  case «89» => exact h.on_i64_ge_s v st
  case «90» => exact h.on_i64_ge_u v st
  case «91» => exact h.on_f32_eq v st
  case «92» => exact h.on_f32_ne v st
  case «93» => exact h.on_f32_lt v st
  case «94» => exact h.on_f32_gt v st
  case «95» => exact h.on_f32_le v st
  case «96» => exact h.on_f32_ge v st
  case «97» => exact h.on_f64_eq v st
  case «98» => exact h.on_f64_ne v st
  case «99» => exact h.on_f64_lt v st
  case «100» => exact h.on_f64_gt v st
  case «101» => exact h.on_f64_le v st
  case «102» => exact h.on_f64_ge v st
  case «107» => exact h.on_i32_sub v st
  case «108» => exact h.on_i32_mul v st
  case «109» => exact h.on_i32_div_s v st
  case «110» => exact h.on_i32_div_u v st
  case «111» => exact h.on_i32_rem_s v st
  case «112» => exact h.on_i32_rem_u v st
  case «113» => exact h.on_i32_and v st
  case «114» => exact h.on_i32_or v st
  case «115» => exact h.on_i32_xor v st
  case «116» => exact h.on_i32_shl v st
  case «117» => exact h.on_i32_shr_s v st
  case «118» => exact h.on_i32_shr_u v st
  case «119» => exact h.on_i32_rotl v st
  case «120» => exact h.on_i32_rotr v st
  case «124» => exact h.on_i64_add v st
  case «125» => exact h.on_i64_sub v st
  case «126» => exact h.on_i64_mul v st
  case «127» => exact h.on_i64_div_s v st
  case «128» => exact h.on_i64_div_u v st
  case «129» => exact h.on_i64_rem_s v st
  case «130» => exact h.on_i64_rem_u v st
  case «131» => exact h.on_i64_and v st
  case «132» => exact h.on_i64_or v st
  case «133» => exact h.on_i64_xor v st
  case «134» => exact h.on_i64_shl v st
  case «135» => exact h.on_i64_shr_s v st
  case «136» => exact h.on_i64_shr_u v st
  case «137» => exact h.on_i64_rotl v st
  case «138» => exact h.on_i64_rotr v st
  case «146» => exact h.on_f32_add v st
  case «147» => exact h.on_f32_sub v st
  case «148» => exact h.on_f32_mul v st
  case «149» => exact h.on_f32_div v st
  case «150» => exact h.on_f32_min v st
  case «151» => exact h.on_f32_max v st
  case «152» => exact h.on_f32_copysign v st
  case «160» => exact h.on_f64_add v st
  case «161» => exact h.on_f64_sub v st
  case «162» => exact h.on_f64_mul v st
  case «163» => exact h.on_f64_div v st
  case «164» => exact h.on_f64_min v st
  case «165» => exact h.on_f64_max v st
  case «166» => exact h.on_f64_copysign v st
  case «103» => exact h.on_i32_clz v st
  case «104» => exact h.on_i32_ctz v st
  case «105» => exact h.on_i32_popcnt v st
  case «106» => exact h.on_i32_add v st
  case «121» => exact h.on_i64_clz v st
  case «122» => exact h.on_i64_ctz v st
  case «123» => exact h.on_i64_popcnt v st
  case «139» => exact h.on_f32_abs v st
  case «140» => exact h.on_f32_neg v st
  case «141» => exact h.on_f32_ceil v st
  case «142» => exact h.on_f32_floor v st
  case «143» => exact h.on_f32_trunc v st
  case «144» => exact h.on_f32_nearest v st
  case «145» => exact h.on_f32_sqrt v st
  case «153» => exact h.on_f64_abs v st
  case «154» => exact h.on_f64_neg v st
  case «155» => exact h.on_f64_ceil v st
  case «156» => exact h.on_f64_floor v st
  case «157» => exact h.on_f64_trunc v st
  case «158» => exact h.on_f64_nearest v st
  case «159» => exact h.on_f64_sqrt v st
  case «167» => exact h.on_i32_wrap_i64 v st
  case «168» => exact h.on_i32_trunc_f32_s v st
  case «169» => exact h.on_i32_trunc_f32_u v st
  case «170» => exact h.on_i32_trunc_f64_s v st
  case «171» => exact h.on_i32_trunc_f64_u v st
  case «172» => exact h.on_i64_extend_i32_s v st
  case «173» => exact h.on_i64_extend_i32_u v st
  case «174» => exact h.on_i64_trunc_f32_s v st
  case «175» => exact h.on_i64_trunc_f32_u v st
  case «176» => exact h.on_i64_trunc_f64_s v st
  case «177» => exact h.on_i64_trunc_f64_u v st
  case «178» => exact h.on_f32_convert_i32_s v st
  case «179» => exact h.on_f32_convert_i32_u v st
  case «180» => exact h.on_f32_convert_i64_s v st
  case «181» => exact h.on_f32_convert_i64_u v st
  case «182» => exact h.on_f32_demote_f64 v st
  case «183» => exact h.on_f64_convert_i32_s v st
  case «184» => exact h.on_f64_convert_i32_u v st
  case «185» => exact h.on_f64_convert_i64_s v st
  case «186» => exact h.on_f64_convert_i64_u v st
  case «187» => exact h.on_f64_promote_f32 v st
  case «188» => exact h.on_i32_reinterpret_f32 v st
  case «189» => exact h.on_i64_reinterpret_f64 v st
  case «190» => exact h.on_f32_reinterpret_i32 v st
  case «191» => exact h.on_f64_reinterpret_i64 v st
  all_goals exact ⟨v, rfl⟩

/-- Memory dispatch invokes only one of the explicitly total hooks. -/
theorem Accepts.visit_memory {V : Type} {visitor : code.OpVisitor V} (h : Accepts visitor)
    (v : V) (st : code.OpIterState) (opcode : U8) (memarg : code.MemArg) :
    ∃ v', code.visit_memory visitor v st opcode memarg = .ok (.Ok (), v') := by
  unfold code.visit_memory
  split <;> first
  | exact h.on_i32_load v st memarg
  | exact h.on_i64_load v st memarg
  | exact h.on_f32_load v st memarg
  | exact h.on_f64_load v st memarg
  | exact h.on_i32_load8_s v st memarg
  | exact h.on_i32_load8_u v st memarg
  | exact h.on_i32_load16_s v st memarg
  | exact h.on_i32_load16_u v st memarg
  | exact h.on_i64_load8_s v st memarg
  | exact h.on_i64_load8_u v st memarg
  | exact h.on_i64_load16_s v st memarg
  | exact h.on_i64_load16_u v st memarg
  | exact h.on_i64_load32_s v st memarg
  | exact h.on_i64_load32_u v st memarg
  | exact h.on_i32_store v st memarg
  | exact h.on_i64_store v st memarg
  | exact h.on_f32_store v st memarg
  | exact h.on_f64_store v st memarg
  | exact h.on_i32_store8 v st memarg
  | exact h.on_i32_store16 v st memarg
  | exact h.on_i64_store8 v st memarg
  | exact h.on_i64_store16 v st memarg
  | exact h.on_i64_store32 v st memarg
  | exact ⟨v, rfl⟩

end Itasca.FullVisitor
