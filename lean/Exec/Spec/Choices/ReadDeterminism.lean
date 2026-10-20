import Exec.Spec.Choices.VectorReadUniqueness
import Exec.Spec.Choices.FunctionEntryUniqueness
import Exec.Spec.Choices.StructuredReadUniqueness

/-! Every generated read reduction has a unique result. Guard partitions,
canonical defaults, and bounded scalar/SIMD byte decoding rule out accidental
alternatives independently of any interpreter execution. -/

namespace Exec.Spec
open SpecExt
private def lastReadInstruction : config → Option admininstr
  | ⟨_,body⟩ => body.getLast?

set_option maxHeartbeats 8000000 in
theorem read_deterministic {before other : config} {left right : List admininstr}
    (first : Step_read before left) (second : Step_read other right) (same : before=other) : left=right := by
  have last := congrArg lastReadInstruction same
  cases first
  all_goals cases second <;> simp [lastReadInstruction,Map] at last
  all_goals simp [config.mk_config.injEq] at same
  all_goals try casesm* _ ∧ _
  all_goals subst_vars
  all_goals try rfl
  all_goals try contradiction
  all_goals try { solve_by_elim (maxDepth := 12) [Step_read_before_call_indirect_trap.call_indirect_call_0] }
  all_goals try { repeat' first | casesm* fun_memarg0 _ | casesm* fun_iadd_ _ _ _ _
                  all_goals grind }
  all_goals try { norm_num [Ki] at *; grind }
  case load_num_trap.load_num_val | load_num_val.load_num_trap =>
    casesm* wf_admininstr (.CONST _ _)
    have bound := numeric_read_rule_bound (by assumption) (by assumption)
    casesm* numtype
    all_goals norm_num [valtype_numtype,size,rat_to_nat] at *
    all_goals omega
  case load_num_val.load_num_val =>
    apply congrArg (fun value => [admininstr.CONST _ value])
    apply numericBytes_injective
    · casesm* wf_admininstr (.CONST _ _); assumption
    · casesm* wf_admininstr (.CONST _ _); assumption
    · grind
  case load_pack_trap.load_pack_val | load_pack_val.load_pack_trap =>
    have inside := source_packed_read_inside (by assumption) (by assumption)
    omega
  case load_pack_val.load_pack_val =>
    have width := source_load_packed_width (by assumption)
    grind [bounded_integer_encoding_unique,bounded_integer_read_inside]
  case call_addr.call_addr =>
    dsimp only [Map,funccode_func] at *
    apply source_function_entry_unique <;> assumption
  case vload_oob.vload_val | vload_val.vload_oob =>
    norm_num [valtype_vectype,size,rat_to_nat] at *
    have inside := Simd.vector_read_bounds _ _ _ (by assumption)
    omega
  case vload_val.vload_val =>
    apply congrArg (fun value => [admininstr.VCONST .V128 value])
    apply vectorBytes_injective
    · assumption
    · assumption
    · grind
  case vload_splat_oob.vload_splat_val | vload_splat_val.vload_splat_oob |
      vload_lane_oob.vload_lane_val | vload_lane_val.vload_lane_oob =>
    have inside := source_lane_read_inside (by assumption)
    omega
  case vload_splat_val.vload_splat_val =>
    apply source_splat_unique
    all_goals first | assumption | grind
  case vload_lane_val.vload_lane_val =>
    apply source_lane_load_unique
    all_goals first | assumption | grind
  case vload_zero_oob.vload_zero_val | vload_zero_val.vload_zero_oob =>
    have inside := source_zero_read_inside (by assumption) (by assumption)
    omega
  case vload_zero_val.vload_zero_val =>
    apply source_zero_values_unique (source_zero_read_width (by assumption))
    all_goals first | assumption | grind
  case vload_shape_oob.vload_shape_val | vload_shape_val.vload_shape_oob =>
    have operation := source_vector_load_operation (by assumption)
    cases operation
    have inside := source_widening_read_inside (by assumption) (by assumption) (by assumption) (by assumption)
    omega
  case vload_shape_val.vload_shape_val =>
    have operation := source_vector_load_operation (by assumption)
    cases operation
    apply source_widening_values_unique
    all_goals assumption

theorem read_same_input_deterministic {before : config} {left right : List admininstr}
    (first : Step_read before left) (second : Step_read before right) : left=right :=
  read_deterministic first second rfl

end Exec.Spec
