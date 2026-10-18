import Exec.Spec.Wf
import Mathlib.Tactic

namespace Exec.Spec

theorem i32_successor_boundary_not_wf :
    ¬ wf_admininstr (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (2^32)))) := by
  intro h
  cases h
  rename_i hn
  cases hn
  have bounded : wf_uN 32 (.mk_uN (2^32)) := by assumption
  cases bounded with
  | uN_case_0 _ bounds => norm_num at bounds

/-- Last-byte initialization fits an allowed 4GiB memory, but the original
recursive rule's required next i32 address is not syntactically valid. -/
theorem memory_init_boundary_witness :
    (2^32-1 : Nat) + 1 ≤ 65536*65536 ∧
    (0 : Nat) + 1 ≤ 1 ∧
    wf_admininstr (.CONST .I32 (.mk_num__0 .I32 (.mk_uN (2^32-1)))) ∧
    ¬ wf_admininstr (.CONST .I32 (.mk_num__0 .I32 (.mk_uN ((2^32-1)+1)))) := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · exact .admininstr_case_13 _ _ (wf_num_.num__case_0 .I32 .I32 _ (by decide) (wf_uN.uN_case_0 _ _ (by norm_num [size, valtype_Inn])) rfl)
  · simpa using i32_successor_boundary_not_wf

/-- The repaired recursive address uses the existing 32-bit addition relation. -/
theorem memory_init_boundary_successor :
    fun_iadd_ 32 (.mk_uN (2^32-1)) (.mk_uN 1) (.mk_uN 0) ∧
    wf_admininstr (.CONST .I32 (.mk_num__0 .I32 (.mk_uN 0))) := by
  constructor
  · have h := fun_iadd_.fun_iadd__case_0 32 (.mk_uN (2^32-1)) (.mk_uN 1)
      (wf_uN.uN_case_0 _ _ (by norm_num [proj_uN_0]))
    norm_num [proj_uN_0] at h
    exact h
  · exact .admininstr_case_13 _ _ (.num__case_0 .I32 .I32 _ (by decide)
      (.uN_case_0 _ _ (by norm_num [size, valtype_Inn])) rfl)

/-- Under the range check, wrapping a successor occurs only on the final write. -/
theorem memory_init_wrap_is_final (destination count : Nat)
    (address : destination < 2^32) (positive : 0 < count)
    (range : destination + count ≤ 2^32) (wrap : destination + 1 ≥ 2^32) :
    count = 1 ∧ (destination + 1) % 2^32 = 0 := by
  have last : destination + 1 = 2^32 := by omega
  exact ⟨by omega, by rw [last]; exact Nat.mod_self _⟩
end Exec.Spec
