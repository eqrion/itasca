import Itasca.Support.TypeTranslation

open Aeneas Aeneas.Std

namespace Itasca.Spec

/-- SpecTec represents an i32 constant by its unsigned 32-bit bit pattern. -/
def i32Const (value : I32) : instr :=
  .CONST .I32 (.mk_num__0 .I32 (.mk_uN (value.val % 4294967296).toNat))

theorem i32Const_wf (value : I32) : wf_instr (i32Const value) := by
  apply wf_instr.instr_case_13
  apply wf_num_.num__case_0 _ .I32 _ (by decide) _ rfl
  apply wf_uN.uN_case_0
  have hmod := Int.emod_lt_of_pos value.val (by decide : (0 : Int) < 4294967296)
  have hnonneg := Int.emod_nonneg value.val (by decide : (4294967296 : Int) ≠ 0)
  norm_num [size, valtype_Inn] at hmod hnonneg ⊢
  omega

theorem label_wf (depth : U32) : wf_uN 32 (.mk_uN depth.val) := by
  apply wf_uN.uN_case_0
  have h := depth.hmax
  norm_num at h ⊢
  omega

end Itasca.Spec
