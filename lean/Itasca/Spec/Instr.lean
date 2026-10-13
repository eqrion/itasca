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

/-- An I32 constant's generated typing uses its unsigned bit pattern. -/
theorem i32Const_typed (C : context) (hC : wf_context C) (value : I32) :
    Instr_ok C (i32Const value) (.mk_functype (.mk_list []) (.mk_list [.I32])) :=
  .const C .I32 _ hC (i32Const_wf value)

theorem i32Const_framed (C : context) (hC : wf_context C) (value : I32) (ts : List valtype) :
    Instrs_ok C [i32Const value] (.mk_functype (.mk_list ts) (.mk_list (ts ++ [.I32]))) := by
  simpa using Instrs_ok.frame C [i32Const value] ts [] [.I32]
    (.instr C _ [] [.I32] (i32Const_typed C hC value) hC (i32Const_wf value))
    hC (by simpa [Forall] using i32Const_wf value)

end Itasca.Spec
