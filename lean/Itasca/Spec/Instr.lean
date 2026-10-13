import Itasca.Support.TypeTranslation

/-!
# `i32.const` and label indices in SpecTec

`Spec.i32Const` encodes an extracted `i32` as a SpecTec `i32.const` instruction by its unsigned
bit pattern, with well-formedness (`i32Const_wf`) and typing (`i32Const_typed`, `i32Const_framed`).
-/

open Aeneas Aeneas.Std

namespace Itasca.Spec

/-- The SpecTec `i32.const` instruction for `value`, using its unsigned 32-bit bit pattern. -/
def i32Const (value : I32) : instr :=
  .CONST .I32 (.mk_num__0 .I32 (.mk_uN (value.val % 4294967296).toNat))

/-- The encoded `i32.const` instruction is well-formed. -/
theorem i32Const_wf (value : I32) : wf_instr (i32Const value) := by
  apply wf_instr.instr_case_13
  apply wf_num_.num__case_0 _ .I32 _ (by decide) _ rfl
  apply wf_uN.uN_case_0
  have hmod := Int.emod_lt_of_pos value.val (by decide : (0 : Int) < 4294967296)
  have hnonneg := Int.emod_nonneg value.val (by decide : (4294967296 : Int) ≠ 0)
  norm_num [size, valtype_Inn] at hmod hnonneg ⊢
  omega

/-- A `u32` label index is a well-formed 32-bit `uN`. -/
theorem label_wf (depth : U32) : wf_uN 32 (.mk_uN depth.val) := by
  apply wf_uN.uN_case_0
  have h := depth.hmax
  norm_num at h ⊢
  omega

/-- The encoded `i32.const` instruction has type `[] -> [i32]` under `Instr_ok`. -/
theorem i32Const_typed (C : context) (hC : wf_context C) (value : I32) :
    Instr_ok C (i32Const value) (.mk_functype (.mk_list []) (.mk_list [.I32])) :=
  .const C .I32 _ hC (i32Const_wf value)

/-- The encoded `i32.const` instruction is typed under `Instrs_ok` on top of any stack `ts`. -/
theorem i32Const_framed (C : context) (hC : wf_context C) (value : I32) (ts : List valtype) :
    Instrs_ok C [i32Const value] (.mk_functype (.mk_list ts) (.mk_list (ts ++ [.I32]))) := by
  simpa using Instrs_ok.frame C [i32Const value] ts [] [.I32]
    (.instr C _ [] [.I32] (i32Const_typed C hC value) hC (i32Const_wf value))
    hC (by simpa [Forall] using i32Const_wf value)

end Itasca.Spec
