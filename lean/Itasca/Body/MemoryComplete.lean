import Itasca.Body.MemoryTyping

open Aeneas Aeneas.Std

namespace Itasca.MemoryMeaning

private def Principal (C : context) (op : instr) (ins outs : List valtype) : Prop :=
  match op with
  | .LOAD nt none arg =>
      0 < C.MEMS.length ∧ (2 : Rat) ^ proj_uN_0 arg.ALIGN ≤
        (Option.get! (size (valtype_numtype nt)) : Rat) / 8 ∧ ins = [.I32] ∧ outs = [valtype_numtype nt]
  | .LOAD _ (some (.mk_loadop__0 it (.mk_loadop_Inn width _))) arg =>
      0 < C.MEMS.length ∧ (2 : Rat) ^ proj_uN_0 arg.ALIGN ≤
        (proj_sz_0 width : Rat) / 8 ∧ ins = [.I32] ∧ outs = [valtype_Inn it]
  | .STORE nt none arg =>
      0 < C.MEMS.length ∧ (2 : Rat) ^ proj_uN_0 arg.ALIGN ≤
        (Option.get! (size (valtype_numtype nt)) : Rat) / 8 ∧ ins = [.I32, valtype_numtype nt] ∧ outs = []
  | .STORE nt (some width) arg =>
      0 < C.MEMS.length ∧ (2 : Rat) ^ proj_uN_0 arg.ALIGN ≤
        (proj_sz_0 width : Rat) / 8 ∧ ins = [.I32, valtype_numtype nt] ∧ outs = []
  | _ => True

private theorem principal {C op ins outs}
    (h : Instr_ok C op (.mk_functype (.mk_list ins) (.mk_list outs))) : Principal C op ins outs := by
  have hinn (i : Inn) : valtype_numtype (numtype_Inn i) = valtype_Inn i := by cases i <;> rfl
  cases h <;> simp_all [Principal, proj_sz_0]

/-- Principal generated typing recovers every runtime memory precondition,
including the exponent bound used by the Wasm 1.0 alignment check. -/
theorem opcodeMeaning_inverse (opcode : U8) (operation : Operation)
    (hrow : opcodeMeaning opcode = some operation) (C : context) (arg : code.MemArg)
    (ins outs : List valtype)
    (ht : Instr_ok C (operation.op arg) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    0 < C.MEMS.length ∧ arg.align.val ≤ operation.naturalAlign.val ∧
      ins = operation.inputs.map Translate.valueType ∧
      outs = operation.outputs.map Translate.valueType := by
  have hp := principal ht
  unfold opcodeMeaning at hrow
  split at hrow <;> cases hrow
  all_goals simp only [fullLoad, fullStore, packedLoad, packedStore, Principal] at hp
  all_goals obtain ⟨hm, ha, rfl, rfl⟩ := hp
  all_goals refine ⟨hm, ?_, rfl, rfl⟩
  all_goals apply (pow_le_pow_iff_right₀ (a := (2 : Rat)) (by norm_num)).mp
  all_goals norm_num [memArg, proj_uN_0, proj_sz_0, valtype_numtype, size] at *
  all_goals assumption

end Itasca.MemoryMeaning
