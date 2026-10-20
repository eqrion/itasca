import Exec.Spec.Typing.ValueSubtyping

/-! Primitive value-instruction typing inversion, including the plain and
administrative reference representations. -/

namespace Exec.Spec
open SpecExt

def instructionValue : admininstr → Option val
  | .CONST type value => some (.CONST type value)
  | .VCONST type value => some (.VCONST type value)
  | .REF_NULL type => some (.REF_NULL type)
  | .REF_FUNC_ADDR address => some (.REF_FUNC_ADDR address)
  | .REF_HOST_ADDR address => some (.REF_HOST_ADDR address)
  | _ => none

theorem instructionValue_val (value : val) : instructionValue (admininstr_val value) = some value := by
  cases value <;> rfl

theorem instructionValue_ref (value : ref) : instructionValue (admininstr_ref value) = some (val_ref value) := by
  cases value <;> rfl

set_option maxHeartbeats 1600000 in
theorem typed_value_instruction {s : store} {context : _root_.context} {instruction : admininstr}
    {value : val} {input output : List valtype}
    (typed : Instr_ok2 s context instruction (.mk_functype (.mk_list input) (.mk_list output)))
    (read : instructionValue instruction = some value) :
    input = [] ∧ ∃ type, output = [type] ∧ Val_ok s value type := by
  cases typed
  case plain =>
    rename_i instruction _ _ _ primitive
    have storeWf : wf_store s := by assumption
    have instructionWf : wf_instr instruction := by assumption
    cases instruction <;> simp [admininstr_instr,instructionValue] at read
    all_goals cases primitive
    all_goals subst value
    all_goals refine ⟨rfl,_,rfl,?_⟩
    all_goals first
    | (apply Val_ok.numtype; exact storeWf; cases instructionWf; constructor; assumption)
    | (apply Val_ok.vectype; exact storeWf; cases instructionWf; constructor <;> assumption)
    | exact Val_ok.reftype _ (.REF_NULL _) _ (.null _ _ storeWf) storeWf
  case ref =>
    rename_i reference type _ _ _
    have valid : Ref_ok s reference type := by assumption
    have storeWf : wf_store s := by assumption
    rw [instructionValue_ref] at read
    cases read
    exact ⟨rfl,_,rfl,.reftype _ _ _ valid storeWf⟩
  all_goals simp [instructionValue] at read

end Exec.Spec

