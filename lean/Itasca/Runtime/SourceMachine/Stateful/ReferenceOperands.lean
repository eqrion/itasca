import Itasca.Runtime.SourceMachine.Stateful.Reference
namespace Itasca.Runtime.Abs.Stateful
open SpecExt Itasca.Runtime.Spec

theorem reference_operand {s : store} {value : val} {type : reftype}
    (typed : Val_ok s value (valtype_reftype type)) :
    ∃ reference, value = val_ref reference ∧ Ref_ok s reference type := by
  generalize equation : valtype_reftype type = actual at typed
  cases typed with
  | numtype nt _ _ _ => cases type <;> cases nt <;> cases equation
  | vectype vt _ _ _ => cases type <;> cases vt <;> cases equation
  | reftype reference actualType referenceTyped _ =>
    have same : actualType = type := by cases type <;> cases actualType <;> simp_all [valtype_reftype]
    subst actualType
    exact ⟨reference,rfl,referenceTyped⟩

@[simp] theorem reference_admin_value (value : ref) : admininstr_val (val_ref value) = admininstr_ref value := by
  cases value <;> rfl
end Itasca.Runtime.Abs.Stateful
