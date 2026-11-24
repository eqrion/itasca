import Itasca.Runtime.SourceMachine.Simulation
import Itasca.Runtime.SourceMachine.Typing

/-! ## Signature -/

section

namespace Itasca.SourceMachine.Simd
open SpecExt

theorem PureSignature.principal {source inputs output C signature}
    (shape : PureSignature source inputs output) (typed : Instr_ok C source signature) :
    signature = .mk_functype (.mk_list inputs) (.mk_list [output]) := by
  cases shape <;> cases typed <;> rfl

theorem PureSignature.output_numeric {source inputs output} (shape : PureSignature source inputs output) :
    output = .V128 ∨ ∃ ty : numtype, output = valtype_numtype ty := by
  cases shape <;> first | exact Or.inl rfl | exact Or.inr ⟨.I32,rfl⟩ | exact Or.inr ⟨_,rfl⟩

theorem numeric_value_typed {s : store} {value : val} {output : valtype}
    (numeric : output = .V128 ∨ ∃ ty : numtype, output = valtype_numtype ty)
    (storeWf : wf_store s) (valid : wf_val value) (typeEq : valueType value = output) :
    Val_ok s value output := by
  rw [← typeEq]
  cases value with
  | CONST ty bits => exact .numtype s ty bits storeWf valid
  | VCONST ty bits => cases ty; exact .vectype s .V128 bits storeWf valid
  | REF_NULL ty =>
    rcases numeric with numeric | ⟨nt,numeric⟩
    · cases ty <;> simp_all [valueType,valtype_reftype]
    · cases ty <;> cases nt <;> simp_all [valueType,valtype_reftype,valtype_numtype]
  | REF_FUNC_ADDR address =>
    rcases numeric with numeric | ⟨nt,numeric⟩
    · simp_all [valueType]
    · cases nt <;> simp_all [valueType,valtype_numtype]
  | REF_HOST_ADDR address =>
    rcases numeric with numeric | ⟨nt,numeric⟩
    · simp_all [valueType]
    · cases nt <;> simp_all [valueType,valtype_numtype]

end Itasca.SourceMachine.Simd

end

/-! ## Source -/

section

namespace Itasca.SourceMachine.Simd
open SpecExt

theorem MemorySignature.principal {source inputs outputs C signature}
    (shape : MemorySignature source inputs outputs) (typed : Instr_ok C source signature) :
    signature = .mk_functype (.mk_list inputs) (.mk_list outputs) := by
  cases shape <;> cases typed <;> rfl

end Itasca.SourceMachine.Simd

end
