import Exec.Spec.Choices.CoreChoiceStep
namespace Exec.Spec
open SpecExt

theorem NumericRequest.instructions_injective : Function.Injective NumericRequest.instructions := by
  intro left right same
  cases left <;> cases right <;> simp_all [NumericRequest.instructions]

theorem VectorRequest.instructions_injective : Function.Injective VectorRequest.instructions := by
  intro left right same
  cases left <;> cases right <;> simp_all [VectorRequest.instructions]

theorem host_function_unique {s : store} {address : funcaddr} {leftId rightId : Nat}
    {leftParams leftResults rightParams rightResults : List valtype}
    (first : HostFunction s address leftId leftParams leftResults)
    (second : HostFunction s address rightId rightParams rightResults) :
    leftId=rightId ∧ leftParams=rightParams ∧ leftResults=rightResults := by
  obtain ⟨leftObject,first⟩ := first
  obtain ⟨rightObject,second⟩ := second
  have same := Option.some.inj (first.symm.trans second)
  have code := congrArg funcinst.CODE same
  have signature := congrArg funcinst.TYPE same
  simp only [funccode.HOST.injEq] at code
  cases code
  cases signature
  exact ⟨rfl,rfl,rfl⟩

theorem ref_instruction_injective {left right : ref} (same : admininstr_ref left=admininstr_ref right) : left=right := by
  cases left <;> cases right <;> simp_all [admininstr_ref]
end Exec.Spec
