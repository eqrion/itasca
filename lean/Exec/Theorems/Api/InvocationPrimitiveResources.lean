import Exec.Theorems.Api.InvocationResourcesAdequate
import Exec.Interp.Invocation.InvokeResourceCauses
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem invocation_resource_cause_impossible {A M : Type} {allocator : runtime.platform.Alloc A}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {signature : Itasca.types.FuncType}
    {results : alloc.vec.Vec runtime.Value} {error : runtime.ExecError}
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (fits : signatureWords (Store.decodeFuncType signature)≤store.limits.max_values.val)
    (cause : InvocationResourceCause allocator exec store signature results error) : False := by
  have kind : error=.Exhausted .Values ∨ error=.Exhausted .Allocation := by
    cases error <;> simp only [InvocationResourceCause] at cause
    all_goals try contradiction
    rename_i resource
    cases resource <;> simp only [InvocationResourceCause] at cause
    all_goals try contradiction
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases kind with rfl | rfl
  · have exceeds : store.limits.max_values.val<signatureWords (Store.decodeFuncType signature) := by
      simpa only [InvocationResourceCause,signatureWords,Store.decodeFuncType,typeSlots] using cause
    omega
  · rcases cause with ⟨n,amount,refused⟩ | ⟨n,amount,refused⟩
    · exact reserve_ne_refusal_of_universal_bound available exec.slots n refused
    · exact reserve_ne_refusal_of_universal_bound available results n refused
end Exec.Theorems
