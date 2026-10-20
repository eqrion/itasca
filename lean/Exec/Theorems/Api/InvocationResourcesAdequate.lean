import Exec.Theorems.Api.InvocationCanonicalResources
import Exec.Theorems.Composition.Supported.ChosenResourceFailure
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp

/-- A conservative primitive allocation bound covering any representable
vector and additional request. This is independent of any invocation. -/
theorem reserve_ne_refusal_of_universal_bound {A T : Type} {allocator : runtime.platform.Alloc A}
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (values : alloc.vec.Vec T) (n : Usize) : allocator.reserve values n≠.ok (false,values) := by
  have fits : values.val.length+n.val≤2*Usize.max := by scalar_tac
  rw [available T values n fits]
  simp

/-- Source requirements for setup, every reachable call and every source
frame depth. These bounds do not mention native execution or its outcome. -/
structure SourceInvocationResources (initial : config) (store : _root_.store)
    (signature : functype) (address : funcaddr) (valueLimit frameLimit : Nat) : Prop where
  signature : signatureWords signature≤valueLimit
  entry : ∀ words,SourceCanonicalFunctionCapacity store address words → words≤valueLimit
  frames : ∀ final,StepsH initial [] final → frameDepth final<frameLimit
  calls : ∀ source,StepsH initial [] (Abs.decode source) → ∀ callee base words,
    SourceInvocationSite source callee base → SourceCanonicalFunctionCapacity source.store callee words → base+words≤valueLimit

/-- Source capacities, continuing interrupts and primitive allocator
availability exclude the classified public resource/interrupt failures. -/
theorem CanonicalInvocationResourceCause.excludes_boundary {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {initial : config} {store : _root_.store}
    {signature : functype} {address : funcaddr} {valueLimit frameLimit : Nat} {error : runtime.ExecError}
    (resources : SourceInvocationResources initial store signature address valueLimit frameLimit)
    (initialWf : wf_config initial)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (cause : CanonicalInvocationResourceCause allocator hooks initial store signature address valueLimit frameLimit error)
    (kind : error=.Terminated ∨ error=.Exhausted .CallStack ∨ error=.Exhausted .Values ∨ error=.Exhausted .Allocation) : False := by
  rcases kind with rfl | rfl | rfl | rfl
  · obtain ⟨before,after,refused⟩ := cause
    exact continuing _ _ refused
  · rcases cause with depth | ⟨final,steps,depth⟩
    · have bounded := resources.frames initial (.refl initialWf)
      omega
    · have bounded := resources.frames final steps
      omega
  · rcases cause with signature | ⟨words,capacity,exceeds⟩ | ⟨source,callee,base,words,steps,site,capacity,exceeds⟩
    · exact Nat.not_lt_of_ge resources.signature signature
    · exact Nat.not_lt_of_ge (resources.entry words capacity) exceeds
    · exact Nat.not_lt_of_ge (resources.calls source steps callee base words site capacity) exceeds
  · rcases cause with signature | ⟨words,capacity,allocated⟩ | ⟨source,steps,callee,base,words,site,capacity,allocated⟩
    · rcases signature with ⟨slots,n,amount,refused⟩ | ⟨results,n,amount,refused⟩
      · exact reserve_ne_refusal_of_universal_bound available slots n refused
      · exact reserve_ne_refusal_of_universal_bound available results n refused
    · rcases allocated with ⟨slots,n,amount,refused⟩ | ⟨frames,refused⟩
      · exact reserve_ne_refusal_of_universal_bound available slots n refused
      · exact reserve_ne_refusal_of_universal_bound available frames 1#usize refused
    · rcases allocated with ⟨slots,n,amount,refused⟩ | ⟨frames,refused⟩
      · exact reserve_ne_refusal_of_universal_bound available slots n refused
      · exact reserve_ne_refusal_of_universal_bound available frames 1#usize refused
end Exec.Theorems
