import Exec.Theorems.Invocation.PublicEventfulSourceResources
import Exec.Theorems.Api.InvocationResourcesAdequate
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem InitialHostSourceResourceCause.excludes_boundary {M P A : Type}
    {hooks : runtime.platform.Platform P M} {allocator : runtime.platform.Alloc A}
    {store after : runtime.store.Store M} {identity : U64} {signature : Itasca.types.FuncType} {error : runtime.ExecError}
    (signatureFits : signatureWords (Store.decodeFuncType signature)≤store.limits.max_values.val)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (overflow : ∀p args defaults nextPlatform after returned,
      hooks.call_host p store identity args defaults≠.ok (.Err .StackOverflow,nextPlatform,after,returned))
    (cause : InitialHostSourceResourceCause hooks allocator store after identity signature error)
    (kind : error=.Terminated ∨ error=.Exhausted .CallStack ∨ error=.Exhausted .Values ∨ error=.Exhausted .Allocation ∨ error=.Exhausted .Objects) : False := by
  rcases kind with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨before,after,refused⟩ := cause
    exact continuing _ _ refused
  · obtain ⟨p,args,defaults,nextPlatform,returned,refused⟩ := cause
    exact overflow p args defaults nextPlatform after returned refused
  · exact Nat.not_lt_of_ge signatureFits cause
  · rcases cause with ⟨slots,n,amount,refused⟩ | ⟨arguments,n,amount,refused⟩ | ⟨results,n,amount,refused⟩
    · exact reserve_ne_refusal_of_universal_bound available slots n refused
    · exact reserve_ne_refusal_of_universal_bound available arguments n refused
    · exact reserve_ne_refusal_of_universal_bound available results n refused
  · exact cause
end Exec.Theorems
