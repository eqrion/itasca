import Exec.Theorems.Host.Open.Source.State.RootCall
import Exec.Theorems.Api.InvocationPrimitiveResources
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Source entry capacities and primitive allocation/interrupt laws exclude a
fresh root's preparation refusal. No whole-call normality is assumed. -/
theorem SourceRootCallCause.impossible {M A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform Unit M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {token : Unit} {address : runtime.FuncAddr}
    {signature : Itasca.types.FuncType} {error : runtime.ExecError}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    (held : ExecutableInv view code store) (empty : exec.frames.val=[])
    (positive : 0<store.limits.max_frames.val)
    (signatureFits : signatureWords (Store.decodeFuncType signature)≤store.limits.max_values.val)
    (entryFits : ∀words,SourceCanonicalFunctionCapacity (Store.decodeStore view code store) address.index.val words →
      words≤store.limits.max_values.val)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀before after,hooks.interrupt before≠.ok (.Terminate,after))
    (cause : SourceRootCallCause allocator hooks exec store token address signature error) : False := by
  cases cause with
  | defined function instanceIndex functionIndex inst compiled functionAt kind instanceAt compiledAt cause =>
    obtain ⟨words,capacity,storage⟩ := function_canonical_capacity_decoded view code store held.capacities held.typed
      address function instanceIndex functionIndex inst compiled functionAt kind instanceAt compiledAt
    have fits := entryFits words capacity
    exact cause.impossible_of_resources available continuing
      (by simpa only [alloc.vec.Vec.length,empty,List.length_nil] using positive)
      (by scalar_tac) (by scalar_tac) (by scalar_tac)
  | host function identity functionAt kind cause =>
    cases error <;> simp only [HostPreparationCause] at cause
    all_goals try contradiction
    case Terminated =>
      obtain ⟨after,refused⟩:=cause
      exact continuing _ _ refused
    case Exhausted resource =>
      cases resource <;> simp only [HostPreparationCause] at cause
      all_goals try contradiction
      case Values =>
        have exceeds : store.limits.max_values.val<signatureWords (Store.decodeFuncType signature) := by
          simpa only [hostSlotDemand,signatureWords,Store.decodeFuncType,typeSlots,
            show (0#usize).val=0 from rfl,Nat.zero_add,Nat.max_comm] using cause
        omega
      case Allocation =>
        rcases cause with ⟨n,bound,refused⟩ | ⟨n,bound,refused⟩ | ⟨n,bound,refused⟩
        · exact reserve_ne_refusal_of_universal_bound available exec.slots n refused
        · exact reserve_ne_refusal_of_universal_bound available exec.host_args n refused
        · exact reserve_ne_refusal_of_universal_bound available exec.host_results n refused
end Exec.Theorems.OpenReentrantControl
