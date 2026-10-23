import Exec.Theorems.Composition.Eventful.EventfulSourceResources
import Exec.Theorems.Api.InvocationResourcesAdequate
import Exec.Contracts
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp

/-- Source storage demand at a selected point, including defined and host
callees and suspended callers. No native success or trace appears here. -/
structure SourceWorldResources (valueLimit frameLimit : Nat) (source : Abs.AState) : Prop where
  frames : frameDepth (Abs.decode source)<frameLimit
  defined : ∀ address base words,SourceInvocationSite source address base →
    SourceCanonicalFunctionCapacity source.store address words → base+words≤valueLimit
  host : ∀ address identity base params results,SourceInvocationSite source address base →
    HostFunction source.store address identity params results → base+max (Code.slots params) (Code.slots results)≤valueLimit

def ChosenWorldResources (choices : SourceChoices) (occurrence : Nat) (initial : config)
    (valueLimit frameLimit : Nat) : Prop :=
  ∀ count events source,ChosenStepsN choices occurrence count initial events (Abs.decode source) →
    SourceWorldResources valueLimit frameLimit source

theorem EventfulSourceResourceCause.excludes_boundary {M P A : Type} {hooks : runtime.platform.Platform P M}
    {allocator : runtime.platform.Alloc A} {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {machine : EventfulMachine M P view code expected} {out : EventfulDispatchResult M P} {error : runtime.ExecError}
    {valueLimit frameLimit : Nat}
    (resources : SourceWorldResources valueLimit frameLimit machine.source)
    (valueFloor : valueLimit≤machine.store.limits.max_values.val) (frameFloor : frameLimit≤machine.store.limits.max_frames.val)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (overflow : ∀ p identity args defaults nextPlatform after returned,
      hooks.call_host p machine.store identity args defaults≠.ok (.Err .StackOverflow,nextPlatform,after,returned))
    (cause : EventfulSourceResourceCause hooks allocator machine out error)
    (kind : error=.Terminated ∨ error=.Exhausted .CallStack ∨ error=.Exhausted .Values ∨ error=.Exhausted .Allocation ∨ error=.Exhausted .Objects) : False := by
  rcases kind with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨after,refused⟩ := cause
    exact continuing _ _ refused
  · rcases cause with depth | ⟨identity,p,args,defaults,returned,refused⟩
    · have bounded := resources.frames
      omega
    · exact overflow p identity args defaults _ _ returned refused
  · obtain ⟨address,base,site,defined | host⟩ := cause
    · obtain ⟨words,capacity,exceeds⟩ := defined
      have bounded := resources.defined address base words site capacity
      omega
    · obtain ⟨identity,params,results,signature,exceeds⟩ := host
      have bounded := resources.host address identity base params results site signature
      omega
  · rcases cause with ⟨address,base,words,site,capacity,refusal⟩ | ⟨address,identity,base,params,results,site,signature,refusal⟩
    · rcases refusal with ⟨slots,n,amount,refused⟩ | ⟨frames,refused⟩
      · exact reserve_ne_refusal_of_universal_bound available slots n refused
      · exact reserve_ne_refusal_of_universal_bound available frames 1#usize refused
    · rcases refusal with ⟨slots,n,amount,refused⟩ | ⟨arguments,n,amount,refused⟩ | ⟨results,n,amount,refused⟩
      · exact reserve_ne_refusal_of_universal_bound available slots n refused
      · exact reserve_ne_refusal_of_universal_bound available arguments n refused
      · exact reserve_ne_refusal_of_universal_bound available results n refused
  · exact cause
end Exec.Theorems
