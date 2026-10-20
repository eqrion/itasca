import Exec.Theorems.Composition.Supported.ChosenFailureErasure
import Exec.Theorems.Composition.Supported.SupportedSourceResources
import Exec.Interp.Calls.ResourcesAdequate
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp

/-- Independent source storage conditions at a dispatch state. Function words
come from canonical validation traces, including suspended caller operands. -/
structure SourceDispatchResources (limits : runtime.store.StoreLimits) (source : Abs.AState) : Prop where
  frames : frameDepth (Abs.decode source)<limits.max_frames.val
  values : ∀ address base words, SourceInvocationSite source address base →
    SourceCanonicalFunctionCapacity source.store address words → base+words≤limits.max_values.val

/-- Sufficient source storage and primitive allocator/interrupt laws exclude
all nontrap failures at the actual dispatch point. -/
theorem ChosenCumulativeFailure.resources_trap {choices : SourceChoices} {occurrence : Nat}
    {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop} {M P A : Type}
    {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : Abs.AState} {expected pc pending error bound}
    (invariant : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec source expected pc pending)
    (capacities : Store.FunctionCapacities code store) (typed : CoreFunctionsTyped view code store)
    (resources : SourceDispatchResources store.limits source)
    (available : Platform.AllocationAvailable allocator bound)
    (continuing : ∀ before after,hooks.interrupt before≠.ok (.Terminate,after))
    (frameBound : store.limits.max_frames.val≤bound) (valueBound : store.limits.max_values.val≤bound)
    (failure : ChosenCumulativeFailure choices occurrence allocator hooks exec store platform source error) :
    ∃ trap,error=.Trap trap ∧ CumulativeTrap trap := by
  have room : exec.frames.length<store.limits.max_frames.val := by
    rw [invariant.stack.depth]
    exact resources.frames
  rcases failure with ⟨kind,steps⟩ | ⟨rfl,after,refused⟩ | rejected
  · exact kind
  · exact False.elim (continuing _ _ refused)
  · obtain ⟨index,raw,inst,compiled,_,_,_,_,cause⟩ := rejected
    rcases cause with direct | ⟨interpretation,indirect⟩
    · obtain ⟨target,offset,pc,address,base,function,ii,fi,callee,calleeCode,fetch,resolved,found,defined,hi,hc,baseEq,pcEq,rejection,site⟩ := direct
      obtain ⟨words,capacity,storage⟩ := function_canonical_capacity_decoded view code store capacities typed address function ii fi callee calleeCode found defined hi hc
      have adequate := resources.values address.index.val base.val words (Or.inl site) (by simpa only [invariant.storeEq] using capacity)
      exact False.elim (rejection.impossible_of_resources available continuing
        (by simpa only [alloc.vec.Vec.set_length] using room) (by omega) frameBound valueBound)
    · obtain ⟨pc,address,base,function,ii,fi,inst,callee,found,defined,hi,hc,rejection,site⟩ := indirect.source_site view code invariant.storeEq
      obtain ⟨words,capacity,storage⟩ := function_canonical_capacity_decoded view code store capacities typed {store:=store.id,index:=address} function ii fi inst callee found defined hi hc
      have adequate := resources.values address.val base.val words (Or.inr site) (by simpa only [invariant.storeEq] using capacity)
      exact False.elim (rejection.impossible_of_resources available continuing
        (by simpa only [alloc.vec.Vec.set_length] using room) (by omega) frameBound valueBound)
end Exec.Theorems
