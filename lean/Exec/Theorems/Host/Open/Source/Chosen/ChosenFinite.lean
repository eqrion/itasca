import Exec.Theorems.Host.Open.Source.State.Finite
import Exec.Theorems.Host.Open.Source.Chosen.TickChosenDone
import Exec.Theorems.Host.Open.Source.State.TickLimits
import Exec.Theorems.Host.Open.Completeness.ChosenSourceResources
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp
/-- Every finite actual root trace retains its selected source choices,
expanded observations and reached store. Source-only capacities and primitive
availability exclude invocation cutoffs throughout the combined execution. -/
theorem normal_trace_chosen_source {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (admissible : choices.wasm.Admissible)
    (numericChoice : choices.wasm.numeric=Spec.firstNumericChoice)
    (vectorChoice : choices.wasm.vector=Spec.firstVectorChoice)
    (growthCompatible : GrowthChoicesCompatible memory allocator view choices.wasm)
    (apiCompatible : SourceAPIChoicesCompatible memory allocator view choices)
    (publicationCompatible : SourcePublicationChoicesCompatible memory floats allocator view choices)
    {native : State M} {outcome : Outcome M} {ticks : Nat}
    (trace : NormalTrace (tick memory floats allocator select) ticks native outcome)
    (occurrence : Nat) (code : Store.CodeInterpretation) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (shape : native.Shape .invocation) (noOverflow : NoOverflowMode native.mode)
    (ownerEq : owner=native.store.id)
    (resources : ChosenSourceResources (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence native.store.limits source)
    (available : Platform.AllocationAvailable allocator (2*Usize.max)) :
    ∃afterCode completed count events,
      ReentrantCallbacks.Effect view code native.store afterCode outcome.store ∧
      Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
        (sourceControlChoices choices) occurrence count source events completed ∧
      completed.Typed ∧ SourceOutcome view afterCode outcome completed ∧
      sourceHistory outcome.history=sourceHistory native.history++visibleSourceHistory events := by
  induction trace generalizing occurrence code source rank with
  | @done current result actual=>
    obtain ⟨completed,path,typed,matching,observed⟩:=source_tick_chosen_done memory floats allocator view select owner stop choices occurrence code _ source rank guard shape _ actual
    have storeEq:=guarded_done_store memory floats allocator select view code _ guard.native shape _ actual
    have effect : ReentrantCallbacks.Effect view code current.store code result.store:=by
      rw [storeEq]
      exact .refl guard.invariant
    cases result <;> exact ⟨code,completed,1,_,effect,path,typed,matching,sourceHistory_visible_append observed⟩
  | @next ticks current middle outcome actual tail ih=>
    obtain ⟨middleCode,middleSource,middleRank,count,events,effect,fresh,path,decrease,headObserved⟩:=source_tick_chosen_cont
      memory floats allocator correct allocation view laws select owner stop choices admissible numericChoice vectorChoice
        growthCompatible apiCompatible publicationCompatible occurrence code current source rank guard shape noOverflow ownerEq
        resources.initial available middle actual
    have nextShape:=tick_shape memory floats allocator select current .invocation shape (.cont middle) actual
    have nextSafe:=tick_no_overflow memory floats allocator correct allocation view laws select code current guard.invariant noOverflow (.cont middle) actual
    have nextOwner : owner=middle.store.id:=ownerEq.trans effect.metadata.identity.symm
    have sameLimits:=source_tick_limits memory floats allocator correct allocation view laws select code current source rank guard middle actual
    have nextResources : ChosenSourceResources (sourceModel view (sourcePublication allocator view) select owner stop)
        (sourceControlChoices choices) (occurrence+count) middle.store.limits middleSource := by
      simpa only [sameLimits] using resources.future path
    obtain ⟨afterCode,completed,more,observed,cumulative,rest,typed,matching,historyEq⟩:=
      ih (occurrence+count) middleCode middleSource middleRank fresh nextShape nextSafe nextOwner nextResources
    refine ⟨afterCode,completed,count+more,events++observed,effect.trans cumulative,path.trans rest,typed,matching,?_⟩
    rw [historyEq,headObserved,visibleSourceHistory_append,List.append_assoc]
end Exec.Theorems.OpenReentrantControl
