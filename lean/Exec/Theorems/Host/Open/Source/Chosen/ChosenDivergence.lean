import Exec.Theorems.Host.Open.Source.Chosen.TickChosenCont
import Exec.Theorems.Host.Open.Source.State.TickLimits
import Exec.Theorems.Host.Open.Completeness.ChosenSourceResources
import Exec.Spec.Open.ChosenProgress
import Exec.Theorems.Host.Open.Driver.DriverPrefixes
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Divergence of the actual guarded driver yields productive combined source
execution under the same selected policy and one occurrence ledger. Capacity
requirements refer to independent source prefixes and initial native limits. -/
theorem run_chosen_source_infinite {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (admissible : choices.wasm.Admissible)
    (numericChoice : choices.wasm.numeric=Spec.firstNumericChoice)
    (vectorChoice : choices.wasm.vector=Spec.firstVectorChoice)
    (growthCompatible : GrowthChoicesCompatible memory allocator view choices.wasm)
    (apiCompatible : SourceAPIChoicesCompatible memory allocator view choices)
    (publicationCompatible : SourcePublicationChoicesCompatible memory floats allocator view choices) (occurrence : Nat)
    (code : Store.CodeInterpretation) (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (shape : native.Shape .invocation) (noOverflow : NoOverflowMode native.mode)
    (ownerEq : owner=native.store.id)
    (resources : ChosenSourceResources (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence native.store.limits source)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    (divergent : run memory floats allocator select native=.div) :
    Spec.OpenExecution.ChoiceInfinite (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence source := by
  classical
  let Point:={p : State M × Store.CodeInterpretation × Spec.OpenExecution.State SourceControl × Nat × Nat //
    SourceStateGuard memory allocator view p.2.1 p.1 p.2.2.1 p.2.2.2.1 ∧
    p.1.Shape .invocation ∧ NoOverflowMode p.1.mode ∧ owner=p.1.store.id ∧
    run memory floats allocator select p.1=.div ∧
    ChosenSourceResources (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) p.2.2.2.2 p.1.store.limits p.2.2.1}
  let sourceOf (point : Point):=point.val.2.2.1
  let rankOf (point : Point):=point.val.2.2.2.1
  let occurrenceOf (point : Point):=point.val.2.2.2.2
  let model:=sourceModel view (sourcePublication allocator view) select owner stop
  have advance : ∀point : Point,∃next count events,
      Spec.OpenExecution.ChoiceTrace model (sourceControlChoices choices) (occurrenceOf point) count (sourceOf point) events (sourceOf next) ∧
      occurrenceOf next=occurrenceOf point+count ∧ (count=0 → rankOf next<rankOf point) := by
    rintro ⟨⟨current,currentCode,currentSource,currentRank,currentOccurrence⟩,held,shaped,safe,owned,diverges,currentResources⟩
    obtain ⟨states,initial,steps⟩:=run_divergent_stream memory floats allocator correct allocation view laws select currentCode current held.native diverges
    have firstStep:=(steps 0).2.1
    rw [initial] at firstStep
    have nextDiverges:=(steps 1).2.2.1
    obtain ⟨afterCode,nextSource,afterRank,count,events,effect,fresh,path,decrease,observed⟩:=
      source_tick_chosen_cont memory floats allocator correct allocation view laws select owner stop choices admissible numericChoice vectorChoice
        growthCompatible apiCompatible publicationCompatible currentOccurrence currentCode current currentSource currentRank
        held shaped safe owned currentResources.initial available (states 1) firstStep
    have nextShape:=tick_shape memory floats allocator select current .invocation shaped (.cont (states 1)) firstStep
    have nextSafe:=tick_no_overflow memory floats allocator correct allocation view laws select currentCode current held.invariant safe (.cont (states 1)) firstStep
    have nextOwner : owner=(states 1).store.id:=owned.trans effect.metadata.identity.symm
    have sameLimits:=source_tick_limits memory floats allocator correct allocation view laws select currentCode current currentSource currentRank held (states 1) firstStep
    have nextResources : ChosenSourceResources model (sourceControlChoices choices) (currentOccurrence+count) (states 1).store.limits nextSource := by
      simpa only [sameLimits] using currentResources.future path
    let next : Point:=⟨⟨states 1,afterCode,nextSource,afterRank,currentOccurrence+count⟩,fresh,nextShape,nextSafe,nextOwner,nextDiverges,nextResources⟩
    exact ⟨next,count,events,path,rfl,decrease⟩
  let initial : Point:=⟨⟨native,code,source,rank,occurrence⟩,guard,shape,noOverflow,ownerEq,divergent,resources⟩
  exact Spec.OpenExecution.chosen_infinite_of_decreasing_stutter model (sourceControlChoices choices) sourceOf occurrenceOf rankOf advance initial
end Exec.Theorems.OpenReentrantControl
