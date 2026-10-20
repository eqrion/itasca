import Exec.Theorems.Host.Open.Source.State.BoundaryNativePrefix
import Exec.Theorems.Host.Open.Driver.ActiveWasmSourceArrival
import Exec.Theorems.Host.Open.Driver.BoundaryArrivalTransport
import Exec.Spec.Open.WasmSegment
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- A terminating chosen source run from Wasm supplies a finite actual native
prefix and a strictly shorter matched reference suffix. The suffix retains its
own occurrence index, including across different trap-cleanup lengths. -/
theorem reference_wasm_prefix {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (admissible : choices.Admissible view (sourcePublication allocator view))
    (numericChoice : choices.wasm.numeric=Spec.firstNumericChoice) (vectorChoice : choices.wasm.vector=Spec.firstVectorChoice)
    (compatible : GrowthChoicesCompatible memory allocator view choices.wasm) (occurrence : Nat)
    (code : Store.CodeInterpretation) (native : State M) (source : Spec.OpenExecution.State SourceControl) (rank : Nat)
    (guard : SourceStateGuard memory allocator view code native source rank)
    (f : frame) (body : List admininstr) (expected : resulttype) (sourceMode : source.mode=.wasm f body expected)
    (ownerEq : owner=native.store.id)
    (resources : ChosenSourceResources (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence native.store.limits source)
    (available : Platform.AllocationAvailable allocator (2*Usize.max))
    {count events target}
    (reference : Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence count source events target)
    (completed : ∃result,target.mode=.completed result) :
    ∃nativeTicks reached afterCode afterSource afterRank consumed remaining beforeEvents moreEvents,
      ContinuingTrace (tick memory floats allocator select) nativeTicks native reached ∧
      ReentrantCallbacks.Effect view code native.store afterCode reached.store ∧
      SourceStateGuard memory allocator view afterCode reached afterSource afterRank ∧
      Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
        (sourceControlChoices choices) occurrence consumed source beforeEvents afterSource ∧
      Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
        (sourceControlChoices choices) (occurrence+consumed) remaining afterSource moreEvents target ∧
      count=consumed+remaining ∧ 0<consumed ∧ events=beforeEvents++moreEvents ∧
      sourceHistory reached.history=sourceHistory native.history++visibleSourceHistory beforeEvents ∧
      reached.store.limits=native.store.limits := by
  rcases native with ⟨store,mode,stack,history⟩
  rcases source with ⟨sourceStore,sourceModeRaw,sourceStack⟩
  rcases guard with ⟨held,related,stackGuard,storeEq⟩
  dsimp only at sourceMode storeEq
  have guard:=SourceStateGuard.mk held related stackGuard storeEq
  cases related with
  | host raw hostSource represented => cases sourceMode
  | draft status values owned => cases sourceMode
  | preparing exec address signature args results phase metadata ready => cases sourceMode
  | finishing exec error root results signature metadata => cases sourceMode
  | returned answer sameStore issued => cases sourceMode
  | wasm signature world root results metadata typed =>
    cases sourceMode
    let model:=sourceModel view (sourcePublication allocator view) select owner stop
    have permitted:=sourceControlChoices_admissible view (sourcePublication allocator view) select owner stop choices admissible
    have oldStore : sourceStore=(Abs.decode world.machine.source).1.1 := storeEq.trans world.machine.invariant.storeEq.symm
    have canonical:=Spec.OpenExecution.State.wasm_eq
      (Spec.OpenExecution.State.mk sourceStore (.wasm (Abs.decode world.machine.source).1.2 (Abs.decode world.machine.source).2
        (.mk_list (signature.results.val.map sourceType))) sourceStack)
      (Abs.decode world.machine.source) (.mk_list (signature.results.val.map sourceType)) oldStore rfl
    have referenceAt : Spec.OpenExecution.ChoiceTrace model (sourceControlChoices choices) occurrence count
        ⟨(Abs.decode world.machine.source).1.1,.wasm (Abs.decode world.machine.source).1.2 (Abs.decode world.machine.source).2
          (.mk_list (signature.results.val.map sourceType)),sourceStack⟩ events target := by
      rw [←canonical]
      exact reference
    have typedAt : (Spec.OpenExecution.State.mk (Abs.decode world.machine.source).1.1
        (.wasm (Abs.decode world.machine.source).1.2 (Abs.decode world.machine.source).2 (.mk_list (signature.results.val.map sourceType))) sourceStack).Typed := by
      rw [←canonical]
      exact guard.typed
    obtain ⟨sourceCount,referenceCfg,remaining,referenceEvents,referenceQuiet,referenceBoundary,referenceTail,totalCount,totalEvents⟩:=
      Spec.OpenExecution.ChoiceTrace.wasm_segment permitted (initial := Abs.decode world.machine.source) referenceAt typedAt completed
    obtain ⟨nativeTicks,boundaryNative,nativePath,nativeBoundary⟩:=source_boundary_native_prefix admissible.wasm numericChoice vectorChoice occurrence
      memory floats allocator correct allocation view laws compatible select world held referenceQuiet referenceBoundary root results stack history
    obtain ⟨actualTicks,reached,afterCode,afterSource,afterRank,quietCount,actualCfg,actualEvents,actualPath,effect,fresh,quiet,arrival,observed,limitsEq⟩:=
      active_wasm_source_arrival memory floats allocator correct allocation view laws select owner stop choices admissible.wasm numericChoice vectorChoice
        compatible nativePath occurrence world.code _ _ guard (Abs.decode world.machine.source).1.2 (Abs.decode world.machine.source).2
        (.mk_list (signature.results.val.map sourceType)) rfl ownerEq resources available nativeBoundary
    have cfgEq : Abs.decode world.machine.source=⟨⟨sourceStore,(Abs.decode world.machine.source).1.2⟩,(Abs.decode world.machine.source).2⟩ := by
      generalize same : Abs.decode world.machine.source=configuration at oldStore ⊢
      rcases configuration with ⟨⟨s,g⟩,body⟩
      dsimp only at oldStore
      rw [oldStore]
    have actualQuiet : Spec.ChosenStepsN choices.wasm occurrence quietCount (Abs.decode world.machine.source) [] actualCfg :=
      Eq.mp (congrArg (fun cfg=>Spec.ChosenStepsN choices.wasm occurrence quietCount cfg [] actualCfg) cfgEq.symm) quiet
    have boundaryEq:=Spec.OpenHost.quiet_boundary_unique admissible.wasm referenceQuiet referenceBoundary actualQuiet (arrival.boundary fresh.typed.1)
    cases boundaryEq
    cases referenceTail with
    | nil =>
      obtain ⟨result,impossible⟩:=completed
      cases impossible
    | @next position more first middle last headEvents tailEvents edge tail =>
      have referenceArrival:=boundary_transition_arrival view (sourcePublication allocator view) choices admissible.wasm
        (occurrence+sourceCount) referenceBoundary stop edge
      obtain ⟨eventsEq,represented⟩:=arrival.transport_guard referenceArrival rfl fresh
      have front : Spec.OpenExecution.ChoiceTrace model (sourceControlChoices choices) occurrence (sourceCount+1)
          ⟨sourceStore,.wasm (Abs.decode world.machine.source).1.2 (Abs.decode world.machine.source).2
            (.mk_list (signature.results.val.map sourceType)),sourceStack⟩
          (List.replicate sourceCount .wasm++headEvents) middle := by
        rw [canonical]
        have head:=Spec.OpenExecution.ChoiceTrace.wasmCounted model (sourceControlChoices choices) referenceQuiet
          (.mk_list (signature.results.val.map sourceType)) sourceStack
        simpa only [List.append_nil] using head.trans (Spec.OpenExecution.ChoiceTrace.next edge (.nil _ _))
      refine ⟨actualTicks,reached,afterCode,middle,afterRank,sourceCount+1,more,List.replicate sourceCount .wasm++headEvents,tailEvents,
        actualPath,effect,represented,front,?_,by omega,by omega,?_,?_,limitsEq⟩
      · simpa only [Nat.add_assoc] using tail
      · simpa only [List.append_assoc] using totalEvents
      · simpa only [eventsEq,visibleSourceHistory_append,visibleSourceHistory_wasm,List.nil_append] using observed
end Exec.Theorems.OpenReentrantControl
