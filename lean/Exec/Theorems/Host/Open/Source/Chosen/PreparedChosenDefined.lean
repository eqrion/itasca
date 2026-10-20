import Exec.Theorems.Host.Open.Completeness.ControlSegment
import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Theorems.Host.Open.Source.Control.Publication
import Exec.Theorems.Host.Open.Source.Chosen.ControlChoices
import Exec.Spec.Choices.FreeSyntax
import Exec.Spec.Steps
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- Accepted root preparation advances the independent selected source
request while preserving the exact saved caller stack and observations. -/
theorem source_prepared_chosen_defined {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (code : Store.CodeInterpretation)
    (choices : SourceOperationChoices) (occurrence : Nat)
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (guard : SourceStateGuard memory allocator view code native source 0)
    (address : runtime.FuncAddr) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value) (answer : Answer M Unit)
    (entry : Abs.AState)
    (metadata : RootMetadata native.store address signature)
    (arguments : ResultsTyped (Store.decodeStore view code native.store) (signature.params.val.map sourceType) (args.val.map sourceValue))
    (status : answer.1=.Ok ()) (sameStore : answer.2.2.1=native.store)
    (machine : StructuredMachine.Execution Executable.emission (Abs.SupportedState Abs.ExecutableInstr) view code native.store
      answer.2.1 entry (signature.results.val.map sourceType) 0 false)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds native.store) entry)
    (step : StepH ⟨⟨Store.decodeStore view code native.store,Spec.invocationFrame⟩,
      vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ [] (Abs.decode entry))
    (mode : native.mode=.preparing (.waiting (.done answer) address results))
    (sourceMode : source.mode=.invokeRequest address.index.val (args.val.map sourceValue)
      (signature.params.val.map sourceType) (signature.results.val.map sourceType)) :
    ∃next nextSource rank,tick memory floats allocator select native=.ok (.cont next) ∧
      SourceStateGuard memory allocator view code next nextSource rank ∧
      Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
        (sourceControlChoices choices) occurrence 2 source [.wasm] nextSource ∧
      next.history=native.history ∧
      ControlSegment (sourceModel view (sourcePublication allocator view) select owner stop)
        (sourceControlChoices choices) select owner occurrence source [.wasm] nextSource := by
  let model:=sourceModel view (sourcePublication allocator view) select owner stop
  have canonical : source=⟨Store.decodeStore view code native.store,
      .invokeRequest address.index.val (args.val.map sourceValue) (signature.params.val.map sourceType) (signature.results.val.map sourceType),source.stack⟩ := by
    rcases source with ⟨s,m,stack⟩
    dsimp only at sourceMode
    subst m
    have same : s=Store.decodeStore view code native.store:=guard.storeEq
    subst s
    rfl
  have inputTyped:=guard.typed.2.1
  rw [canonical] at inputTyped
  obtain ⟨bound,typeEq⟩:=inputTyped
  have entryTyped:=Spec.stepH_config_preserved step
    (Spec.invocation_config_ok guard.invariant.source_typed _ _ _ _ bound typeEq arguments)
  let world : EventfulWorld Executable.emission Abs.ExecutableInstr M Unit view (signature.results.val.map sourceType):=
    ⟨code,⟨native.store,answer.2.1,(),entry,0,false,machine,guard.invariant.toCertifiedApiStore.toCertifiedSupportedStore,owned⟩⟩
  let next : State M:={native with mode:=.wasm answer.2.1 (.Ok ()) address results}
  let nextSource : Spec.OpenExecution.State SourceControl:=⟨Store.decodeStore view code native.store,
    .wasm (Abs.decode entry).1.2 (Abs.decode entry).2 (.mk_list (signature.results.val.map sourceType)),source.stack⟩
  have entryStore : (Abs.decode entry).1.1=Store.decodeStore view code native.store:=by
    simpa only [Abs.decode] using machine.storeEq
  refine ⟨next,nextSource,_,?_,⟨guard.invariant,.wasm signature world address results metadata entryTyped,guard.stack,rfl⟩,?_,rfl,?_⟩
  · simp only [tick,mode,acceptCall,status,sameStore,next]
  · rw [canonical]
    have trace : Spec.OpenExecution.ChoiceTrace model (sourceControlChoices choices) occurrence 2
        ⟨Store.decodeStore view code native.store,.invokeRequest address.index.val (args.val.map sourceValue)
          (signature.params.val.map sourceType) (signature.results.val.map sourceType),source.stack⟩ [.wasm]
        ⟨(Abs.decode entry).1.1,.wasm (Abs.decode entry).1.2 (Abs.decode entry).2
          (.mk_list (signature.results.val.map sourceType)),source.stack⟩ :=
      .next (.acceptInvoke arguments) (.next (.wasm (.ordinary (Spec.stepH_nil_to_step step) (by
          intro instruction member
          rcases List.mem_append.mp member with front | last
          · obtain ⟨value,member,rfl⟩:=List.mem_map.mp front
            exact .atom _ (Spec.ordinaryChoiceTag_value value)
          · simp only [List.mem_singleton] at last
            subst instruction
            exact .atom _ rfl))) (.nil _ _))
    simpa only [entryStore,nextSource] using trace
  · rw [canonical]
    have chosenStep : Spec.ChoiceStep choices.wasm (occurrence+1)
        ⟨⟨Store.decodeStore view code native.store,Spec.invocationFrame⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ [] (Abs.decode entry) :=
      .ordinary (Spec.stepH_nil_to_step step) (by
        intro instruction member
        rcases List.mem_append.mp member with front | last
        · obtain ⟨value,member,rfl⟩:=List.mem_map.mp front
          exact .atom _ (Spec.ordinaryChoiceTag_value value)
        · simp only [List.mem_singleton] at last
          subst instruction
          exact .atom _ rfl)
    have segment : ControlSegment model (sourceControlChoices choices) select owner occurrence
        ⟨Store.decodeStore view code native.store,.invokeRequest address.index.val (args.val.map sourceValue)
          (signature.params.val.map sourceType) (signature.results.val.map sourceType),source.stack⟩ [.wasm]
        ⟨(Abs.decode entry).1.1,.wasm (Abs.decode entry).1.2 (Abs.decode entry).2
          (.mk_list (signature.results.val.map sourceType)),source.stack⟩ := by
      simpa only [List.nil_append] using ControlSegment.next (select := select) (owner := owner)
        (by intros; simp) (Spec.OpenExecution.ChoiceTransition.acceptInvoke arguments)
        (ControlSegment.quiet (choices := sourceControlChoices choices) chosenStep (by simp only [Spec.trapCode,Spec.activeTrap_vals,Spec.activeTrap]))
    simpa only [entryStore,nextSource] using segment

end Exec.Theorems.OpenReentrantControl
