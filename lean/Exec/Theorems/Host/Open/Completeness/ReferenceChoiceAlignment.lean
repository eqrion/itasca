import Exec.Theorems.Host.Open.Driver.BoundaryArrivalTransport
import Exec.Theorems.Host.Open.Completeness.ControlChoiceDeterminism
import Exec.Spec.Open.WasmSegment
import Exec.Theorems.Host.Open.Source.Control.Publication
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- A selected quiet non-trap reduction is also the exact next combined step;
a terminal boundary or pending host entry cannot bypass it. -/
theorem quiet_nonactive_combined_head {H : Type} {model : Spec.OpenExecution.HostModel H}
    {choices : Spec.OpenExecution.Choices H} (allowed : choices.wasm.Admissible)
    {occurrence before after expected stack events next}
    (quiet : Spec.ChoiceStep choices.wasm occurrence before [] after)
    (typed : Store_ok before.1.1)
    (nonactive : Spec.activeTrap (Spec.trapCode before)=false)
    (step : Spec.OpenExecution.ChoiceTransition model choices occurrence
      ⟨before.1.1,.wasm before.1.2 before.2 expected,stack⟩ events next) :
    events=[.wasm] ∧ next=⟨after.1.1,.wasm after.1.2 after.2 expected,stack⟩ := by
  rcases before with ⟨⟨s,f⟩,body⟩
  cases step with
  | wasm other =>
    obtain ⟨_,same⟩:=Spec.choice_step_nonactive_deterministic allowed quiet other nonactive
    cases same
    exact ⟨rfl,rfl⟩
  | enter suspended same atStore expectedEq =>
    have forbidden:=suspended.pending.no_quiet_step (after := after) allowed occurrence (by rw [atStore];exact typed)
    exact False.elim (forbidden (by rw [same];exact quiet))
  | values => exact False.elim ((Spec.SourceTerminal.values _ _).no_step _ _ (quiet.erases allowed))
  | trap => exact False.elim ((Spec.SourceTerminal.trap _).no_step _ _ (quiet.erases allowed))

/-- Any actual arrival after a quiet Wasm segment matches a prefix of the
reference run. The reference's own occurrence count indexes the retained
suffix, even when trap cleanup lengths differ. -/
theorem reference_quiet_arrival {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (admissible : choices.Admissible view (sourcePublication allocator view))
    {occurrence count initial expected stack events target}
    (reference : Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence count ⟨initial.1.1,.wasm initial.1.2 initial.2 expected,stack⟩ events target)
    (typed : (Spec.OpenExecution.State.mk initial.1.1 (.wasm initial.1.2 initial.2 expected) stack).Typed)
    (completed : ∃result,target.mode=.completed result)
    {quietCount endpoint actualEvents actualSource code native rank}
    (quiet : Spec.ChosenStepsN choices.wasm occurrence quietCount initial [] endpoint)
    (arrival : WasmBoundaryArrival select owner expected stack endpoint actualEvents actualSource)
    (guard : SourceStateGuard memory allocator view code native actualSource rank) :
    ∃consumed remaining beforeEvents afterSource moreEvents,
      SourceStateGuard memory allocator view code native afterSource rank ∧
      Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
        (sourceControlChoices choices) occurrence consumed
        ⟨initial.1.1,.wasm initial.1.2 initial.2 expected,stack⟩ beforeEvents afterSource ∧
      Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
        (sourceControlChoices choices) (occurrence+consumed) remaining afterSource moreEvents target ∧
      count=consumed+remaining ∧ 0<consumed ∧ events=beforeEvents++moreEvents ∧
      visibleSourceHistory beforeEvents=visibleSourceHistory actualEvents := by
  let model:=sourceModel view (sourcePublication allocator view) select owner stop
  have permitted:=sourceControlChoices_admissible view (sourcePublication allocator view) select owner stop choices admissible
  obtain ⟨sourceCount,referenceCfg,remaining,referenceEvents,referenceQuiet,referenceBoundary,referenceTail,totalCount,totalEvents⟩:=
    Spec.OpenExecution.ChoiceTrace.wasm_segment permitted (initial := initial) reference typed completed
  have boundaryEq:=Spec.OpenHost.quiet_boundary_unique admissible.wasm referenceQuiet referenceBoundary quiet (arrival.boundary guard.typed.1)
  cases boundaryEq
  cases referenceTail with
  | nil => obtain ⟨result,impossible⟩:=completed;cases impossible
  | @next position more first middle last headEvents tailEvents edge tail =>
    have referenceArrival:=boundary_transition_arrival view (sourcePublication allocator view) choices admissible.wasm
      (occurrence+sourceCount) referenceBoundary stop edge
    obtain ⟨eventsEq,represented⟩:=arrival.transport_guard referenceArrival rfl guard
    have head:=Spec.OpenExecution.ChoiceTrace.wasmCounted model (sourceControlChoices choices) referenceQuiet expected stack
    have front:=head.trans (Spec.OpenExecution.ChoiceTrace.next edge (.nil _ _))
    refine ⟨sourceCount+1,more,List.replicate sourceCount .wasm++headEvents,middle,tailEvents,represented,?_,?_,by omega,by omega,?_,?_⟩
    · simpa only [List.append_nil] using front
    · simpa only [Nat.add_assoc] using tail
    · simpa only [List.append_assoc] using totalEvents
    · simp only [visibleSourceHistory_append,visibleSourceHistory_wasm,List.nil_append,eventsEq]
end Exec.Theorems.OpenReentrantControl
