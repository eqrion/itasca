import Exec.Theorems.Host.Open.Completeness.ReferenceChoiceAlignment
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- The source transitions grouped by one native control tick. Deterministic
control can precede one ordinary Wasm entry step or a whole quiet segment.
A pending host arrival can only occur at the end of the tick. -/
inductive ControlSegment (model : Spec.OpenExecution.HostModel SourceControl)
    (choices : Spec.OpenExecution.Choices SourceControl) (select : Selector) (owner : Usize) :
    Nat → Spec.OpenExecution.State SourceControl → List Spec.OpenExecution.Observation →
      Spec.OpenExecution.State SourceControl → Prop
  | single {occurrence first events last}
      (outside : ∀f body expected,first.mode≠.wasm f body expected)
      (step : Spec.OpenExecution.ChoiceTransition model choices occurrence first events last) :
      ControlSegment model choices select owner occurrence first events last
  | next {occurrence first middle last events more}
      (outside : ∀f body expected,first.mode≠.wasm f body expected)
      (step : Spec.OpenExecution.ChoiceTransition model choices occurrence first events middle)
      (tail : ControlSegment model choices select owner (occurrence+1) middle more last) :
      ControlSegment model choices select owner occurrence first (events++more) last
  | quiet {occurrence initial after expected stack}
      (step : Spec.ChoiceStep choices.wasm occurrence initial [] after)
      (nonactive : Spec.activeTrap (Spec.trapCode initial)=false) :
      ControlSegment model choices select owner occurrence
        ⟨initial.1.1,.wasm initial.1.2 initial.2 expected,stack⟩ [.wasm]
        ⟨after.1.1,.wasm after.1.2 after.2 expected,stack⟩
  | boundary {occurrence initial quietCount endpoint expected stack events last}
      (quiet : Spec.ChosenStepsN choices.wasm occurrence quietCount initial [] endpoint)
      (arrival : WasmBoundaryArrival select owner expected stack endpoint events last) :
      ControlSegment model choices select owner occurrence
        ⟨initial.1.1,.wasm initial.1.2 initial.2 expected,stack⟩
        (List.replicate quietCount .wasm++events) last

/-- Expanding control grouping yields a positive chosen source trace. -/
theorem ControlSegment.trace {M : Type} (view : M → Slice U8) (publication : SourcePublication)
    (select : Selector) (owner : Usize) (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) {occurrence first events last}
    (segment : ControlSegment (sourceModel view publication select owner stop) (sourceControlChoices choices)
      select owner occurrence first events last) :
    ∃count,0<count ∧ Spec.OpenExecution.ChoiceTrace (sourceModel view publication select owner stop)
      (sourceControlChoices choices) occurrence count first events last := by
  induction segment with
  | single outside step =>
    exact ⟨1,by omega,by simpa only [List.append_nil] using Spec.OpenExecution.ChoiceTrace.next step (.nil _ _)⟩
  | next outside step tail ih =>
    obtain ⟨count,positive,trace⟩:=ih
    exact ⟨count+1,by omega,.next step trace⟩
  | quiet step nonactive =>
    exact ⟨1,by omega,by simpa only [List.append_nil] using Spec.OpenExecution.ChoiceTrace.next (.wasm step) (.nil _ _)⟩
  | @boundary occurrence initial quietCount endpoint expected stack events last quiet arrival =>
    have front:=Spec.OpenExecution.ChoiceTrace.wasmCounted (sourceModel view publication select owner stop)
      (sourceControlChoices choices) quiet expected stack
    have step:=arrival.transition view publication stop choices (occurrence+quietCount)
    exact ⟨quietCount+1,by omega,by simpa only [List.append_nil] using front.trans (Spec.OpenExecution.ChoiceTrace.next step (.nil _ _))⟩

/-- One native control tick with all committed effects and its selected source
grouping. The grouping supports comparison with an independent reference run. -/
def SourceControlAdvance {M A : Type} (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (choices : SourceOperationChoices)
    (occurrence : Nat) (code : Store.CodeInterpretation)
    (native : State M) (source : Spec.OpenExecution.State SourceControl) (next : State M) : Prop :=
  ∃afterCode nextSource afterRank events,
    ReentrantCallbacks.Effect view code native.store afterCode next.store ∧
    SourceStateGuard memory allocator view afterCode next nextSource afterRank ∧
    ControlSegment (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) select owner occurrence source events nextSource ∧
    sourceHistory next.history=sourceHistory native.history++visibleSourceHistory events

private theorem transition_not_completed {H : Type} {model : Spec.OpenExecution.HostModel H}
    {choices : Spec.OpenExecution.Choices H} {occurrence first events last}
    (step : Spec.OpenExecution.ChoiceTransition model choices occurrence first events last) :
    ¬∃result,first.mode=.completed result := by
  intro ⟨result,same⟩
  cases step <;> cases same

/-- Control grouping preserves the exact reference suffix and its occurrence
index. Native saved callers are retargeted only at the final host boundary. -/
theorem ControlSegment.match_reference {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (view : M → Slice U8) (select : Selector) (owner : Usize)
    (stop : Spec.OpenExecution.StopReason → config → Prop)
    (choices : SourceOperationChoices) (admissible : choices.Admissible view (sourcePublication allocator view))
    {occurrence first actualEvents actualSource}
    (segment : ControlSegment (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) select owner occurrence first actualEvents actualSource)
    {count events target}
    (reference : Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
      (sourceControlChoices choices) occurrence count first events target)
    (typed : first.Typed) (completed : ∃result,target.mode=.completed result)
    {code native rank} (guard : SourceStateGuard memory allocator view code native actualSource rank) :
    ∃consumed remaining beforeEvents afterSource moreEvents,
      SourceStateGuard memory allocator view code native afterSource rank ∧
      Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
        (sourceControlChoices choices) occurrence consumed first beforeEvents afterSource ∧
      Spec.OpenExecution.ChoiceTrace (sourceModel view (sourcePublication allocator view) select owner stop)
        (sourceControlChoices choices) (occurrence+consumed) remaining afterSource moreEvents target ∧
      count=consumed+remaining ∧ 0<consumed ∧ events=beforeEvents++moreEvents ∧
      visibleSourceHistory beforeEvents=visibleSourceHistory actualEvents := by
  have permitted:=sourceControlChoices_admissible view (sourcePublication allocator view) select owner stop choices admissible
  induction segment generalizing count events target with
  | single outside step =>
    cases reference with
    | nil => exact False.elim (transition_not_completed step completed)
    | @next position more first middle last headEvents tailEvents edge tail =>
      obtain ⟨eventsEq,stateEq⟩:=control_choice_deterministic view (sourcePublication allocator view) select owner stop choices step edge outside
      cases stateEq
      cases eventsEq
      refine ⟨1,more,_,_,tailEvents,guard,?_,tail,by omega,by omega,rfl,rfl⟩
      simpa only [List.append_nil] using Spec.OpenExecution.ChoiceTrace.next step (.nil _ _)
  | @next occurrence first middle last actualHead actualTail outside step rest ih =>
    cases reference with
    | nil => exact False.elim (transition_not_completed step completed)
    | @next position more first middle last headEvents tailEvents edge tail =>
      obtain ⟨eventsEq,stateEq⟩:=control_choice_deterministic view (sourcePublication allocator view) select owner stop choices step edge outside
      cases stateEq
      cases eventsEq
      obtain ⟨consumed,remaining,beforeEvents,afterSource,moreEvents,fresh,front,back,total,positive,observed,visible⟩:=
        ih tail ((step.erases permitted).preserves typed).1 completed guard
      refine ⟨consumed+1,remaining,actualHead++beforeEvents,afterSource,moreEvents,fresh,
        .next step front,?_,by omega,by omega,?_,?_⟩
      · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using back
      · simp only [observed,List.append_assoc]
      · simp only [visibleSourceHistory_append,visible]
  | quiet step nonactive =>
    cases reference with
    | nil => obtain ⟨result,same⟩:=completed;cases same
    | @next position more first middle last headEvents tailEvents edge tail =>
      obtain ⟨eventsEq,stateEq⟩:=quiet_nonactive_combined_head admissible.wasm step typed.1 nonactive edge
      cases stateEq
      cases eventsEq
      refine ⟨1,more,[.wasm],_,tailEvents,guard,?_,tail,by omega,by omega,rfl,rfl⟩
      simpa only [List.append_nil] using Spec.OpenExecution.ChoiceTrace.next edge (.nil _ _)
  | boundary quiet arrival =>
    obtain ⟨consumed,remaining,beforeEvents,afterSource,moreEvents,fresh,front,back,total,positive,observed,visible⟩:=
      reference_quiet_arrival memory allocator view select owner stop choices admissible reference typed completed quiet arrival guard
    refine ⟨consumed,remaining,beforeEvents,afterSource,moreEvents,fresh,front,back,total,positive,observed,?_⟩
    simpa only [visibleSourceHistory_append,visibleSourceHistory_wasm,List.nil_append] using visible
end Exec.Theorems.OpenReentrantControl
