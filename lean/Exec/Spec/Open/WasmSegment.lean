import Exec.Spec.Open.QuietBoundary
import Exec.Spec.Open.ExecutionChosenCounted
namespace Exec.Spec.OpenExecution
open SpecExt

/-- A terminating combined run splits at the next Wasm return, trap or host
request. The exact remaining source trace and its choice index are retained. -/
def WasmSegment {H : Type} (model : HostModel H) (choices : Choices H) (occurrence total : Nat)
    (initial : config) (expected : resulttype) (stack : List (Continuation H))
    (events : List Observation) (last : State H) : Prop :=
  ∃count endpoint remaining tailEvents,
    ChosenStepsN choices.wasm occurrence count initial [] endpoint ∧
    OpenHost.QuietBoundary endpoint ∧
    ChoiceTrace model choices (occurrence+count) remaining
      ⟨endpoint.1.1,.wasm endpoint.1.2 endpoint.2 expected,stack⟩ tailEvents last ∧
    total=count+remaining ∧ events=List.replicate count .wasm++tailEvents

theorem WasmSegment.zero {H : Type} {model : HostModel H} {choices : Choices H} {occurrence total initial expected stack events last}
    (trace : ChoiceTrace model choices occurrence total
      ⟨initial.1.1,.wasm initial.1.2 initial.2 expected,stack⟩ events last)
    (wf : wf_config initial) (boundary : OpenHost.QuietBoundary initial) :
    WasmSegment model choices occurrence total initial expected stack events last := by
  exact ⟨0,initial,total,events,.refl occurrence wf,boundary,trace,by omega,rfl⟩

theorem WasmSegment.prepend {H : Type} {model : HostModel H} {choices : Choices H}
    {occurrence total before middle expected stack events last}
    (head : ChoiceStep choices.wasm occurrence before [] middle)
    (tail : WasmSegment model choices (occurrence+1) total middle expected stack events last) :
    WasmSegment model choices occurrence (total+1) before expected stack (.wasm::events) last := by
  obtain ⟨count,endpoint,remaining,tailEvents,prefixSteps,boundary,rest,length,observed⟩:=tail
  refine ⟨count+1,endpoint,remaining,tailEvents,?_,boundary,?_,by omega,?_⟩
  · simpa only [List.nil_append] using ChosenStepsN.cons head prefixSteps
  · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest
  · simp only [observed,List.replicate_succ,List.cons_append]

theorem ChoiceTrace.wasm_segment {H : Type} {model : HostModel H} {choices : Choices H}
    (allowed : choices.Admissible model) {occurrence total initial expected stack events last}
    (trace : ChoiceTrace model choices occurrence total
      ⟨initial.1.1,.wasm initial.1.2 initial.2 expected,stack⟩ events last)
    (held : (State.mk initial.1.1 (.wasm initial.1.2 initial.2 expected) stack).Typed)
    (completed : ∃result,last.mode=.completed result) :
    WasmSegment model choices occurrence total initial expected stack events last := by
  induction total generalizing occurrence initial expected stack events last with
  | zero =>
    cases trace
    obtain ⟨result,impossible⟩:=completed
    cases impossible
  | succ total ih =>
    rcases initial with ⟨⟨s,f⟩,body⟩
    cases trace with
    | next step tail =>
      have fresh := ((step.erases allowed).preserves held).1
      have whole := ChoiceTrace.next step tail
      have wf : wf_config ⟨⟨s,f⟩,body⟩ := by
        have typed : Config_ok ⟨⟨s,f⟩,body⟩ expected := held.2.1
        cases typed
        assumption
      cases step with
      | wasm reduction => exact (ih tail fresh completed).prepend reduction
      | enter suspended same atStore expectedEq =>
        apply WasmSegment.zero whole wf
        rw [←same]
        exact .host suspended.pending (by rw [atStore];exact held.1)
      | values => exact WasmSegment.zero whole wf (.terminal (.values _ _))
      | trap => exact WasmSegment.zero whole wf (.terminal (.trap _))
end Exec.Spec.OpenExecution
