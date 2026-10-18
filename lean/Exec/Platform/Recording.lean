import Exec.Generated.Types
import Exec.Spec.Events

namespace Exec.Platform.Recording
open Aeneas Aeneas.Std SpecExt

/-- Proof-only instrumentation records events at an interpreter call site,
after its result checker has determined the observable outcome. -/
def run {α : Type} (operation : Result α) (events : α → List HostEvent)
    (prior : List HostEvent) : Result (α × List HostEvent) := do
  let answer ← operation
  Result.ok (answer,prior ++ events answer)

/-- Erasing instrumentation preserves the exact computation, including
ordinary failure and divergence. -/
theorem erase {α : Type} (operation : Result α) (events : α → List HostEvent)
    (prior : List HostEvent) :
    (do let (answer,_) ← run operation events prior; Result.ok answer) = operation := by
  simp only [run,Std.bind_assoc,bind_ok,Std.uncurry,Std.bind_pure]

/-- Returning instrumented executions append precisely the site's event list. -/
theorem returned {α : Type} (operation : Result α) (events : α → List HostEvent)
    (prior : List HostEvent) (answer : α) (trace : List HostEvent) :
    run operation events prior = .ok (answer,trace) ↔
      operation = .ok answer ∧ trace = prior ++ events answer := by
  constructor
  · intro result
    have original := erase operation events prior
    rw [result,bind_ok] at original
    have exactRun : operation = .ok answer := original.symm
    refine ⟨exactRun,?_⟩
    simpa only [run,exactRun,bind_ok,Result.ok.injEq,Prod.mk.injEq,true_and] using result.symm
  · rintro ⟨operationEq,rfl⟩
    simp only [run,operationEq,bind_ok]

/-- Each invocation starts its own log; an atomic host callback's nested
invocations are not implicitly inserted into the caller's list. -/
theorem starts_empty {α : Type} (operation : Result α) (events : α → List HostEvent)
    (answer : α) (result : operation = .ok answer) :
    run operation events [] = .ok (answer,events answer) := by
  simp only [run,result,bind_ok,List.nil_append]
end Exec.Platform.Recording
