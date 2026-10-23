import Exec.Theorems.Host.Open.Completeness.CompletedSourceWorld
import Exec.Theorems.Host.Open.Source.State.Observations
import Exec.Spec.Open.ExecutionTraces
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Classified native errors have an actual silent source prefix. Traps finish
through the source trap rule; resource/interrupt outcomes use the independently
selected stop policy. The native failure cause is retained by the caller. -/
theorem error_source_trace {H : Type} (model : Spec.OpenExecution.HostModel H)
    (before : config) (after : store) (ambient : frame) (error : runtime.ExecError)
    (values : alloc.vec.Vec runtime.Value) (expected : resulttype)
    (stack : List (Spec.OpenExecution.Continuation H))
    (prefixSteps : EventfulInvocationError before [] after ambient error)
    (allowed : ∀reason,sourceInvocationResult (.Err error) values=.stopped reason →
      ∀configuration,model.permitsStop reason configuration) :
    ∃count events,0<count ∧ Spec.OpenExecution.Trace model count
      ⟨before.1.1,.wasm before.1.2 before.2 expected,stack⟩ events
      ⟨after,.invokeReturn (sourceInvocationResult (.Err error) values),stack⟩ ∧ visibleSourceHistory events=[] := by
  have cutoff : ∀reason,sourceInvocationResult (.Err error) values=.stopped reason →
      ∀body,StepsH before [] ⟨⟨after,ambient⟩,body⟩ →
      ∃count events,0<count ∧ Spec.OpenExecution.Trace model count
        ⟨before.1.1,.wasm before.1.2 before.2 expected,stack⟩ events
        ⟨after,.invokeReturn (.stopped reason),stack⟩ ∧ visibleSourceHistory events=[] := by
    intro reason selected body path
    obtain ⟨count,trace⟩ := Spec.OpenExecution.Trace.wasmSteps model path expected stack
    refine ⟨count+1,List.replicate count .wasm,by omega,?_,visibleSourceHistory_wasm count⟩
    simpa only [List.append_nil] using trace.trans
      (Spec.OpenExecution.Trace.next (.cutoff (allowed reason selected _)) (.nil _))
  cases error with
  | Trap trap=>
    simp only [EventfulInvocationError] at prefixSteps
    obtain ⟨count,trace⟩ := Spec.OpenExecution.Trace.wasmSteps model prefixSteps expected stack
    refine ⟨count+1,List.replicate count .wasm,by omega,?_,visibleSourceHistory_wasm count⟩
    simpa only [sourceInvocationResult,List.append_nil] using trace.trans (Spec.OpenExecution.Trace.next (.trap) (.nil _))
  | Exhausted limit=>
    obtain ⟨body,path⟩ := prefixSteps
    cases limit <;> exact cutoff _ rfl body path
  | Terminated=>
    obtain ⟨body,path⟩ := prefixSteps
    exact cutoff .interrupt rfl body path
  | BadArguments | WrongStore | Internal | Link reason=>cases prefixSteps
end Exec.Theorems.OpenReentrantControl
