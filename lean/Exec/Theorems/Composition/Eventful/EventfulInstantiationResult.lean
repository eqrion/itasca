import Exec.Theorems.Composition.InstantiationResult
import Exec.Theorems.Composition.Eventful.EventfulErrors
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- Instantiation may run host events in its start function. Resource and
interrupt outcomes retain the actual reached store and source configuration. -/
def EventfulInstantiationExecution (initial : config) (events : List HostEvent)
    (store : _root_.store) (ambient : frame) : core.result.Result runtime.InstanceAddr runtime.ExecError → Prop
  | .Ok _ => StepsH initial events ⟨⟨store,ambient⟩,[]⟩
  | .Err (.Trap _) => StepsH initial events ⟨⟨store,ambient⟩,[.TRAP]⟩
  | .Err (.Exhausted _) | .Err .Terminated => ∃ frame body, StepsH initial events ⟨⟨store,frame⟩,body⟩
  | .Err _ => False

theorem InstantiationExecution.eventful {initial : config} {store : _root_.store} {ambient : frame}
    {result : core.result.Result runtime.InstanceAddr runtime.ExecError}
    (executed : InstantiationExecution initial store ambient result) :
    EventfulInstantiationExecution initial [] store ambient result := by
  cases result with
  | Ok address => exact executed
  | Err error => cases error <;> exact executed

theorem EventfulInvocationError.instantiation {initial : config} {events : List HostEvent}
    {store : _root_.store} {ambient : frame} {error : runtime.ExecError}
    (failed : EventfulInvocationError initial events store ambient error) :
    EventfulInstantiationExecution initial events store ambient (.Err error) := by
  cases error <;> simp only [EventfulInvocationError,EventfulInstantiationExecution] at failed ⊢
  · exact failed
  · exact ⟨ambient,failed⟩
  · exact ⟨ambient,failed⟩

theorem EventfulInstantiationExecution.prepend {initial middle : config} {first events : List HostEvent}
    {store : _root_.store} {ambient : frame} {result : core.result.Result runtime.InstanceAddr runtime.ExecError}
    (executed : EventfulInstantiationExecution middle events store ambient result)
    (steps : StepsH initial first middle) :
    EventfulInstantiationExecution initial (first++events) store ambient result := by
  cases result with
  | Ok address => exact Spec.stepsH_trans steps executed
  | Err error =>
    cases error <;> simp only [EventfulInstantiationExecution] at executed ⊢
    · exact Spec.stepsH_trans steps executed
    · obtain ⟨f,body,rest⟩ := executed; exact ⟨f,body,Spec.stepsH_trans steps rest⟩
    · obtain ⟨f,body,rest⟩ := executed; exact ⟨f,body,Spec.stepsH_trans steps rest⟩
end Exec.Theorems
