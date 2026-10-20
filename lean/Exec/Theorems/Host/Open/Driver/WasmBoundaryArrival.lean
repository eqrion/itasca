import Exec.Theorems.Host.Open.Source.Chosen.ControlChoices
import Exec.Spec.Open.QuietBoundary
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- A complete open Wasm segment includes its final values, trap or host-entry
transition. Its captured continuation and expanded boundary event are exact. -/
inductive WasmBoundaryArrival (select : Selector) (owner : Usize) (expected : resulttype)
    (stack : List (Spec.OpenExecution.Continuation SourceControl)) :
    config → List Spec.OpenExecution.Observation → Spec.OpenExecution.State SourceControl → Prop
  | values (s : store) (f : frame) (values : List val) :
      WasmBoundaryArrival select owner expected stack ⟨⟨s,f⟩,vals values⟩ [] ⟨s,.invokeReturn (.returned values),stack⟩
  | trap (s : store) (f : frame) :
      WasmBoundaryArrival select owner expected stack ⟨⟨s,f⟩,[.TRAP]⟩ [] ⟨s,.invokeReturn .trapped,stack⟩
  | host (suspended : Spec.OpenExecution.Suspension) (expectedEq : suspended.expected=expected) :
      WasmBoundaryArrival select owner expected stack suspended.pending.initial
        [.hostEnter suspended.pending.address suspended.pending.identity suspended.pending.arguments]
        ⟨suspended.pending.before,.host (.active (sourceHostEntry select owner suspended.pending.identity suspended.pending.arguments)),
          .wasm suspended::stack⟩

theorem WasmBoundaryArrival.boundary {select owner expected stack configuration events after}
    (arrival : WasmBoundaryArrival select owner expected stack configuration events after)
    (typed : Store_ok after.store) : Spec.OpenHost.QuietBoundary configuration := by
  cases arrival with
  | values s f values => exact .terminal (.values _ _)
  | trap s f => exact .terminal (.trap _)
  | host suspended expectedEq => exact .host suspended.pending typed

theorem WasmBoundaryArrival.store {select owner expected stack configuration events after}
    (arrival : WasmBoundaryArrival select owner expected stack configuration events after) :
    configuration.1.1=after.store := by
  cases arrival with
  | values | trap => rfl
  | host suspended expectedEq => exact Spec.OpenExecution.pending_store suspended.pending

theorem WasmBoundaryArrival.transition {M : Type} (view : M → Slice U8) (publication : SourcePublication)
    {select owner expected stack configuration events after}
    (arrival : WasmBoundaryArrival select owner expected stack configuration events after)
    (stop : Spec.OpenExecution.StopReason → config → Prop) (choices : SourceOperationChoices) (occurrence : Nat) :
    Spec.OpenExecution.ChoiceTransition (sourceModel view publication select owner stop) (sourceControlChoices choices) occurrence
      ⟨configuration.1.1,.wasm configuration.1.2 configuration.2 expected,stack⟩ events after := by
  cases arrival with
  | values => exact .values
  | trap => exact .trap
  | host suspended expectedEq =>
    have step : Spec.OpenExecution.ChoiceTransition (sourceModel view publication select owner stop) (sourceControlChoices choices) occurrence
        ⟨suspended.pending.initial.1.1,.wasm suspended.pending.initial.1.2 suspended.pending.initial.2 expected,stack⟩
        [.hostEnter suspended.pending.address suspended.pending.identity suspended.pending.arguments]
        ⟨suspended.pending.initial.1.1,.host ((sourceModel view publication select owner stop).enter suspended.pending.identity suspended.pending.arguments),
          .wasm suspended::stack⟩ :=
      .enter suspended rfl (Spec.OpenExecution.pending_store suspended.pending).symm expectedEq
    simpa only [Spec.OpenExecution.pending_store,sourceModel] using step
theorem WasmBoundaryArrival.not_wasm {select owner expected stack configuration events after}
    (arrival : WasmBoundaryArrival select owner expected stack configuration events after)
    (f : frame) (body : List admininstr) (results : resulttype) : after.mode≠.wasm f body results := by
  cases arrival <;> intro impossible <;> cases impossible
end Exec.Theorems.OpenReentrantControl
