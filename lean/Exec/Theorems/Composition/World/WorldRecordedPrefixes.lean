import Exec.Theorems.Progress.EventfulWorldInfinite
import Exec.Theorems.Progress.RecordedInfinite
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
theorem WorldRecordedTransition.actual_recording {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {before after : EventfulWorld emission allowed M P view expected} {events : List HostEvent}
    (transition : WorldRecordedTransition memory hooks floats allocator before events after)
    (prior : List HostEvent) :
    recordedStep memory hooks floats allocator before.machine.exec before.machine.store before.machine.platform prior =
      .ok ((.Ok (),after.machine.exec,after.machine.store,after.machine.platform),prior++events) :=
  (recordedStep_returned ..).mpr ⟨transition.edge.actual,congrArg (prior++·) transition.recorded⟩

/-- The finite source trace and actual dispatch recording use exactly the same
concatenated labels, starting from any caller-supplied log prefix. -/
theorem world_recorded_history_exact {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {before after : EventfulWorld emission allowed M P view expected} {n : Nat} {events : List HostEvent}
    (history : Spec.Iterations (WorldRecordedTransition memory hooks floats allocator) n before events after)
    (prior : List HostEvent) :
    recordedSteps memory hooks floats allocator n before.machine.exec before.machine.store before.machine.platform prior =
      .ok ((.Ok (),after.machine.exec,after.machine.store,after.machine.platform),prior++events) ∧
    ∃ count,Spec.StepsHN count (Abs.decode before.machine.source) events (Abs.decode after.machine.source) := by
  constructor
  · induction history generalizing prior with
    | refl state => simp [recordedSteps]
    | cons edge tail ih =>
      simp only [recordedSteps,edge.actual_recording,bind_ok]
      simpa only [List.append_assoc,Std.uncurry] using ih (prior++_)
  · exact EventfulWorld.history_source (world_recorded_history history)

/-- One coherent stream of concrete dispatches records the same labels as its
source reductions. Every finite prefix uses the deterministic common recorder. -/
theorem world_loop_recorded_prefixes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : WorldStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view expected Inv)
    (initial : EventfulWorld emission allowed M P view expected) (valid : Inv initial.code initial.machine.store)
    (divergent : runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())=.div) :
    ∃ (states : Nat → EventfulWorld emission allowed M P view expected) (events : Nat → List HostEvent),
      states 0=initial ∧
      (∀n,Inv (states n).code (states n).machine.store ∧ WorldRecordedTransition memory hooks floats allocator (states n) (events n) (states (n+1))) ∧
      (∀n,runtime.interp.invoke_with_loop2 memory hooks floats allocator (states n).machine.exec (states n).machine.store (states n).machine.platform (.Ok ())=.div) ∧
      (∀n prior,recordedSteps memory hooks floats allocator n initial.machine.exec initial.machine.store initial.machine.platform prior=
        .ok ((.Ok (),(states n).machine.exec,(states n).machine.store,(states n).machine.platform),prior++recordedPrefixEvents events n)) ∧
      (∀n,∃count,Spec.StepsHN count (Abs.decode initial.machine.source) (recordedPrefixEvents events n) (Abs.decode (states n).machine.source)) := by
  classical
  let running (machine : EventfulWorld emission allowed M P view expected) :=
    Inv machine.code machine.machine.store ∧ runtime.interp.invoke_with_loop2 memory hooks floats allocator machine.machine.exec machine.machine.store machine.machine.platform (.Ok ())=.div
  have successor (current : {machine // running machine}) : ∃events,∃after : {machine // running machine},
      WorldRecordedTransition memory hooks floats allocator current.val events after.val := by
    obtain ⟨events,next,edge,valid,divergent⟩ := world_divergent_next memory hooks floats allocator Inv steps current.val current.property.1 current.property.2
    exact ⟨events,⟨next,valid,divergent⟩,edge⟩
  choose labels move edge using successor
  let states : Nat → {machine // running machine} := Nat.rec ⟨initial,valid,divergent⟩ (fun _ current=>move current)
  let events : Nat → List HostEvent := fun n=>labels (states n)
  have history (n : Nat) : Spec.Iterations (WorldRecordedTransition memory hooks floats allocator) n initial (recordedPrefixEvents events n) (states n).val := by
    induction n with
    | zero => exact .refl initial
    | succ n ih =>
      have tail := Spec.Iterations.cons (edge (states n)) (Spec.Iterations.refl (move (states n)).val)
      simpa only [List.append_nil,recordedPrefixEvents,events,states] using history_append ih tail
  refine ⟨(fun n=>(states n).val),events,rfl,?_,?_,?_,?_⟩
  · intro n
    exact ⟨(states n).property.1,edge (states n)⟩
  · intro n
    exact (states n).property.2
  · intro n prior
    exact (world_recorded_history_exact (history n) prior).1
  · intro n
    exact (world_recorded_history_exact (history n) []).2
end Exec.Theorems
