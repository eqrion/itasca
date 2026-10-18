import Exec.Theorems.Composition.Recorded.RecordedLoop
import Exec.Theorems.Composition.Eventful.EventfulLoop
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

def recordedPrefixEvents (events : Nat → List HostEvent) : Nat → List HostEvent
  | 0 => []
  | n+1 => recordedPrefixEvents events n ++ events n

/-- The actual divergent loop has a next recorded successful dispatch. The
auxiliary API invariant is retained at the selected successor. -/
theorem recorded_inv_divergent_next {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (Inv : runtime.store.Store M → Prop)
    (steps : RecordedInvStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected Inv)
    (machine : EventfulMachine emission allowed M P view code expected) (valid : Inv machine.store)
    (divergent : runtime.interp.invoke_with_loop2 memory hooks floats allocator machine.exec machine.store machine.platform (.Ok ())=.div) :
    ∃events next, RecordedEventfulTransition memory hooks floats allocator machine events next ∧ Inv next.store ∧
      runtime.interp.invoke_with_loop2 memory hooks floats allocator next.exec next.store next.platform (.Ok ())=.div := by
  have active := execution_loop_divergent_active memory hooks floats allocator machine.exec machine.store machine.platform divergent
  obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,returned,fresh,outcome,rest⟩ := WP.spec_imp_exists (steps machine valid active)
  change loop (executionBody memory hooks floats allocator) (machine.exec,machine.store,machine.platform,.Ok ())=.div at divergent
  rw [loop.eq_def,executionBody_active memory hooks floats allocator _ ⟨active,rfl⟩,returned] at divergent
  simp [bind_ok] at divergent
  cases status with
  | Err error => rw [execution_loop_error memory hooks floats allocator] at divergent;simp at divergent
  | Ok value =>
    cases value
    obtain ⟨events,next,equal,edge⟩ := outcome rfl
    have components : nextExec=next.exec ∧ nextStore=next.store ∧ nextPlatform=next.platform := by
      simpa only [Prod.mk.injEq,true_and] using equal
    refine ⟨events,next,edge,?_,?_⟩
    · simpa only [components.2.1] using fresh
    · change loop (executionBody memory hooks floats allocator) (next.exec,next.store,next.platform,.Ok ())=.div
      simpa only [components.1,components.2.1,components.2.2] using divergent

/-- One coherent stream of concrete dispatches records the same labels as its
source reductions. Every finite prefix uses the deterministic common recorder. -/
theorem recorded_inv_loop_prefixes {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (Inv : runtime.store.Store M → Prop)
    (steps : RecordedInvStepOutcomes (emission:=emission) (allowed:=allowed) memory hooks floats allocator view code expected Inv)
    (initial : EventfulMachine emission allowed M P view code expected) (valid : Inv initial.store)
    (divergent : runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())=.div) :
    ∃ (states : Nat → EventfulMachine emission allowed M P view code expected) (events : Nat → List HostEvent),
      states 0=initial ∧
      (∀n,Inv (states n).store ∧ RecordedEventfulTransition memory hooks floats allocator (states n) (events n) (states (n+1))) ∧
      (∀n,runtime.interp.invoke_with_loop2 memory hooks floats allocator (states n).exec (states n).store (states n).platform (.Ok ())=.div) ∧
      (∀n prior,recordedSteps memory hooks floats allocator n initial.exec initial.store initial.platform prior=
        .ok ((.Ok (),(states n).exec,(states n).store,(states n).platform),prior++recordedPrefixEvents events n)) ∧
      (∀n,∃count,Spec.StepsHN count (Abs.decode initial.source) (recordedPrefixEvents events n) (Abs.decode (states n).source)) := by
  classical
  let running (machine : EventfulMachine emission allowed M P view code expected) :=
    Inv machine.store ∧ runtime.interp.invoke_with_loop2 memory hooks floats allocator machine.exec machine.store machine.platform (.Ok ())=.div
  have successor (current : {machine // running machine}) : ∃events,∃after : {machine // running machine},
      RecordedEventfulTransition memory hooks floats allocator current.val events after.val := by
    obtain ⟨events,next,edge,valid,divergent⟩ := recorded_inv_divergent_next memory hooks floats allocator Inv steps current.val current.property.1 current.property.2
    exact ⟨events,⟨next,valid,divergent⟩,edge⟩
  choose labels move edge using successor
  let states : Nat → {machine // running machine} := Nat.rec ⟨initial,valid,divergent⟩ (fun _ current=>move current)
  let events : Nat → List HostEvent := fun n=>labels (states n)
  have history (n : Nat) : Spec.Iterations (RecordedEventfulTransition memory hooks floats allocator) n initial (recordedPrefixEvents events n) (states n).val := by
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
    exact (recorded_history_exact (history n) prior).1
  · intro n
    exact (recorded_history_exact (history n) []).2
end Exec.Theorems
