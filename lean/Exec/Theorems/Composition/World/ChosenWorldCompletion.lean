import Exec.Theorems.Composition.World.ChosenWorldLoopResult
import Exec.Theorems.Composition.World.ChosenWorldDivergence
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- A terminating run under the selected policy excludes native loop
divergence even when returning callbacks publish new interpreted code. -/
theorem chosen_world_loop_terminates {choices : SourceChoices} (admissible : choices.Admissible) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : ChosenWorldStepOutcomes (emission:=emission) (allowed:=allowed) choices memory hooks floats allocator view expected Inv)
    (initial : ChosenWorld emission allowed M P view expected) (valid : Inv initial.code initial.machine.store)
    {events : List HostEvent} {target : config}
    (run : ChoiceSteps choices initial.occurrence (Abs.decode initial.machine.source) events target) (terminal : SourceTerminal target) :
    runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())
      ⦃ result => ChosenWorldLoopResult choices Inv initial result ∧
        ∃ state,ChosenWorldLoopInvariant choices memory hooks floats allocator Inv initial state ∧
          ¬ActiveExecution state ∧ finishExecution state=result ⦄ := by
  have notdiv : runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())≠.div := by
    intro divergent
    exact chosen_terminating_no_infinite admissible run terminal
      (chosen_world_loop_infinite memory hooks floats allocator Inv steps initial valid divergent)
  have safe := chosen_world_loop_stops memory hooks floats allocator Inv steps initial valid
  generalize answerEq : runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ())=answer at safe notdiv ⊢
  cases safe with
  | ret post =>
    obtain ⟨state,held,stopped,rfl⟩ := post
    exact .ret ⟨chosen_world_loop_finished memory hooks floats allocator Inv initial state held stopped,state,held,stopped,rfl⟩
  | div => exact False.elim (notdiv rfl)
end Exec.Theorems
