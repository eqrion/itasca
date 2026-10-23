import Exec.Theorems.Composition.Supported.ChosenMachineLoop
import Exec.Theorems.Composition.Supported.ChosenMachineDivergence
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Termination of one selected source run excludes divergence of the actual
host-free native loop. Resource errors remain possible ordinary results. -/
theorem chosen_supported_loop_terminates {choices : SourceChoices} (admissible : choices.Admissible) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (steps : ChosenSupportedStepOutcomes (emission:=emission) (allowed:=allowed) choices memory hooks floats allocator view code expected)
    (initial : ChosenSupportedMachine emission allowed M P view code expected)
    {events : List HostEvent} {target : config}
    (run : ChoiceSteps choices initial.occurrence (Abs.decode initial.source) events target)
    (terminal : SourceTerminal target) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ result => ∃ state, ChosenSupportedLoopInvariant (choices:=choices) memory hooks floats allocator initial state ∧
        ¬ActiveExecution state ∧ finishExecution state=result ⦄ := by
  have notdiv : runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())≠.div := by
    intro divergent
    exact chosen_terminating_no_infinite admissible run terminal
      (chosen_supported_loop_infinite memory hooks floats allocator steps initial divergent)
  have safe := chosen_supported_loop_stops memory hooks floats allocator steps initial
  generalize answerEq : runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())=answer at safe notdiv ⊢
  cases safe with
  | ret post => exact .ret post
  | div => exact False.elim (notdiv rfl)
end Exec.Theorems
