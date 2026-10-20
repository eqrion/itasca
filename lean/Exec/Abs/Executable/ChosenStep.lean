import Exec.Abs.Executable.Step
import Exec.Abs.Cumulative.ChosenStep
import Exec.Abs.Simd.ChosenStep
import Exec.Abs.Sim.ChosenSelectTable
namespace Exec.Abs.Executable
open SpecExt Exec.Spec

inductive ChosenStep (choices : SourceChoices) (occurrence : Nat) : AState → AResult → Prop where
  | cumulative {before result} : Cumulative.ChosenStep choices occurrence before result → ChosenStep choices occurrence before result
  | simd {before result} : Simd.ChosenStep choices occurrence before result → ChosenStep choices occurrence before result
  | typedSelect {before next} : TypedSelect.Step before next → ChosenStep choices occurrence before (.next next)
  | branchTable {before next} : BrTable.Transition before next → ChosenStep choices occurrence before (.next next)

theorem ChosenStep.erases {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence before result} (step : ChosenStep choices occurrence before result) : Step before result := by
  cases step with
  | cumulative old => exact .cumulative (old.erases admissible)
  | simd old => exact .simd old.erases
  | typedSelect old => exact .typedSelect old
  | branchTable old => exact .branchTable old

theorem ChosenStep.next_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) {occurrence before next}
    (step : ChosenStep choices occurrence before (.next next))
    (typed : CoreTyped before) (covered : ExecutableState before) :
    ChosenNextSim choices occurrence before next := by
  cases step with
  | cumulative old => exact old.next_simulation admissible vector executable_language typed covered
  | simd old => exact old.next_simulation admissible vector typed
  | typedSelect old => exact ChosenNextSim.single admissible (old.chosen admissible vector _ typed)
  | branchTable old => exact (old.chosen admissible vector _ typed).2

theorem ChosenStep.trap_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) {occurrence before}
    (step : ChosenStep choices occurrence before .trap)
    (typed : CoreTyped before) (covered : ExecutableState before) :
    ∃ count,0<count ∧ ChosenStepsN choices occurrence count (decode before) [] ⟨⟨before.store,before.ambient⟩,[.TRAP]⟩ := by
  cases step with
  | cumulative old => exact old.trap_simulation admissible vector executable_language typed covered
  | simd old => exact old.trap_simulation admissible vector typed
end Exec.Abs.Executable
