import Exec.Abs.Stateful.ChosenTransition
namespace Exec.Abs.Stateful
open SpecExt Exec.Spec

def Instruction.choosesGrowth : Instruction → Bool
  | .memoryGrow | .tableGrow _ => true
  | _ => false

/-- For all other operations the source policy consumes no growth reply. -/
theorem Transition.chosen_of_no_growth {choices : SourceChoices} {occurrence : Nat}
    {s f rest after op result} (step : Transition s f rest after op result)
    (ordinary : op.choosesGrowth=false) :
    ChosenTransition choices occurrence s f rest after op result := by
  obtain ⟨selection,allowed,equation⟩ := step
  refine ⟨selection,allowed,?_,equation⟩
  cases op <;> simp_all only [Instruction.choosesGrowth,Selection.Matches,Bool.true_eq_false]

/-- The admissible source policy itself supplies an allowed reply on every
actual operand/object tuple; no whole execution trace is assumed. -/
theorem memory_policy_allowed {choices : SourceChoices} (admissible : choices.Admissible)
    (occurrence : Nat) (object : meminst) (delta : Nat) :
    MemoryGrowthChoice object delta (choices.memory occurrence object delta) := by
  cases selected : choices.memory occurrence object delta with
  | none => exact .refused
  | some next => exact .grown (admissible.memory occurrence object delta next selected)

theorem table_policy_allowed {choices : SourceChoices} (admissible : choices.Admissible)
    (occurrence : Nat) (object : tableinst) (delta : Nat) (value : ref) :
    TableGrowthChoice object delta value (choices.table occurrence object delta value) := by
  cases selected : choices.table occurrence object delta value with
  | none => exact .refused
  | some next => exact .grown (admissible.table occurrence object delta value next selected)
end Exec.Abs.Stateful
