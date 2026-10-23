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

end Exec.Abs.Stateful
