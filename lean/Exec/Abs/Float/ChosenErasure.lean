import Exec.Abs.Float.ChosenTransition
namespace Exec.Abs.Float
open SpecExt Exec.Spec

theorem ChosenTransition.erases {choices : SourceChoices} (admissible : choices.Admissible)
    {occurrence s f rest after op result}
    (step : ChosenTransition choices occurrence s f rest after op result) :
    Transition s f rest after op result := by
  cases step with
  | next front a b bits values first second effect =>
    exact .next front a b bits values first second (Instruction.ChosenResult.erases admissible effect)
  | trap front a b values first second effect =>
    exact .trap front a b values first second (Instruction.ChosenResult.erases admissible effect)
end Exec.Abs.Float
