import Exec.Abs.Simd.ChosenStep
import Exec.Spec.Choices.ChosenPureNeutral
namespace Exec.Abs.Simd
open SpecExt Exec.Spec

def NeutralHead (state : AState) : Prop :=
  match state.frames with
  | [] => True
  | frame::_ => match frame.code with
    | [] => True
    | source::_ => neutralActive [admininstr_instr source]=true

theorem Step.chosen_of_neutral {choices : SourceChoices} (vector : choices.vector=firstVectorChoice)
    (occurrence : Nat) {before result} (step : Step before result) (neutral : NeutralHead before) :
    ChosenStep choices occurrence before result := by
  cases step with
  | @pure s ambient f rest after source inputs output next signature transition =>
    cases transition with
    | next front operands value values types effect =>
      apply ChosenStep.pure signature values types effect
      apply chosen_pure_neutral occurrence vector effect.1
      apply neutralActive_pure
      rw [neutralActive_vals]
      change neutralActive [admininstr_instr source]=true at neutral
      cases signature <;> simpa only [admininstr_instr,neutralActive] using neutral
  | constant => exact .constant
  | memory signature transition => exact .memory signature transition
end Exec.Abs.Simd
