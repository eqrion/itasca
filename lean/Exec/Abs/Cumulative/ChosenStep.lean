import Exec.Abs.Cumulative.Step
import Exec.Abs.Stateful.ChosenTransition
import Exec.Abs.Float.ChosenTransition
import Exec.Abs.Indirect.ChosenCorrect
import Exec.Abs.Supported.ChosenCorrect
import Exec.Abs.Supported.ChosenTerminal
namespace Exec.Abs.Cumulative
open SpecExt Exec.Spec

inductive ChosenStep (choices : SourceChoices) (occurrence : Nat) : AState → AResult → Prop where
  | core {before result} (equation : Core.step before=result) (executable : result≠.stuck) :
      ChosenStep choices occurrence before result
  | scalar {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {op : Float.Instruction} {result : AResult}
      (transition : Float.ChosenTransition choices occurrence ⟨s,ambient,{f with code:=op.source::after}::rest,[]⟩
        {f with code:=op.source::after} rest after op result) :
      ChosenStep choices occurrence ⟨s,ambient,{f with code:=op.source::after}::rest,[]⟩ result
  | stateful {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {op : Stateful.Instruction} {result : AResult}
      (transition : Stateful.ChosenTransition choices occurrence ⟨s,ambient,{f with code:=op.source::after}::rest,[]⟩
        {f with code:=op.source::after} rest after op result) (executable : result≠.stuck) :
      ChosenStep choices occurrence ⟨s,ambient,{f with code:=op.source::after}::rest,[]⟩ result
  | indirect {s : store} {ambient : frame} {f : AFrame} {rest : List AFrame}
      {after : List instr} {table type : Nat} {result : AResult}
      (equation : Indirect.step ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩
        f rest table type after=result) (executable : result≠.stuck) :
      ChosenStep choices occurrence ⟨s,ambient,{f with code:=.CALL_INDIRECT (.mk_uN table) (.mk_uN type)::after}::rest,[]⟩ result

theorem ChosenStep.erases {choices : SourceChoices} (admissible : choices.Admissible) {occurrence before result}
    (step : ChosenStep choices occurrence before result) : Step before result := by
  cases step with
  | core equation executable => exact .core equation executable
  | scalar transition =>
    apply Step.scalar
    cases transition with
    | next front a b bits values first second effect => exact .next front a b bits values first second (Float.Instruction.ChosenResult.erases admissible effect)
    | trap front a b values first second effect => exact .trap front a b values first second (Float.Instruction.ChosenResult.erases admissible effect)
  | stateful transition executable => exact .stateful transition.erases executable
  | indirect equation executable => exact .indirect equation executable

theorem ChosenStep.next_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) {occurrence before next allowed}
    (step : ChosenStep choices occurrence before (.next next)) (language : Supported.Language allowed)
    (typed : CoreTyped before) (covered : SupportedState allowed before) :
    ChosenNextSim choices occurrence before next := by
  cases step with
  | core equation executable => exact Supported.step_chosen_simulation admissible vector _ _ _ typed covered language.head equation
  | scalar transition => exact ChosenNextSim.single admissible (Float.chosen_transition_simulation admissible _ _ _ _ _ _ _ typed.typed transition)
  | indirect equation executable => exact ChosenNextSim.counted (Indirect.chosen_next_simulation admissible vector _ _ _ _ _ _ _ _ _ typed equation) (by decide)
  | stateful transition executable => exact (Stateful.transition_chosen_safe admissible vector _ _ _ _ _ _ _ _ typed transition).2.2

theorem ChosenStep.trap_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) {occurrence before allowed}
    (step : ChosenStep choices occurrence before .trap) (language : Supported.Language allowed)
    (typed : CoreTyped before) (covered : SupportedState allowed before) :
    ∃ count,0<count ∧ ChosenStepsN choices occurrence count (decode before) [] ⟨⟨before.store,before.ambient⟩,[.TRAP]⟩ := by
  cases step with
  | core equation executable => exact Supported.step_chosen_trap admissible vector _ _ typed covered language.head equation
  | scalar transition => exact Float.chosen_transition_trap_simulation admissible _ _ _ _ _ _ typed.typed transition
  | indirect equation executable => exact Indirect.chosen_trap_simulation admissible vector _ _ _ _ _ _ _ _ typed equation
  | stateful transition executable => exact Stateful.transition_chosen_safe admissible vector _ _ _ _ _ _ _ _ typed transition
end Exec.Abs.Cumulative
