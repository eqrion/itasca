import Exec.Abs.Float.ChosenSimulation
import Exec.Abs.Float.Transition
import Exec.Abs.Float.Progress
namespace Exec.Abs.Float
open SpecExt Exec.Spec

/-- Scalar transition retaining the selected numeric policy and occurrence. -/
inductive ChosenTransition (choices : SourceChoices) (occurrence : Nat) (s : AState) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Instruction) : AResult → Prop where
  | next (front : List val) (a b bits : Nat)
      (values : f.vals = front ++ op.operands a b)
      (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
      (effect : op.ChosenResult choices occurrence a b (some bits)) :
      ChosenTransition choices occurrence s f rest after op
        (advance s { f with code := after, vals := front ++ [.CONST op.output (numberOfBits op.output bits)] } rest)
  | trap (front : List val) (a b : Nat)
      (values : f.vals = front ++ op.operands a b)
      (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
      (effect : op.ChosenResult choices occurrence a b none) : ChosenTransition choices occurrence s f rest after op .trap

theorem chosen_transition_preservation {choices : SourceChoices} {occurrence : Nat} (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : ChosenTransition choices occurrence ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op (.next next)) :
    ATyped next := by
  cases step with
  | next front a b bits values first second effect =>
    have hf : FrameTyped s { f with code := op.source :: after } [] := by
      cases typed.frames with | cons h _ => exact h
    apply active_frame_preservation typed (op.frame_preservation front a b bits typed.store effect.1 ?_) rfl
    change f.vals = front ++ op.operands a b at values
    simpa only [values] using hf


theorem chosen_transition_simulation {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat} (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : ChosenTransition choices occurrence ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op (.next next)) :
    ChoiceStep choices occurrence (decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) [] (decode next) := by
  cases step with
  | next front a b bits values first second effect =>
    change f.vals = front ++ op.operands a b at values
    have hf : FrameTyped s { f with code := op.source :: after } [] := by
      cases typed.frames with | cons h _ => exact h
    have hr : Forall FrameWf rest := by
      cases typed.frames with | cons _ h => exact framesTyped_wf h
    obtain ⟨hw, hl, _, hc⟩ := frameTyped_wf hf
    obtain ⟨frontWf, heights⟩ := op.prefix_bounds hf front a b values
    simpa only [values] using op.chosen_simulation admissible s ambient f rest after front a b bits first second effect
      typed.store typed.ambient hw hl frontWf (fun i hi => hc i (by simp [hi])) hr heights

theorem chosen_transition_trap_simulation {choices : SourceChoices} (admissible : choices.Admissible) {occurrence : Nat} (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : ChosenTransition choices occurrence ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op .trap) :
    ∃ n, 0 < n ∧ ChosenStepsN choices occurrence n
      (decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  cases step with
  | trap front a b values first second effect =>
    change f.vals = front ++ op.operands a b at values
    have hf : FrameTyped s { f with code := op.source :: after } [] := by
      cases typed.frames with | cons h _ => exact h
    have hr : Forall FrameWf rest := by
      cases typed.frames with | cons _ h => exact framesTyped_wf h
    obtain ⟨hw, hl, _, hc⟩ := frameTyped_wf hf
    obtain ⟨frontWf, heights⟩ := op.prefix_bounds hf front a b values
    simpa only [values] using op.chosen_trap_simulation admissible s ambient f rest after front a b first second effect
      typed.store typed.ambient hw hl frontWf (fun i hi => hc i (by simp [hi])) hr heights

end Exec.Abs.Float
