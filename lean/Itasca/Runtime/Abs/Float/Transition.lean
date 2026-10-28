import Itasca.Runtime.Abs.Float.Simulation
import Itasca.Runtime.Abs.Float.Progress
namespace Itasca.Runtime.Abs.Float
open SpecExt Itasca.Runtime.Spec

/-- Relational scalar float transition: every permitted NaN result remains available. -/
inductive Transition (s : AState) (f : AFrame) (rest : List AFrame)
    (after : List instr) (op : Instruction) : AResult → Prop where
  | next (front : List val) (a b bits : Nat)
      (values : f.vals = front ++ op.operands a b)
      (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
      (effect : op.Result a b (some bits)) :
      Transition s f rest after op
        (advance s { f with code := after, vals := front ++ [.CONST op.output (numberOfBits op.output bits)] } rest)
  | trap (front : List val) (a b : Nat)
      (values : f.vals = front ++ op.operands a b)
      (first : a < 2^sizenn op.input) (second : b < 2^sizenn op.input)
      (effect : op.Result a b none) : Transition s f rest after op .trap

theorem transition_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : Transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op (.next next)) :
    ATyped next := by
  cases step with
  | next front a b bits values first second effect =>
    have hf : FrameTyped s { f with code := op.source :: after } [] := by
      cases typed.frames with | cons h _ => exact h
    apply active_frame_preservation typed (op.frame_preservation front a b bits typed.store effect.1 ?_) rfl
    change f.vals = front ++ op.operands a b at values
    simpa only [values] using hf

theorem Instruction.operands_length (op : Instruction) (a b : Nat) :
    (op.operands a b).length = op.arity := by cases op <;> rfl

theorem Instruction.prefix_bounds (op : Instruction) {s : store} {f : AFrame} {after : List instr}
    (typed : FrameTyped s { f with code := op.source :: after } [])
    (front : List val) (a b : Nat) (values : f.vals = front ++ op.operands a b) :
    Forall wf_val front ∧ (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨other, x, y, otherValues, _, _, _, heights⟩ := op.typed_operands typed
  have lengthEq : other.length = front.length := by
    have left := congrArg List.length values
    have right := congrArg List.length otherValues
    simp only [List.length_append, Instruction.operands_length] at left right
    omega
  constructor
  · intro value member
    have valid := (frameTyped_wf typed).2.2.1
    apply valid value
    change value ∈ f.vals
    rw [values]
    exact List.mem_append_left _ member
  · simpa only [lengthEq] using heights

theorem transition_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : Transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op (.next next)) :
    NextSim ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ next := by
  cases step with
  | next front a b bits values first second effect =>
    change f.vals = front ++ op.operands a b at values
    have hf : FrameTyped s { f with code := op.source :: after } [] := by
      cases typed.frames with | cons h _ => exact h
    have hr : Forall FrameWf rest := by
      cases typed.frames with | cons _ h => exact framesTyped_wf h
    obtain ⟨hw, hl, _, hc⟩ := frameTyped_wf hf
    obtain ⟨frontWf, heights⟩ := op.prefix_bounds hf front a b values
    apply NextSim.single
    simpa only [values] using op.simulation s ambient f rest after front a b bits first second effect
      typed.store typed.ambient hw hl frontWf (fun i hi => hc i (by simp [hi])) hr heights

theorem transition_trap_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : Transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op .trap) :
    ∃ n, 0 < n ∧ StepsHN n
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
    simpa only [values] using op.trap_simulation s ambient f rest after front a b first second effect
      typed.store typed.ambient hw hl frontWf (fun i hi => hc i (by simp [hi])) hr heights

end Itasca.Runtime.Abs.Float
