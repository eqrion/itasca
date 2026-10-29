import Itasca.Runtime.SourceMachine.Numeric.OperandBounds
import Itasca.Runtime.SourceMachine.Numeric.TransitionSafety

namespace Itasca.Runtime.Abs.Numeric
open SpecExt Itasca.Runtime.Spec

theorem transition_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op = .next next) :
    NextSim ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ next := by
  have hf : FrameTyped s { f with code := op.source :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  have hr : Forall FrameWf rest := by
    cases typed.frames with | cons _ h => exact framesTyped_wf h
  obtain ⟨hw, hl, hv, hc⟩ := frameTyped_wf hf
  obtain ⟨front, a, b, values, hfront, heights⟩ := op.typed_operands_bounds hf
  have same : { f with code := op.source :: after } =
      { f with code := op.source :: after, vals := front ++ op.operands a b } := by
    cases f; simp_all
  conv at step => lhs; arg 2; rw [same]
  rw [transition_operands _ { f with code := op.source :: after } rest after front op a b, finish] at step
  cases resultEq : op.apply a b with
  | none => simp only [resultEq, reduceCtorEq] at step
  | some result =>
    simp only [resultEq, advance, AResult.next.injEq] at step
    rw [← step]
    apply NextSim.single
    simpa only [values] using op.simulation s ambient f rest after front a b result resultEq
      typed.store typed.ambient hw hl hfront (fun i hi => hc i (by simp [hi])) hr heights

theorem transition_trap_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op = .trap) :
    ∃ n, 0 < n ∧ StepsHN n
      (decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  have hf : FrameTyped s { f with code := op.source :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  have hr : Forall FrameWf rest := by
    cases typed.frames with | cons _ h => exact framesTyped_wf h
  obtain ⟨hw, hl, hv, hc⟩ := frameTyped_wf hf
  obtain ⟨front, a, b, values, hfront, heights⟩ := op.typed_operands_bounds hf
  have same : { f with code := op.source :: after } =
      { f with code := op.source :: after, vals := front ++ op.operands a b } := by
    cases f; simp_all
  conv at step => lhs; arg 2; rw [same]
  rw [transition_operands _ { f with code := op.source :: after } rest after front op a b, finish] at step
  cases resultEq : op.apply a b with
  | none =>
    simpa only [values] using op.trap_simulation s ambient f rest after front a b resultEq
      typed.store typed.ambient hw hl hfront (fun i hi => hc i (by simp [hi])) hr heights
  | some result => simp only [resultEq, advance, reduceCtorEq] at step
theorem astep_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ = .next next) :
    NextSim ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ next := by
  have hf : FrameTyped s { f with code := op.source :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  rw [astep_typed_eq ⟨s, ambient, [], []⟩ f rest after op hf] at step
  exact transition_simulation s ambient f rest after op next typed step

theorem astep_trap_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ = .trap) :
    ∃ n, 0 < n ∧ StepsHN n
      (decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) []
      ⟨⟨s, ambient⟩, [.TRAP]⟩ := by
  have hf : FrameTyped s { f with code := op.source :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  rw [astep_typed_eq ⟨s, ambient, [], []⟩ f rest after op hf] at step
  exact transition_trap_simulation s ambient f rest after op typed step

end Itasca.Runtime.Abs.Numeric
