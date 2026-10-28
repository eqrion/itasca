import Exec.Abs.Numeric.Astep
import Exec.Abs.Numeric.Transition
import Exec.Abs.Numeric.InstructionSafety

namespace Itasca.Runtime.Abs.Numeric
open SpecExt Itasca.Runtime.Spec

theorem transition_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op = .next next) :
    ATyped next := by
  have hf : FrameTyped s { f with code := op.source :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  obtain ⟨front, a, b, values⟩ := op.typed_operands hf
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
    apply active_frame_preservation typed (op.frame_preservation a b result typed.store ?_) rfl
    simpa only [values] using hf
theorem astep_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ = .next next) :
    ATyped next := by
  have hf : FrameTyped s { f with code := op.source :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  rw [astep_typed_eq ⟨s, ambient, [], []⟩ f rest after op hf] at step
  exact transition_preservation s ambient f rest after op next typed step

end Itasca.Runtime.Abs.Numeric
