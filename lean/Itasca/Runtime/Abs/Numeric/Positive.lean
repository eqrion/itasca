import Itasca.Runtime.Abs.Numeric.TransitionSimulation
import Itasca.Runtime.Abs.Core.Pure
namespace Itasca.Runtime.Abs.Numeric
open SpecExt Itasca.Runtime.Spec
theorem transition_positive (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op = .next next) :
    StepH (decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) [] (decode next) := by
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
    simpa only [values] using op.simulation s ambient f rest after front a b result resultEq
      typed.store typed.ambient hw hl hfront (fun i hi => hc i (by simp [hi])) hr heights

theorem astep_positive (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩ = .next next) :
    StepH (decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) [] (decode next) := by
  have hf : FrameTyped s { f with code := op.source :: after } [] := by
    cases typed.frames with | cons h _ => exact h
  rw [astep_typed_eq ⟨s, ambient, [], []⟩ f rest after op hf] at step
  exact transition_positive s ambient f rest after op next typed step

theorem core_step_positive (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩)
    (step : Core.step ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩ = .next next) :
    StepH (decode ⟨s,ambient,{f with code := op.source::after}::rest,[]⟩) [] (decode next) := by
  have hf : FrameTyped s {f with code := op.source::after} [] := by
    cases typed.frames with | cons head _ => exact head
  simp only [Core.step] at step
  rw [Core.instruction_slice s ambient {f with code := op.source::after} rest op.source after (.numeric op) hf] at step
  exact astep_positive s ambient f rest after op next typed step
end Itasca.Runtime.Abs.Numeric
