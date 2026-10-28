import Itasca.Runtime.Abs.Float.Transition
namespace Itasca.Runtime.Abs.Float
open SpecExt Itasca.Runtime.Spec
theorem transition_positive (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (op : Instruction) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩)
    (step : Transition ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩
      { f with code := op.source :: after } rest after op (.next next)) :
    StepH (decode ⟨s, ambient, { f with code := op.source :: after } :: rest, []⟩) [] (decode next) := by
  cases step with
  | next front a b bits values first second effect =>
    change f.vals = front ++ op.operands a b at values
    have hf : FrameTyped s { f with code := op.source :: after } [] := by
      cases typed.frames with | cons h _ => exact h
    have hr : Forall FrameWf rest := by
      cases typed.frames with | cons _ h => exact framesTyped_wf h
    obtain ⟨hw, hl, _, hc⟩ := frameTyped_wf hf
    obtain ⟨frontWf, heights⟩ := op.prefix_bounds hf front a b values
    simpa only [values] using op.simulation s ambient f rest after front a b bits first second effect
      typed.store typed.ambient hw hl frontWf (fun i hi => hc i (by simp [hi])) hr heights

end Itasca.Runtime.Abs.Float
