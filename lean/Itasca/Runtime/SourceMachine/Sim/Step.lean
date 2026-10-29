import Itasca.Runtime.SourceMachine.Sim.Instruction

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

theorem typed_label_end_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (label : Label) (labels : List Label) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := [], labels := label :: labels } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := [], labels := label :: labels } :: rest, []⟩ = .next next) :
    NextSim ⟨s, ambient, { f with code := [], labels := label :: labels } :: rest, []⟩ next := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    obtain ⟨hw, hl, hv, _⟩ := frameTyped_wf hf
    have nested : ∀ outer ∈ labels, outer.height ≤ label.height := by
      cases hf with
      | mk C _ _ _ _ _ code _ => exact (codeStack_labels_nested code).1
    have heights := frameTyped_heights hf
    have result := label_exit_simulation s ambient f rest label labels typed.store typed.ambient hw hl hv
      (framesTyped_wf hr) (heights label (by simp)) nested
    simp only [astep] at step
    split at step
    · simp only [advance, AResult.next.injEq] at step
      rw [← step]
      exact .single result
    · contradiction

end Itasca.Runtime.Abs
