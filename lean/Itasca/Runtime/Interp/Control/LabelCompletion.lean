import Itasca.Runtime.Interp.Relations.ControlPoint
import Itasca.Runtime.SourceMachine.Sim.Step

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Generated empty-code typing gives both the precise result suffix and the
source label-completion reduction, without a runtime result-shape premise. -/
theorem typed_label_completion (s : store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (label : Abs.Label) (labels : List Abs.Label)
    (typed : Abs.FrameTyped s { f with code := [], labels := label :: labels } []) :
    f.vals.length = label.height + label.resultTypes.length ∧
    (f.vals.drop label.height).map Abs.valueType = label.resultTypes ∧
    Abs.astep ⟨s, ambient, { f with code := [], labels := label :: labels } :: rest, []⟩ =
      .next ⟨s, ambient, { f with code := label.after, labels := labels } :: rest, []⟩ := by
  cases typed with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨saved, heq, height⟩ := Abs.code_empty_shape (Abs.value_types_concrete f.vals) hc
    have hstack : f.vals.length = label.height + label.resultTypes.length := by
      have h := congrArg List.length heq
      simpa only [List.length_map, List.length_append, height] using h
    have htail : (f.vals.drop label.height).map Abs.valueType = label.resultTypes := by
      rw [List.map_drop, heq, ← height, List.drop_left]
    exact ⟨hstack, htail, by simp [Abs.astep, hstack, htail, Abs.advance]⟩

end Itasca.Runtime.Interp
