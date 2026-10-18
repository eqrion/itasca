import Exec.Interp.Relations.Epilogue
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt
theorem frame_end_positive (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩) :
    StepH (Abs.decode ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩) []
      (Abs.decode (returnedState s ambient rest f.vals)) := by
  have frameTyped : Abs.FrameTyped s { f with code := [], labels := [] } [] := by
    cases typed.frames with | cons h _ => exact h
  have values := Abs.frame_end_typed frameTyped
  have types := Abs.results_type_of_typed values
  have length : f.resultTypes.length = f.vals.length := (Spec.resultsTyped_length values).symm
  have step : Abs.astep ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩ =
      .next (returnedState s ambient rest f.vals) := by
    cases rest <;> simp [Abs.astep, Abs.returnFrame, Abs.AFrame.arity, length, types, returnedState, Abs.advance]
  exact Abs.typed_frame_end_simulation s ambient f rest _ typed step

end Exec.Interp
