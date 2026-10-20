import Exec.Interp.Relations.Epilogue
import Exec.Abs.Sim.ChosenBasic
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt Exec.Spec

theorem frame_end_chosen_source {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : _root_.store) (ambient : frame) (f : Abs.AFrame)
    (rest : List Abs.AFrame)
    (typed : Abs.ATyped ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩) :
    f.vals.map Abs.valueType = f.resultTypes ∧
    Abs.ATyped (returnedState s ambient rest f.vals) ∧
    Abs.ChosenNextSim choices occurrence ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩
      (returnedState s ambient rest f.vals) := by
  have frameTyped : Abs.FrameTyped s { f with code := [], labels := [] } [] := by
    cases typed.frames with | cons h _ => exact h
  have values := Abs.frame_end_typed frameTyped
  have types := Abs.results_type_of_typed values
  have length : f.resultTypes.length = f.vals.length := (Spec.resultsTyped_length values).symm
  have step : Abs.astep ⟨s, ambient, { f with code := [], labels := [] } :: rest, []⟩ =
      .next (returnedState s ambient rest f.vals) := by
    cases rest <;> simp [Abs.astep, Abs.returnFrame, Abs.AFrame.arity, length, types, returnedState, Abs.advance]
  refine ⟨types, ?_, Abs.ChosenNextSim.neutral admissible vector occurrence (Abs.typed_frame_end_simulation s ambient f rest _ typed step)
    (by simp only [List.map_nil,neutralActive])⟩
  have preserved := Abs.return_values_preservation typed values
  cases rest <;> exact preserved


end Exec.Interp
