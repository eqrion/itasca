import Exec.Abs.Numeric.Transition
import Exec.Abs.ReferenceBounds

namespace Exec.Abs.Numeric

theorem finish_reference_bound {bound s f rest next after front op a b}
    (results : ValuesBound bound s.results)
    (locals : ValuesBound bound f.locals) (values : ValuesBound bound front)
    (frames : ∀ item ∈ rest, FrameReferencesBound bound item)
    (step : finish s f rest after front op a b = .next next) :
    StateReferencesBound bound next := by
  unfold finish at step
  split at step
  · contradiction
  · apply references_advance (step := step) results ?_ frames
    exact ⟨locals, valuesBound_append.mpr ⟨values, by simp [ValuesBound, ReferenceBound, integerVal]⟩⟩

theorem transition_reference_bound {bound s f rest next after op}
    (results : ValuesBound bound s.results)
    (frame : FrameReferencesBound bound f)
    (frames : ∀ item ∈ rest, FrameReferencesBound bound item)
    (step : transition s f rest after op = .next next) :
    StateReferencesBound bound next := by
  unfold transition at step
  split at step
  · contradiction
  next front right first =>
    have frontBound := (frame.2.pop first).1
    split at step
    · contradiction
    next bits integer =>
      split at step
      · exact finish_reference_bound results frame.1 frontBound frames step
      · split at step
        · contradiction
        next front left second =>
          split at step
          · contradiction
          · exact finish_reference_bound results frame.1 (frontBound.pop second).1 frames step
end Exec.Abs.Numeric
