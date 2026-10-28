import Itasca.Runtime.Abs.Numeric.Transition
import Itasca.Runtime.Abs.Ownership.Bounds

namespace Itasca.Runtime.Abs.Ownership
open Itasca.Runtime.Abs.Numeric

theorem finish_ownership {bound s f rest next after front op a b}
    (results : ValuesOwned bound s.results)
    (locals : ValuesOwned bound f.locals) (values : ValuesOwned bound front)
    (frames : ∀ item ∈ rest, FrameOwned bound item)
    (step : finish s f rest after front op a b = .next next) :
    StateOwned bound next := by
  unfold finish at step
  split at step
  · contradiction
  · apply ownership_advance (step := step) results ?_ frames
    exact ⟨locals, valuesOwned_append.mpr ⟨values, by simp [ValuesOwned, ValueOwned, integerVal]⟩⟩

theorem transition_ownership {bound s f rest next after op}
    (results : ValuesOwned bound s.results)
    (frame : FrameOwned bound f)
    (frames : ∀ item ∈ rest, FrameOwned bound item)
    (step : transition s f rest after op = .next next) :
    StateOwned bound next := by
  unfold transition at step
  split at step
  · contradiction
  next front right first =>
    have frontBound := (frame.2.pop first).1
    split at step
    · contradiction
    next bits integer =>
      split at step
      · exact finish_ownership results frame.1 frontBound frames step
      · split at step
        · contradiction
        next front left second =>
          split at step
          · contradiction
          · exact finish_ownership results frame.1 (frontBound.pop second).1 frames step
end Itasca.Runtime.Abs.Ownership
