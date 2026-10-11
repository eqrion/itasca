import Aeneas

open Aeneas Aeneas.Std Lean.Order

namespace Itasca.LoopMap

private theorem admissible_bounded {α : Type} [CCPO α] (y : α) :
    admissible (fun x : α => x ⊑ y) := by
  intro c hc h
  exact csup_le hc h

/-- Changing only the representation of loop state preserves the complete
partial computation, including rejection, modeled failure, and divergence. -/
theorem conjugate {α β γ : Type} (body : α → Result (ControlFlow α γ))
    (body' : β → Result (ControlFlow β γ)) (f : α → β)
    (hbody : ∀ x, body' (f x) = do
      let cf ← body x
      pure (match cf with | .cont y => .cont (f y) | .done z => .done z))
    (x : α) : loop body x = loop body' (f x) := by
  apply PartialOrder.rel_antisymm
  · have h := loop.fixpoint_induct body
      (fun run => ∀ a, run a ⊑ loop body' (f a))
      (admissible_pi_apply _ (fun a => admissible_bounded (loop body' (f a))))
      (by
        intro run ih a
        dsimp only
        rw [loop, hbody]
        simp only [Pure.pure, Aeneas.Std.bind_assoc, Aeneas.Std.bind_ok]
        apply MonoBind.bind_mono_right (m := Result)
        intro cf
        cases cf with
        | cont a' => exact ih a'
        | done z => exact PartialOrder.rel_refl)
    exact h x
  · have hadm : admissible (fun run : β → Result γ => ∀ a, run (f a) ⊑ loop body a) := by
      apply admissible_pi
      intro a
      exact admissible_apply (fun _ r => r ⊑ loop body a) (f a)
        (admissible_bounded (loop body a))
    have h := loop.fixpoint_induct body'
      (fun run => ∀ a, run (f a) ⊑ loop body a) hadm
      (by
        intro run ih a
        dsimp only
        rw [hbody, loop]
        simp only [Pure.pure, Aeneas.Std.bind_assoc, Aeneas.Std.bind_ok]
        apply MonoBind.bind_mono_right (m := Result)
        intro cf
        cases cf with
        | cont a' => exact ih a'
        | done z => exact PartialOrder.rel_refl)
    exact h x

end Itasca.LoopMap
