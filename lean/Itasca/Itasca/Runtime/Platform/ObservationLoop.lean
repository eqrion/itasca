import Itasca.Runtime.Platform.Laws

/-! # Erasure through effectful loops

A projection commuting with a loop body also commutes with its least fixed
point. Both inequalities are needed: a one-way termination proof would not
establish preservation of divergence.
-/
namespace Itasca.Platform
open Aeneas Aeneas.Std Lean.Order Aeneas.Data.Coinductive

private theorem bind_right_mono {α β : Type} (r : Result α) (f g : α → Result β)
    (h : ∀ x, f x ⊑ g x) : Std.bind r f ⊑ Std.bind r g :=
  Aeneas.Std.bind_mono (fun _ : α → Result β => r) (fun k => k)
    (monotone_const _) monotone_id f g h

unseal Result in
private theorem result_div_le {α : Type} (r : Result α) : Result.div ⊑ r :=
  Eq.mpr (ITree.le_unfold (E := RustEffect) _ _) (Or.inl rfl)

def eraseFlow {α β γ δ : Type} (state : α → γ) (answer : β → δ) :
    ControlFlow α β → ControlFlow γ δ
  | .cont next => .cont (state next)
  | .done out => .done (answer out)

/-- Bind congruence under a projection; no termination assumption is used. -/
theorem bind_project {α β γ : Type} (project : α → β)
    (observed : Result α) (original : Result β)
    (next : α → Result γ) (plainNext : β → Result γ)
    (erase : (do let answer ← observed; Result.ok (project answer)) = original)
    (continued : ∀ answer, next answer = plainNext (project answer)) :
    Std.bind observed next = Std.bind original plainNext := by
  rw [← erase]
  simp only [Std.bind_assoc, bind_ok]
  apply congrArg (Std.bind observed)
  funext answer
  exact continued answer

/-- A body projection preserves the whole computation, including divergence
and terminal failure, without assuming the loop terminates. -/
theorem loop_project {α β γ δ : Type}
    (observed : α → Result (ControlFlow α β)) (original : γ → Result (ControlFlow γ δ))
    (state : α → γ) (answer : β → δ)
    (body : ∀ s, (do let out ← observed s; Result.ok (eraseFlow state answer out)) = original (state s))
    (initial : α) :
    (do let out ← Aeneas.Std.loop observed initial; Result.ok (answer out)) =
      Aeneas.Std.loop original (state initial) := by
  apply PartialOrder.rel_antisymm
  · have adm : admissible (fun run : α → Result β =>
        ∀ s, (do let out ← run s; Result.ok (answer out)) ⊑ Aeneas.Std.loop original (state s)) := by
      apply admissible_pi
      intro s
      apply admissible_apply (fun (_ : α) (value : Result β) =>
        (do let out ← value; Result.ok (answer out)) ⊑ Aeneas.Std.loop original (state s)) s
      apply Recording.result_admissible
      simpa only [bind_div] using result_div_le (Aeneas.Std.loop original (state s))
    apply Aeneas.Std.loop.fixpoint_induct observed _ adm ?_ initial
    intro run ih s
    rw [Aeneas.Std.loop.eq_def original (state s), ← body s]
    simp only [Std.bind_assoc, bind_ok]
    apply bind_right_mono
    intro out
    cases out with
    | done value => simp only [eraseFlow, bind_ok]; exact PartialOrder.rel_refl
    | cont next => simpa only [eraseFlow, bind_ok] using ih next
  · have adm : admissible (fun run : γ → Result δ =>
        ∀ s, run (state s) ⊑ (do let out ← Aeneas.Std.loop observed s; Result.ok (answer out))) := by
      apply admissible_pi
      intro s
      apply admissible_apply (fun (_ : γ) (value : Result δ) =>
        value ⊑ (do let out ← Aeneas.Std.loop observed s; Result.ok (answer out))) (state s)
      exact Recording.result_admissible _ (result_div_le _)
    apply Aeneas.Std.loop.fixpoint_induct original _ adm ?_ initial
    intro run ih s
    rw [Aeneas.Std.loop.eq_def observed s]
    dsimp only
    rw [← body s]
    simp only [Std.bind_assoc, bind_ok]
    apply bind_right_mono
    intro out
    cases out with
    | done value => simp only [eraseFlow, bind_ok]; exact PartialOrder.rel_refl
    | cont next => simpa only [eraseFlow, bind_ok] using ih next

end Itasca.Platform
