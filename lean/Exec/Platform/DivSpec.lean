import Exec.Generated.Types

/-! Partial correctness that names the cause of divergence. `step` accepts `DivSpec` goals and
lifts total `spec` theorems into them. -/
namespace Exec
open Aeneas Aeneas.Std

/-- `m` returns a value satisfying `post`, or diverges and `cause` holds. -/
inductive DivSpec {α : Type} (cause : Prop) : Result α → WP.Post α → Prop where
  | ret {post : WP.Post α} {x : α} : post x → DivSpec cause (.ok x) post
  | div (post : WP.Post α) : cause → DivSpec cause .div post

namespace DivSpec

theorem mono {α : Type} {cause : Prop} {P₁ : WP.Post α} {m : Result α} {P₀ : WP.Post α}
    (h : DivSpec cause m P₀) : (∀ x, P₀ x → P₁ x) → DivSpec cause m P₁ := by
  intro weaken
  cases h with
  | ret post => exact .ret (weaken _ post)
  | div _ diverged => exact .div _ diverged

theorem bind {α β : Type} {cause : Prop} {k : α → Result β} {Pₖ : WP.Post β} {m : Result α}
    {Pₘ : WP.Post α} :
    DivSpec cause m Pₘ → (∀ x, Pₘ x → DivSpec cause (k x) Pₖ) → DivSpec cause (Std.bind m k) Pₖ := by
  intro first rest
  cases first with
  | ret post => rw [bind_ok]; exact rest _ post
  | div _ diverged => rw [bind_div]; exact .div _ diverged

theorem of_spec (cause : Prop) (α : Type) (m : Result α) (post : WP.Post α)
    (h : WP.spec m post) : DivSpec cause m post := by
  cases h with
  | ret post => exact .ret post

theorem of_dspec {α : Type} {cause : Prop} {m : Result α} {post : WP.Post α}
    (h : WP.dspec m post) (diverged : m = .div → cause) : DivSpec cause m post := by
  cases h with
  | ret post => exact .ret post
  | div _ => exact .div _ (diverged rfl)

theorem dspec {α : Type} {cause : Prop} {m : Result α} {post : WP.Post α}
    (h : DivSpec cause m post) : WP.dspec m post := by
  cases h with
  | ret post => exact .ret post
  | div _ _ => exact .div _

theorem diverged {α : Type} {cause : Prop} {m : Result α} {post : WP.Post α}
    (h : DivSpec cause m post) (divergent : m = .div) : cause := by
  cases h with
  | ret _ => exact absurd divergent ok_not_div
  | div _ cause => exact cause

/-- A computation that returns, or diverges with its cause. -/
theorem imp_exists {α : Type} {cause : Prop} {m : Result α} {post : WP.Post α}
    (h : DivSpec cause m post) : (∃ x, m = .ok x ∧ post x) ∨ (m = .div ∧ cause) := by
  cases h with
  | ret post => exact Or.inl ⟨_, rfl, post⟩
  | div _ diverged => exact Or.inr ⟨rfl, diverged⟩

/-- Divergence without a cause is impossible, so the computation returns. -/
theorem spec {α : Type} {m : Result α} {post : WP.Post α} (h : DivSpec False m post) :
    WP.spec m post := by
  cases h with
  | ret post => exact .ret post
  | div _ impossible => exact impossible.elim

@[simp] theorem ok_iff {α : Type} {cause : Prop} {x : α} {post : WP.Post α} :
    DivSpec cause (.ok x) post ↔ post x := by
  constructor
  · intro h
    rcases h.imp_exists with ⟨y, same, holds⟩ | ⟨impossible, _⟩
    · rw [Result.ok_injective same]; exact holds
    · exact absurd impossible ok_not_div
  · exact .ret

end DivSpec

#register_spec_info {
    spec_name := ``Exec.DivSpec
    arity := 4
    program_index := 2
    post_index := 3
    mk_spec_mono := ``Exec.DivSpec.mono
    mk_spec_mono_skip_args := 3
    mk_spec_bind := ``Exec.DivSpec.bind
    mk_spec_bind_skip_args := 5
    prepare_intro_outputs := ``Aeneas.Step.prepareIntroOutputs
    to_mvcgen := .none
    liftings := #[
      { from_statement := ``Aeneas.Std.WP.spec
        conversion_thm := ``Exec.DivSpec.of_spec
        conversion_thm_inferred_args := 4 }
    ]
  }

end Exec
