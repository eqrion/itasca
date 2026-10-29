import Itasca.Runtime.Compiler.Local.Capacity.ChargeAvailability

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Numerical counter growth and retained budget metadata, independently
parameterized by an allowance for each compiler resource. -/
structure CompilationBudgetEffect {A : Type} (before after : runtime.compiler.Budget A)
    (allowance : ChargeCounter → Nat) : Prop where
  limits : after.limits = before.limits
  error : after.error = before.error
  counts : ∀ counter, (counter.used before).val ≤ (counter.used after).val ∧
    (counter.used after).val ≤ (counter.used before).val + allowance counter

theorem CompilationBudgetEffect.refl {A : Type} (budget : runtime.compiler.Budget A) :
    CompilationBudgetEffect budget budget (fun _ => 0) :=
  ⟨rfl,rfl,by intro counter; exact ⟨Nat.le_refl _,by omega⟩⟩

theorem CompilationBudgetEffect.trans {A : Type} {before middle after : runtime.compiler.Budget A}
    {first second : ChargeCounter → Nat} (a : CompilationBudgetEffect before middle first)
    (b : CompilationBudgetEffect middle after second) :
    CompilationBudgetEffect before after (fun counter => first counter + second counter) := by
  refine ⟨b.limits.trans a.limits,b.error.trans a.error,?_⟩
  intro counter
  have initial := a.counts counter
  have final := b.counts counter
  constructor <;> omega

theorem CompilationBudgetEffect.weaken {A : Type} {before after : runtime.compiler.Budget A}
    {first second : ChargeCounter → Nat} (effect : CompilationBudgetEffect before after first)
    (bounded : ∀ counter, first counter ≤ second counter) : CompilationBudgetEffect before after second := by
  refine ⟨effect.limits,effect.error,?_⟩
  intro counter
  have used := effect.counts counter
  have room := bounded counter
  constructor <;> omega

/-- An exact single-counter frame supplies the corresponding independent
resource effect while preserving all uncharged counters. -/
theorem CompilationBudgetEffect.of_counter {A : Type} (counter : ChargeCounter)
    (before : runtime.compiler.Budget A) (used : Usize) (amount : Nat)
    (lower : (counter.used before).val ≤ used.val)
    (upper : used.val ≤ (counter.used before).val+amount) :
    CompilationBudgetEffect before (counter.replace before used)
      (fun selected => if selected = counter then amount else 0) := by
  constructor
  · cases counter <;> rfl
  · cases counter <;> rfl
  · intro selected
    cases counter <;> cases selected <;>
      simp only [ChargeCounter.used,ChargeCounter.replace] at lower upper ⊢ <;>
      simp <;> omega

/-- A zero allowance retains the exact native counter, not merely an upper bound. -/
theorem CompilationBudgetEffect.uncharged {A : Type} {before after : runtime.compiler.Budget A}
    {allowance : ChargeCounter → Nat} (effect : CompilationBudgetEffect before after allowance)
    (counter : ChargeCounter) (zero : allowance counter = 0) : counter.used after = counter.used before := by
  have bounds := effect.counts counter
  apply UScalar.eq_of_val_eq
  omega

end Itasca.Runtime.Compiler
