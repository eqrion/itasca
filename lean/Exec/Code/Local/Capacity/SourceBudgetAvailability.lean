import Exec.Code.Local.Capacity.BudgetEffects

namespace Exec.Code
open Aeneas Aeneas.Std

/-- A source-byte allowance for every compiler counter, relative to the
already prepared function budget. Limits and retained errors are unchanged. -/
def SourceCompilationBudget {A : Type} (initial current : runtime.compiler.Budget A)
    (rate : ChargeCounter → Nat) (position : Nat) : Prop :=
  CompilationBudgetEffect initial current (fun counter => rate counter * position)

theorem SourceCompilationBudget.initial {A : Type} (initial : runtime.compiler.Budget A)
    (rate : ChargeCounter → Nat) : SourceCompilationBudget initial initial rate 0 := by
  simpa [SourceCompilationBudget] using CompilationBudgetEffect.refl initial

/-- Callback charges are paid by the independently consumed source span.
In particular table labels may consume many bytes within a single reader. -/
theorem SourceCompilationBudget.advance {A : Type}
    {initial before after : runtime.compiler.Budget A} {rate allowance : ChargeCounter → Nat}
    {start finish : Nat} (held : SourceCompilationBudget initial before rate start)
    (effect : CompilationBudgetEffect before after allowance)
    (consumed : start ≤ finish)
    (paid : ∀ counter, allowance counter ≤ rate counter * (finish-start)) :
    SourceCompilationBudget initial after rate finish := by
  apply (held.trans effect).weaken
  intro counter
  have room := paid counter
  have sum : rate counter * start + rate counter * (finish-start) = rate counter * finish := by
    rw [← Nat.mul_add,Nat.add_sub_of_le consumed]
  omega

/-- An output limit and a source-paid remaining span imply actual counter
headroom. No absence-of-exhaustion or accepted callback premise occurs here. -/
theorem SourceCompilationBudget.room {A : Type}
    {initial current : runtime.compiler.Budget A} {rate : ChargeCounter → Nat}
    {position length amount bytes : Nat}
    (held : SourceCompilationBudget initial current rate position) (counter : ChargeCounter)
    (limit : (counter.used initial).val + rate counter * length ≤ (counter.limit initial).val)
    (remaining : position+bytes ≤ length) (paid : amount ≤ rate counter * bytes) :
    (counter.used current).val + amount ≤ (counter.limit current).val := by
  have used := (held.counts counter).2
  have frames : counter.limit current = counter.limit initial := by
    cases counter <;> simp only [ChargeCounter.limit,held.limits]
  have span : rate counter * position + rate counter * bytes ≤ rate counter * length := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ remaining
  rw [frames]
  omega

/-- One source byte pays one instruction whenever the configured source rate
is positive and the complete remaining-body demand fits the limit. -/
theorem SourceCompilationBudget.instruction_room {A : Type}
    {initial current : runtime.compiler.Budget A} {rate : ChargeCounter → Nat}
    {position length : Nat} (held : SourceCompilationBudget initial current rate position)
    (limit : initial.instructions.val + rate .instructions * length ≤ initial.limits.max_instructions.val)
    (remaining : position < length) (positive : 0 < rate .instructions) :
    current.instructions.val < current.limits.max_instructions.val := by
  have room := held.room .instructions limit (bytes := 1) (amount := 1) (by omega) (by omega)
  change current.instructions.val+1 ≤ current.limits.max_instructions.val at room
  omega

end Exec.Code
