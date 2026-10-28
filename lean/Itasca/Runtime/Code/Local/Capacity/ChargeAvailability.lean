import Itasca.Runtime.Code.Local.Capacity.BudgetAvailability

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

inductive ChargeCounter where
  | instructions | branches | controls | locals
  deriving DecidableEq

abbrev ChargeCounter.resource : ChargeCounter → runtime.compiler.CompileResource
  | .instructions => .Instructions | .branches => .BranchTableEntries | .controls => .Controls | .locals => .Locals

abbrev ChargeCounter.used {A : Type} (kind : ChargeCounter) (budget : runtime.compiler.Budget A) : Usize :=
  match kind with
  | .instructions => budget.instructions | .branches => budget.branches | .controls => budget.controls | .locals => budget.locals

abbrev ChargeCounter.limit {A : Type} (kind : ChargeCounter) (budget : runtime.compiler.Budget A) : Usize :=
  match kind with
  | .instructions => budget.limits.max_instructions | .branches => budget.limits.max_branch_table_entries
  | .controls => budget.limits.max_controls | .locals => budget.limits.max_locals

abbrev ChargeCounter.replace {A : Type} (kind : ChargeCounter) (budget : runtime.compiler.Budget A) (used : Usize) : runtime.compiler.Budget A :=
  match kind with
  | .instructions => {budget with instructions := used} | .branches => {budget with branches := used}
  | .controls => {budget with controls := used} | .locals => {budget with locals := used}

/-- Available charging changes exactly one counter. All other counters,
allocator marker, error state, and limits are retained by the actual operation. -/
theorem charge_counter_available {A : Type} (ops : runtime.platform.Alloc A)
    (kind : ChargeCounter) (budget : runtime.compiler.Budget A)
    (room : (kind.used budget).val < (kind.limit budget).val) :
    runtime.compiler.Budget.charge ops budget kind.resource ⦃ out =>
      out.1 = .Ok () ∧ ∃ used, out.2 = kind.replace budget used ∧
        used.val = (kind.used budget).val + 1 ⦄ := by
  cases kind <;>
    simp only [ChargeCounter.used,ChargeCounter.limit] at room <;>
    simp only [ChargeCounter.resource,runtime.compiler.Budget.charge]
  all_goals
    split
    · rename_i full
      scalar_tac
    · step as ⟨used,advanced⟩
      exact ⟨used,rfl,advanced⟩

end Itasca.Runtime.Code
