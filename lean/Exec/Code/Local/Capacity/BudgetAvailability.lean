import Exec.Code.Local.Relations.Common.LayoutProofs

/-! Compiler primitives accept independently bounded available resources.
These lemmas do not assume a successful callback or compilation trace. -/
namespace Exec.Code
open Aeneas Aeneas.Std

/-- An available bounded reserve request makes the actual compiler append
succeed with the exact appended vector and unchanged budget. -/
theorem budget_push_available {A T : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (values : alloc.vec.Vec T) (value : T)
    (fits : values.val.length < Usize.max) (request : values.val.length + 1 ≤ bound) :
    runtime.compiler.Budget.push ops budget values value ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = budget ∧ out.2.2.val = values.val ++ [value] ⦄ := by
  have reserve := available T values 1#usize (by simpa using request)
  unfold runtime.compiler.Budget.push
  rw [reserve,bind_ok]
  change (do
    let after ← alloc.vec.Vec.push values value
    pure (core.result.Result.Ok (),budget,after)) ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = budget ∧ out.2.2.val = values.val ++ [value] ⦄
  step as ⟨after,appended⟩
  exact appended

/-- A remaining instruction budget excludes both resource rejection and checked
arithmetic failure for the actual charge operation. -/
theorem charge_instruction_available {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A)
    (room : budget.instructions.val < budget.limits.max_instructions.val) :
    runtime.compiler.Budget.charge ops budget .Instructions ⦃ out =>
      out.1 = .Ok () ∧ out.2.instructions.val = budget.instructions.val + 1 ∧
      out.2.limits = budget.limits ∧ out.2.error = budget.error ⦄ := by
  have notFull : ¬ budget.instructions ≥ budget.limits.max_instructions := by scalar_tac
  simp only [runtime.compiler.Budget.charge,notFull,↓reduceIte]
  step as ⟨used,increment⟩
  exact increment

theorem charge_branch_available {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A)
    (room : budget.branches.val < budget.limits.max_branch_table_entries.val) :
    runtime.compiler.Budget.charge ops budget .BranchTableEntries ⦃ out =>
      out.1 = .Ok () ∧ out.2.branches.val = budget.branches.val + 1 ∧
      out.2.limits = budget.limits ∧ out.2.error = budget.error ⦄ := by
  have notFull : ¬ budget.branches ≥ budget.limits.max_branch_table_entries := by scalar_tac
  simp only [runtime.compiler.Budget.charge,notFull,↓reduceIte]
  step as ⟨used,increment⟩
  exact increment

theorem charge_control_available {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A)
    (room : budget.controls.val < budget.limits.max_controls.val) :
    runtime.compiler.Budget.charge ops budget .Controls ⦃ out =>
      out.1 = .Ok () ∧ out.2.controls.val = budget.controls.val + 1 ∧
      out.2.limits = budget.limits ∧ out.2.error = budget.error ⦄ := by
  have notFull : ¬ budget.controls ≥ budget.limits.max_controls := by scalar_tac
  simp only [runtime.compiler.Budget.charge,notFull,↓reduceIte]
  step as ⟨used,increment⟩
  exact increment

theorem charge_local_available {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A)
    (room : budget.locals.val < budget.limits.max_locals.val) :
    runtime.compiler.Budget.charge ops budget .Locals ⦃ out =>
      out.1 = .Ok () ∧ out.2.locals.val = budget.locals.val + 1 ∧
      out.2.limits = budget.limits ∧ out.2.error = budget.error ⦄ := by
  have notFull : ¬ budget.locals ≥ budget.limits.max_locals := by scalar_tac
  simp only [runtime.compiler.Budget.charge,notFull,↓reduceIte]
  step as ⟨used,increment⟩
  exact increment

end Exec.Code
