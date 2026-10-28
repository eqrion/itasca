import Exec.Code.Local.Capacity.BudgetEffects

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Each streamed branch-table label, including the default label, accepts
from independent branch budget and scratch-vector bounds. -/
theorem compiler_branch_label_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (depth : U32)
    (room : compiler.budget.branches.val < compiler.budget.limits.max_branch_table_entries.val)
    (capacity : compiler.table_depths.length < Usize.max)
    (request : compiler.table_depths.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops compiler state depth
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
          (fun counter => if counter = .branches then 1 else 0) ∧
        out.2.table_depths.val = compiler.table_depths.val ++ [depth] ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
  step with charge_counter_available ops .branches compiler.budget room
    as ⟨status,budget,accepted,used,same,usedEq⟩
  rw [accepted,same]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available (ChargeCounter.branches.replace compiler.budget used)
    compiler.table_depths depth capacity request as ⟨status,budget,depths,accepted,same,appended⟩
  refine ⟨accepted,?_,appended⟩
  rw [same]
  exact .of_counter .branches compiler.budget used 1
    (by simp [ChargeCounter.used] at usedEq ⊢; omega)
    (by simp [ChargeCounter.used] at usedEq ⊢; omega)

end Itasca.Runtime.Code
