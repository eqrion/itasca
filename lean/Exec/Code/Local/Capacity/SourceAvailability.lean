import Exec.Code.Local.Capacity.BudgetAvailability
import Exec.Code.Local.Source.SourceControlBudget

/-! Actual code, control-map, and physical-frame requests fit independent
source-byte bounds. These are local demand lemmas for compiler completeness. -/
namespace Exec.Code
open Aeneas Aeneas.Std

/-- The source byte accounting pays for this actual emitted-code append. -/
theorem SourceCodeBudget.push_available {A : Type} (ops : runtime.platform.Alloc A)
    {compiler : runtime.compiler.FunctionCompiler A} {position : Nat}
    (budget : SourceCodeBudget compiler position)
    (sourceBound : position ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (available : Platform.AllocationAvailable ops (3 * position + 1))
    (instruction : runtime.bytecode.Instr) :
    runtime.compiler.Budget.push ops compiler.budget compiler.function.code instruction ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = compiler.budget ∧
      out.2.2.val = compiler.function.code.val ++ [instruction] ⦄ := by
  apply budget_push_available ops _ available _ _ _ (budget.code_capacity sourceBound)
  have bound := budget
  unfold SourceCodeBudget at bound
  omega

/-- A control-map append uses at most one entry per consumed byte plus the
function root, so its reserve request is bounded by `position + 2`. -/
theorem SourceControlBudget.map_push_available {A : Type} (ops : runtime.platform.Alloc A)
    {compiler : runtime.compiler.FunctionCompiler A} {position : Nat}
    (budget : SourceControlBudget compiler position)
    (sourceBound : position ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (available : Platform.AllocationAvailable ops (position + 2))
    (control : runtime.compiler.ControlMap) :
    runtime.compiler.Budget.push ops compiler.budget compiler.function.controls control ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = compiler.budget ∧
      out.2.2.val = compiler.function.controls.val ++ [control] ⦄ := by
  apply budget_push_available ops _ available _ _ _ (budget.capacities sourceBound).1
  have bound := budget.maps
  omega

/-- Physical frames are bounded by allocated control maps, including dormant
scopes; the same independent request bound therefore pays for their append. -/
theorem SourceControlBudget.frame_push_available {A : Type} (ops : runtime.platform.Alloc A)
    {compiler : runtime.compiler.FunctionCompiler A} {position : Nat}
    (budget : SourceControlBudget compiler position)
    (sourceBound : position ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (available : Platform.AllocationAvailable ops (position + 2))
    (frame : runtime.compiler.Frame) :
    runtime.compiler.Budget.push ops compiler.budget compiler.frames frame ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = compiler.budget ∧ out.2.2.val = compiler.frames.val ++ [frame] ⦄ := by
  apply budget_push_available ops _ available _ _ _ (budget.capacities sourceBound).2
  have maps := budget.maps
  have frames := budget.frames
  omega

end Exec.Code
