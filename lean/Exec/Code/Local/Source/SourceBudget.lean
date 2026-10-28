import Exec.Code.Local.Relations.Common.EntryTypedSteps
import Exec.Code.Local.Capacity.EmissionGrowth
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- The source byte budget pays for at most three emitted instructions per byte.
Branch-table depths are charged when their complete instruction is lowered. -/
def SourceCodeBudget {A : Type} (compiler : runtime.compiler.FunctionCompiler A) (position : Nat) : Prop :=
  compiler.function.code.val.length ≤ 3 * position

theorem SourceCodeBudget.initial {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    (empty : compiler.function.code.val = []) : SourceCodeBudget compiler 0 := by
  simp [SourceCodeBudget, empty]

/-- One ordinary or structured opcode pays for up to three emitted instructions. -/
theorem SourceCodeBudget.advance {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {start finish : Nat} (budget : SourceCodeBudget before start)
    (growth : after.function.code.val.length ≤ before.function.code.val.length + 3)
    (consumed : start < finish) : SourceCodeBudget after finish := by
  unfold SourceCodeBudget at *
  omega

/-- The table count and default-depth bytes cover the table instruction itself;
each target depth pays for its at-most-two-instruction branch stub. -/
theorem SourceCodeBudget.table {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {start finish targets : Nat} (budget : SourceCodeBudget before start)
    (growth : after.function.code.val.length ≤ before.function.code.val.length + 1 + 2 * targets)
    (consumed : start + targets + 1 ≤ finish) : SourceCodeBudget after finish := by
  unfold SourceCodeBudget at *
  omega

/-- The existing module byte cap leaves room for all emitted instruction PCs. -/
theorem SourceCodeBudget.fetch_bound {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {position : Nat} (budget : SourceCodeBudget compiler position)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) :
    compiler.function.code.val.length < U32.max := by
  unfold SourceCodeBudget at budget
  norm_num [limits.MAX_MODULE_BYTES, U32.max_eq] at *
  omega

/-- The same source budget discharges the extracted vector append capacity. -/
theorem SourceCodeBudget.code_capacity {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {position : Nat} (budget : SourceCodeBudget compiler position)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) :
    compiler.function.code.val.length < Usize.max := by
  have fetchBound := budget.fetch_bound sourceBound
  have wordBound : U32.max ≤ Usize.max := by scalar_tac
  omega
end Itasca.Runtime.Code
