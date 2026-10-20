import Exec.Code.Local.Capacity.BudgetAvailability
import Exec.Code.Local.Lowering.Common.Emit

namespace Exec.Code
open Aeneas Aeneas.Std

/-- A representable bytecode PC excludes the actual instruction-index rejection. -/
theorem compiler_pc_available {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A)
    (bounded : compiler.function.code.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.pc ops compiler ⦃ out =>
      out.2 = compiler ∧ ∃ pc, out.1 = .Ok pc ∧ pc.val = compiler.function.code.length ⦄ := by
  unfold runtime.compiler.FunctionCompiler.pc
  step as ⟨maximum,maximumEq⟩
  have inside : ¬ alloc.vec.Vec.len compiler.function.code > maximum := by
    simp_all [core.num.U32.MAX,U32.rMax]
    scalar_tac
  simp only [if_neg inside]
  step as ⟨pc,pcEq⟩
  refine ⟨pc,rfl,?_⟩
  simp only [pcEq,UScalar.cast_val_eq]
  scalar_tac

/-- Actual ordinary-body emission accepts an independently bounded available
pair of reserves, PC, source coordinate, and remaining instruction budget. -/
theorem compiler_emit_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (pcBound : compiler.function.code.length ≤ U32.max)
    (codeFits : compiler.function.code.length < Usize.max)
    (sourcesFit : compiler.function.source_offsets.length < Usize.max)
    (codeRequest : compiler.function.code.length + 1 ≤ bound)
    (sourceRequest : compiler.function.source_offsets.length + 1 ≤ bound)
    (coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (room : compiler.budget.instructions.val < compiler.budget.limits.max_instructions.val) :
    runtime.compiler.FunctionCompiler.emit ops compiler instruction ⦃ out =>
      out.1 = .Ok () ∧ Emitted compiler out.2 instruction ∧
      out.2.budget.instructions.val = compiler.budget.instructions.val + 1 ∧
      out.2.budget.limits = compiler.budget.limits ⦄ := by
  unfold runtime.compiler.FunctionCompiler.emit
  step with compiler_pc_available ops compiler pcBound as ⟨status,first,same,pc,accepted,pcEq⟩
  subst first
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with charge_instruction_available ops compiler.budget room
    as ⟨status,charged,accepted,used,limits,error⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available charged compiler.function.code instruction codeFits codeRequest
    as ⟨status,afterCode,code,accepted,sameCode,appended⟩
  subst status afterCode
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step as ⟨source,sourceEq⟩
  step with budget_push_available ops bound available charged compiler.function.source_offsets source sourcesFit sourceRequest
    as ⟨status,afterSources,sources,accepted,sameSources,recorded⟩
  refine ⟨accepted,⟨afterSources,code,sources,rfl,appended,?_⟩,?_,?_⟩
  · simp [recorded,sourceEq]
  · simpa [sameSources] using used
  · simpa [sameSources] using limits

end Exec.Code
