import Itasca.Runtime.Compiler.Local.Capacity.EmitAvailability
import Itasca.Runtime.Compiler.Local.Capacity.ChargeAvailability

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Successful available emission retains every compiler field except the two
appended vectors and the single instruction counter. This exact frame supports
aggregate resource accounting across complete function bodies. -/
theorem compiler_emit_available_frame {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (pcBound : compiler.function.code.length ≤ U32.max)
    (codeFits : compiler.function.code.length < Usize.max)
    (sourcesFit : compiler.function.source_offsets.length < Usize.max)
    (codeRequest : compiler.function.code.length+1 ≤ bound)
    (sourceRequest : compiler.function.source_offsets.length+1 ≤ bound)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max)
    (room : compiler.budget.instructions.val < compiler.budget.limits.max_instructions.val) :
    runtime.compiler.FunctionCompiler.emit ops compiler instruction ⦃ out =>
      out.1 = .Ok () ∧ ∃ used code sources,
        out.2 = {compiler with
          budget := {compiler.budget with instructions := used}
          function := {compiler.function with code,source_offsets := sources}} ∧
        used.val = compiler.budget.instructions.val+1 ∧
        code.val = compiler.function.code.val ++ [instruction] ∧
        sources.val.map (fun value => value.val) = compiler.function.source_offsets.val.map (fun value => value.val) ++
          [compiler.function.body_start.val+compiler.next_source.val] ⦄ := by
  unfold runtime.compiler.FunctionCompiler.emit
  step with compiler_pc_available ops compiler pcBound as ⟨status,first,same,pc,accepted,pcEq⟩
  subst first
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with charge_counter_available ops .instructions compiler.budget room
    as ⟨status,charged,accepted,used,same,usedEq⟩
  rw [accepted]
  subst charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available {compiler.budget with instructions := used}
    compiler.function.code instruction codeFits codeRequest
    as ⟨status,charged,code,accepted,same,appended⟩
  subst status charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step as ⟨source,sourceEq⟩
  step with budget_push_available ops bound available {compiler.budget with instructions := used}
    compiler.function.source_offsets source sourcesFit sourceRequest
    as ⟨status,charged,sources,accepted,same,recorded⟩
  refine ⟨accepted,used,code,sources,?_,usedEq,appended,?_⟩
  · rw [same]
  · simp [recorded,sourceEq]

end Itasca.Runtime.Compiler
