import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.CodeGrowth.CompilerCodeMonotoneLiteral
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdDispatch
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables

/-!
Sections, each formerly its own module: CompilerSimdMetadata, CompilerCodeMonotoneSimd, CompilerTableScratchSimd.
-/

/-! ## CompilerSimdMetadata -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
theorem compiler_simd_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  rcases (runtime.compiler.simd.FunctionCompiler.simd_op.inv ops before after state opcode a bits status accepted).execution with
    ⟨error, same, frame⟩ | ⟨staged, instruction, allocated, finished⟩
  · rw [frame]
    exact ⟨rfl, Nat.le_refl _⟩
  · have frame := allocated.frame
    have first : CompilerOrdinaryStable before staged := by
      rw [frame]
      exact ⟨rfl, Nat.le_refl _⟩
    exact first.trans (compiler_finish_op_ordinary_result ops law staged after state instruction status finished)

end Itasca.Runtime.Compiler

end

/-! ## CompilerCodeMonotoneSimd -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

theorem compiler_simd_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a : U32) (bits : U128)
    (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits = .ok (.Ok (),after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  obtain ⟨staged, instruction, allocated, finished⟩ :=
    (runtime.compiler.simd.FunctionCompiler.simd_op.inv ops before after state opcode a bits (.Ok ()) accepted).execution.success
  have frame := allocated.frame
  have result := compiler_finish_op_code_mono ops law staged after state instruction (.Ok ()) finished
  rw [frame] at result
  exact result

theorem compiler_lower_simd_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases reachable : before.reachable = true
  · rw [lower_simd_dispatch ops before state opcode a b bits reachable lower upper] at accepted
    exact compiler_simd_code_mono ops law before after state opcode a bits accepted
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reachable)] at accepted
    exact compiler_observe_code_mono ops law before after state (.Ok ()) accepted
end Itasca.Runtime.Compiler

end

/-! ## CompilerTableScratchSimd -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

theorem compiler_simd_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a : U32) (bits : U128)
    (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits = .ok (.Ok (),after)) :
    after.table_depths = before.table_depths := by
  obtain ⟨staged, instruction, allocated, finished⟩ :=
    (runtime.compiler.simd.FunctionCompiler.simd_op.inv ops before after state opcode a bits (.Ok ()) accepted).execution.success
  have frame := allocated.frame
  have result := compiler_finish_op_depths ops law staged after state instruction (.Ok ()) finished
  rw [frame] at result
  exact result

theorem compiler_lower_simd_depths {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    after.table_depths = before.table_depths := by
  by_cases reachable : before.reachable = true
  · rw [lower_simd_dispatch ops before state opcode a b bits reachable lower upper] at accepted
    exact compiler_simd_depths ops law before after state opcode a bits accepted
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reachable)] at accepted
    exact compiler_observe_depths ops law before after state (.Ok ()) accepted
end Itasca.Runtime.Compiler

end
