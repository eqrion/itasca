import Exec.Code.Local.Callbacks.Table.CompilerTableTactic
import Exec.Code.Local.Lowering.Simd.SimdDispatch
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem compiler_simd_preserved_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a : U32) (bits : U128)
    (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits = .ok (.Ok (),after)) :
    after.function.indirect.val = before.function.indirect.val ∧
      after.function.jump_tables.val = before.function.jump_tables.val := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op at accepted
  repeat' table_preservation_step accepted using ops, law

theorem compiler_lower_simd_preserved_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    after.function.indirect.val = before.function.indirect.val ∧
      after.function.jump_tables.val = before.function.jump_tables.val := by
  by_cases reachable : before.reachable = true
  · rw [lower_simd_dispatch ops before state opcode a b bits reachable lower upper] at accepted
    exact compiler_simd_preserved_tables ops law before after state opcode a bits accepted
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reachable] at accepted
    have tables := compiler_observe_tables ops law before after state (.Ok ()) accepted
    exact ⟨congrArg CompilerTables.indirect tables,congrArg CompilerTables.jumpTables tables⟩
end Itasca.Runtime.Code
