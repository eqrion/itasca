import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerCodeMonotoneTactic
import Itasca.Runtime.Code.Local.Lowering.Simd.SimdDispatch
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem compiler_simd_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a : U32) (bits : U128)
    (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits = .ok (.Ok (),after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op at accepted
  repeat' code_mono_step accepted using ops, law

theorem compiler_lower_simd_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a b : U32) (bits : U128)
    (lower : 512 ≤ opcode.val) (upper : opcode.val < 768)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state opcode a b bits = .ok (.Ok (),after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  by_cases reachable : before.reachable = true
  · rw [lower_simd_dispatch ops before state opcode a b bits reachable lower upper] at accepted
    exact compiler_simd_code_mono ops law before after state opcode a bits accepted
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reachable] at accepted
    exact compiler_observe_code_mono ops law before after state (.Ok ()) accepted
end Itasca.Runtime.Code
