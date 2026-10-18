import Exec.Code.Local.Capacity.GrowthTactic
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem compiler_simd_growth {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (opcode : U16) (a : U32) (bits : U128)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state opcode a bits = .ok (status, after)) :
    after.function.code.val.length ≤ before.function.code.val.length + 1 := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op at accepted
  repeat' growth_step accepted using ops, law



end Exec.Code
