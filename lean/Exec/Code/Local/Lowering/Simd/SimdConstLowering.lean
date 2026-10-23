import Exec.Code.Local.Lowering.Simd.SimdLoweringSuccess
set_option maxRecDepth 4096
namespace Exec.Code
open Aeneas Aeneas.Std Aeneas.Std.Result Itasca.ResultFacts

theorem simd_const_lowering_allocation_success {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (a : U32) (bits : U128)
    (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state 524#u16 a bits = .ok (.Ok (),after)) :
    ∃ entry budget values,
      runtime.compiler.bounded_index (alloc.vec.Vec.len before.function.v128_pool) = .ok (.Ok entry) ∧
      runtime.compiler.Budget.push ops before.budget before.function.v128_pool bits = .ok (.Ok (),budget,values) ∧
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        {before with budget,function := {before.function with v128_pool := values}} state
        (.ConstV128 before.height entry) = .ok (.Ok (),after) := by
  unfold runtime.compiler.simd.FunctionCompiler.simd_op at accepted
  simp only [↓reduceIte] at accepted
  obtain ⟨indexResult,indexEq,rest⟩ := bind_ok_inv _ _ _ accepted
  cases indexResult with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok entry =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
    obtain ⟨⟨pushed,budget,values⟩,pushEq,rest⟩ := bind_ok_inv _ _ _ rest
    cases pushed with
    | Err error => simp [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unitValue =>
      cases unitValue
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
      exact ⟨entry,budget,values,indexEq,pushEq,rest⟩

end Exec.Code
