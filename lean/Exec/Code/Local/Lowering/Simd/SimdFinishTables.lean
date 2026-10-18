import Exec.Code.Local.Lowering.Simd.SimdConstLowering
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

theorem compiler_finish_simd_tables {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.lower.FunctionCompiler.finish_op ops before state instruction = .ok (.Ok (),after)) :
    after.function.simd = before.function.simd ∧ after.function.v128_pool = before.function.v128_pool := by
  unfold runtime.compiler.lower.FunctionCompiler.finish_op at accepted
  obtain ⟨⟨result,middle⟩,emitted,rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unitValue =>
    cases unitValue
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
    have frame := compiler_observe_frame ops law middle state
    rw [rest,WP.spec_ok] at frame
    change ObserveFrame middle after at frame
    obtain ⟨budget,code,sources,middleEq,_,_⟩ := compiler_emit_success ops law before middle instruction emitted
    rw [frame,middleEq]
    exact ⟨rfl,rfl⟩
end Exec.Code
