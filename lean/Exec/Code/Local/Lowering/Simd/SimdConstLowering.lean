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

theorem simd_const_lowering_emission {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (a : U32) (bits : U128)
    (accepted : runtime.compiler.simd.FunctionCompiler.simd_op ops before state 524#u16 a bits = .ok (.Ok (),after)) :
    ∃ entry,
      entry.val = before.function.v128_pool.val.length ∧
      after.function.v128_pool.val = before.function.v128_pool.val ++ [bits] ∧
      after.function.code.val = before.function.code.val ++ [.ConstV128 before.height entry] ∧
      after.function.source_offsets.val.map (fun word => word.val) =
        before.function.source_offsets.val.map (fun word => word.val) ++
          [before.function.body_start.val + before.next_source.val] := by
  obtain ⟨entry,budget,values,indexEq,pushed,finished⟩ :=
    simd_const_lowering_allocation_success ops before after state a bits accepted
  have index := bounded_index (alloc.vec.Vec.len before.function.v128_pool)
  rw [indexEq,WP.spec_ok] at index
  have indexVal : entry.val = before.function.v128_pool.val.length := by simpa using index entry rfl
  have appended := (budget_push_success ops law before.budget budget before.function.v128_pool values bits pushed).2
  unfold runtime.compiler.lower.FunctionCompiler.finish_op at finished
  obtain ⟨⟨emitted,middle⟩,emitEq,rest⟩ := bind_ok_inv _ _ _ finished
  cases emitted with
  | Err error => simp [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unitValue =>
    cases unitValue
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
    have frame := compiler_observe_frame ops law middle state
    rw [rest,WP.spec_ok] at frame
    change ObserveFrame middle after at frame
    obtain ⟨budget1,code,sources,middleEq,codeEq,sourcesEq⟩ := compiler_emit_success ops law _ middle (.ConstV128 before.height entry) emitEq
    refine ⟨entry,indexVal,?_,?_,?_⟩
    · rw [frame,middleEq]; exact appended
    · rw [frame,middleEq]; exact codeEq
    · rw [frame,middleEq]; exact sourcesEq

end Exec.Code
