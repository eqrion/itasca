import Exec.Code.Local.Lowering.Simd.SimdLowering
set_option maxRecDepth 4096
namespace Exec.Code
open Aeneas Aeneas.Std Aeneas.Std.Result Itasca.ResultFacts

theorem simd_lowering_allocation_success {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode reduced : U16) (sub a operand : U32) (bits : U128) (totalCount operandCount : Usize)
    (reducedEq : (opcode - 512#u16) = Result.ok reduced)
    (subEq : sub = UScalar.cast .U32 reduced)
    (added : Usize.checked_add (alloc.vec.Vec.len before.before)
      (if simdStores sub then 0#usize else 1#usize) = some totalCount)
    (subtracted : Usize.checked_sub totalCount (alloc.vec.Vec.len state.vals) = some operandCount)
    (operandEq : runtime.compiler.FunctionCompiler.operand ops before operandCount = .ok (.Ok operand))
    (accepted : simdLowering ops before state opcode a bits = .ok (.Ok (),after)) :
    ∃ entry budget immediates instruction,
      runtime.compiler.bounded_index (alloc.vec.Vec.len before.function.simd) = .ok (.Ok entry) ∧
      runtime.compiler.Budget.push ops before.budget before.function.simd (simdImmediate sub a bits) = .ok (.Ok (),budget,immediates) ∧
      runtime.bytecode.Instr.make_simd sub operand operand entry = .ok (some instruction) ∧
      runtime.compiler.lower.FunctionCompiler.finish_op ops
        {before with budget,function := {before.function with simd := immediates}} state instruction = .ok (.Ok (),after) := by
  unfold simdLowering at accepted
  simp only [reducedEq,lift,bind_ok,←subEq,simd_stores_eq,simd_outputs_eq,added,subtracted,operandEq,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch] at accepted
  obtain ⟨indexResult,indexEq,rest⟩ := bind_ok_inv _ _ _ accepted
  cases indexResult with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok entry =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,simd_lane_eq] at rest
    obtain ⟨⟨pushed,budget,immediates⟩,pushEq,rest⟩ := bind_ok_inv _ _ _ rest
    cases pushed with
    | Err error => simp [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unitValue =>
      cases unitValue
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
      obtain ⟨constructed,makeEq,rest⟩ := bind_ok_inv _ _ _ rest
      cases constructed with
      | none => simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | some instruction =>
        simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
        exact ⟨entry,budget,immediates,instruction,indexEq,pushEq,makeEq,rest⟩

end Exec.Code
namespace Exec.Code
open Aeneas Aeneas.Std Aeneas.Std.Result Itasca.ResultFacts

theorem simd_lowering_emission {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode reduced : U16) (sub a operand : U32) (bits : U128) (totalCount operandCount : Usize)
    (reducedEq : (opcode - 512#u16) = Result.ok reduced)
    (subEq : sub = UScalar.cast .U32 reduced)
    (added : Usize.checked_add (alloc.vec.Vec.len before.before)
      (if simdStores sub then 0#usize else 1#usize) = some totalCount)
    (subtracted : Usize.checked_sub totalCount (alloc.vec.Vec.len state.vals) = some operandCount)
    (operandEq : runtime.compiler.FunctionCompiler.operand ops before operandCount = .ok (.Ok operand))
    (accepted : simdLowering ops before state opcode a bits = .ok (.Ok (),after)) :
    ∃ entry instruction,
      runtime.bytecode.Instr.make_simd sub operand operand entry = .ok (some instruction) ∧
      entry.val = before.function.simd.val.length ∧
      after.function.simd.val = before.function.simd.val ++ [simdImmediate sub a bits] ∧
      after.function.code.val = before.function.code.val ++ [instruction] ∧
      after.function.source_offsets.val.map (fun word => word.val) =
        before.function.source_offsets.val.map (fun word => word.val) ++
          [before.function.body_start.val + before.next_source.val] := by
  obtain ⟨entry,budget,immediates,instruction,indexEq,pushed,constructed,finished⟩ :=
    simd_lowering_allocation_success ops before after state opcode reduced sub a operand bits totalCount operandCount
      reducedEq subEq added subtracted operandEq accepted
  have index := bounded_index (alloc.vec.Vec.len before.function.simd)
  rw [indexEq,WP.spec_ok] at index
  have indexVal : entry.val = before.function.simd.val.length := by simpa using index entry rfl
  have appended := (budget_push_success ops law before.budget budget before.function.simd immediates
    (simdImmediate sub a bits) pushed).2
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
    obtain ⟨budget1,code,sources,middleEq,codeEq,sourcesEq⟩ := compiler_emit_success ops law _ middle instruction emitEq
    refine ⟨entry,instruction,constructed,indexVal,?_,?_,?_⟩
    · rw [frame,middleEq]; exact appended
    · rw [frame,middleEq]; exact codeEq
    · rw [frame,middleEq]; exact sourcesEq

end Exec.Code
