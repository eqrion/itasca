import Itasca.Runtime.Code.Local.Lowering.Simd.SimdLoweringSuccess
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Aeneas.Std.Result Itasca.ResultFacts
set_option maxRecDepth 4096

theorem simd_lowering_operand_counts {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (opcode reduced : U16) (sub a : U32) (bits : U128)
    (reducedEq : (opcode - 512#u16) = Result.ok reduced)
    (subEq : sub = UScalar.cast .U32 reduced)
    (accepted : simdLowering ops before state opcode a bits = .ok (.Ok (),after)) :
    ∃ totalCount operandCount operand,
      Usize.checked_add (alloc.vec.Vec.len before.before)
        (if simdStores sub then 0#usize else 1#usize) = some totalCount ∧
      Usize.checked_sub totalCount (alloc.vec.Vec.len state.vals) = some operandCount ∧
      runtime.compiler.FunctionCompiler.operand ops before operandCount = .ok (.Ok operand) := by
  unfold simdLowering at accepted
  simp only [reducedEq,lift,bind_ok,←subEq,simd_stores_eq,simd_outputs_eq] at accepted
  cases added : Usize.checked_add (alloc.vec.Vec.len before.before)
      (if simdStores sub then 0#usize else 1#usize) with
  | none => simp [added,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
  | some totalCount =>
    simp only [added,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at accepted
    cases subtracted : Usize.checked_sub totalCount (alloc.vec.Vec.len state.vals) with
    | none => simp [subtracted,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
    | some operandCount =>
      simp only [subtracted,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at accepted
      obtain ⟨operandResult,read,rest⟩ := bind_ok_inv _ _ _ accepted
      cases operandResult with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok operand => exact ⟨totalCount,operandCount,operand,rfl,subtracted,read⟩

theorem simd_count_position {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (front input output : List valtype) (sub operand : U32) (totalCount operandCount : Usize)
    (layout : CompilerLayout before (front ++ input))
    (postLength : state.vals.val.length = (front ++ output).length)
    (outputCount : output.length = if simdStores sub then 0 else 1)
    (positive : 0 < input.length)
    (added : Usize.checked_add (alloc.vec.Vec.len before.before)
      (if simdStores sub then 0#usize else 1#usize) = some totalCount)
    (subtracted : Usize.checked_sub totalCount (alloc.vec.Vec.len state.vals) = some operandCount)
    (read : runtime.compiler.FunctionCompiler.operand ops before operandCount = .ok (.Ok operand)) :
    operandCount.val = input.length ∧ operand.val = slots (compilerLocals before) + slots front := by
  have beforeLength := layout.operands_length
  have addSpec := Usize.checked_add_bv_spec (alloc.vec.Vec.len before.before)
    (if simdStores sub then 0#usize else 1#usize)
  have subSpec := Usize.checked_sub_bv_spec totalCount (alloc.vec.Vec.len state.vals)
  simp only [added] at addSpec
  simp only [subtracted] at subSpec
  have count : operandCount.val = input.length := by
    simp only [List.length_append] at beforeLength postLength
    split at outputCount
    · rename_i store
      simp only [store,↓reduceIte] at addSpec
      scalar_tac
    · rename_i store
      simp only [store,↓reduceIte] at addSpec
      scalar_tac
  obtain ⟨r,executed,first,rfl,position⟩ := WP.spec_imp_exists
    (compiler_operand ops before _ layout operandCount (by omega) (by simp [count]))
  have same : first = operand := by simpa only [read,Result.ok.injEq,core.result.Result.Ok.injEq] using executed.symm
  subst first
  exact ⟨count,by simpa [offset,List.length_append,count] using position⟩
end Itasca.Runtime.Code
