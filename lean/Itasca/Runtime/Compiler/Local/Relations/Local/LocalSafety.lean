import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericSafety
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Copy
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem compiler_copy_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (dst src count : U32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.copy ops compiler dst src count ⦃ _ => True ⦄ := by
  by_cases empty : count = 0#u32 ∨ src = dst
  · rw [compiler_copy_elided ops compiler dst src count empty]
    simp [WP.spec_ok]
  · apply WP.spec_mono (compiler_copy ops law compiler dst src count
      (by tauto) (by tauto) codeFits sourceFits coordinateFits)
    simp

set_option maxRecDepth 4096 in
@[step] theorem compiler_local_get_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (index : U32)
    (offsetBound : index.val < compiler.local_offsets.val.length)
    (localBound : index.val < compiler.function.locals.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 32#u16 index 0#u32 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state 32#u16 index 0#u32 0#u128 = (do
        let i ← lift (UScalar.cast .Usize index)
        let src ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) compiler.local_offsets i
        let j ← lift (UScalar.cast .Usize index)
        let rawType ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Itasca.types.ValueType) compiler.function.locals j
        let count ← runtime.value.width rawType
        let (result, changed) ← runtime.compiler.FunctionCompiler.copy ops compiler compiler.height src count
        let branch ← core.result.Result.Insts.CoreOpsTry.branch result
        match branch with
        | .Continue _ => runtime.compiler.FunctionCompiler.observe ops changed state
        | .Break residual =>
          let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
            (core.convert.FromSame Itasca.error.VisitError) residual
          Result.ok (error, changed)) := by
      unfold runtime.compiler.lower.FunctionCompiler.op
      rw [if_pos live]
      rfl
    rw [run]
    step as ⟨offsetIndex, offsetIndexValue⟩
    step as ⟨src, srcValue⟩
    step as ⟨localIndex, localIndexValue⟩
    step as ⟨ty, tyValue⟩
    step with compiler_width ty as ⟨count, countValue⟩
    step with compiler_copy_total ops law compiler compiler.height src count
      codeFits sourceFits coordinateFits as ⟨answer, nextCompiler⟩
    cases answer with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      exact compiler_observe_stack ops law nextCompiler state
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    exact compiler_observe_stack ops law compiler state

set_option maxRecDepth 4096 in
@[step] theorem compiler_local_write_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (index : U32) (tee : Bool)
    (offsetBound : index.val < compiler.local_offsets.val.length)
    (localBound : index.val < compiler.function.locals.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (if tee then 34#u16 else 33#u16) index 0#u32 0#u128 ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  by_cases live : compiler.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state (if tee then 34#u16 else 33#u16) index 0#u32 0#u128 = (do
        let i ← lift (UScalar.cast .Usize index)
        let dst ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) compiler.local_offsets i
        let result ← runtime.compiler.FunctionCompiler.operand ops compiler 1#usize
        let branch ← core.result.Result.Insts.CoreOpsTry.branch result
        match branch with
        | .Continue src =>
          let j ← lift (UScalar.cast .Usize index)
          let rawType ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Itasca.types.ValueType) compiler.function.locals j
          let count ← runtime.value.width rawType
          let (result, changed) ← runtime.compiler.FunctionCompiler.copy ops compiler dst src count
          let branch ← core.result.Result.Insts.CoreOpsTry.branch result
          match branch with
          | .Continue _ => runtime.compiler.FunctionCompiler.observe ops changed state
          | .Break residual =>
            let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
              (core.convert.FromSame Itasca.error.VisitError) residual
            Result.ok (error, changed)
        | .Break residual =>
          let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
            (core.convert.FromSame Itasca.error.VisitError) residual
          Result.ok (error, compiler)) := by
      cases tee <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> rw [if_pos live] <;> rfl
    rw [run]
    step as ⟨offsetIndex, offsetIndexValue⟩
    step as ⟨dst, dstValue⟩
    step with compiler_operand_total ops compiler 1#usize as ⟨operandResult, _⟩
    cases operandResult with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok src =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨localIndex, localIndexValue⟩
      step as ⟨ty, tyValue⟩
      step with compiler_width ty as ⟨count, countValue⟩
      step with compiler_copy_total ops law compiler dst src count
        codeFits sourceFits coordinateFits as ⟨answer, nextCompiler⟩
      cases answer with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok unit =>
        cases unit
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        exact compiler_observe_stack ops law nextCompiler state
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    exact compiler_observe_stack ops law compiler state

end Itasca.Runtime.Compiler
