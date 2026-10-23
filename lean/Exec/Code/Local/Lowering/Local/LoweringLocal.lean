import Exec.Code.Local.Lowering.Common.Lowering
import Exec.Code.Local.Lowering.Common.Copy
namespace Exec.Code
open Aeneas Aeneas.Std

theorem CompilerLayout.local_slot {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {stack : List valtype} (layout : CompilerLayout compiler stack)
    (index : U32) (ty : Itasca.types.ValueType)
    (found : compiler.function.locals.val[index.val]? = some ty) :
    ∃ slot : U32, compiler.local_offsets.val[index.val]? = some slot ∧
      slot.val = offset (compilerLocals compiler) index.val := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have offsetsBound : index.val < compiler.local_offsets.val.length := by rw [layout.locals_length]; exact bound
  refine ⟨compiler.local_offsets.val[index.val], List.getElem?_eq_getElem offsetsBound, ?_⟩
  have atIndex := congrArg (fun values => values[index.val]?) layout.localOffsets
  simpa [compilerLocals, List.getElem?_eq_getElem, offsetsBound, bound] using atIndex

theorem copy_observe_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (ty : Itasca.types.ValueType) (dst src : U32) (different : src ≠ dst) :
    (do
      let count ← runtime.value.width ty
      let (result, changed) ← runtime.compiler.FunctionCompiler.copy ops compiler dst src count
      let branch ← core.result.Result.Insts.CoreOpsTry.branch result
      match branch with
      | .Continue _ => runtime.compiler.FunctionCompiler.observe ops changed state
      | .Break residual =>
        let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
          (core.convert.FromSame Itasca.error.VisitError) residual
        Result.ok (error, changed)) =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state
        (move (Itasca.Translate.valueType ty) dst src) := by
  cases ty <;> simp [runtime.value.width, runtime.compiler.FunctionCompiler.copy, different,
    runtime.compiler.lower.FunctionCompiler.finish_op, move, width, Itasca.Translate.valueType] <;>
    split <;> simp only [bind_ok] <;> first
    | rfl
    | (rename_i h; exact False.elim ((by decide : (1#u32) ≠ (2#u32)) h))
    | (rename_i h; exact False.elim ((by decide : (2#u32) ≠ (1#u32)) h))
    | (rename_i h _; exact False.elim (h rfl))
    | (rename_i _ h; exact False.elim (h rfl))


set_option maxRecDepth 4096 in
@[step] theorem lower_local_get {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (before : List valtype) (index : U32) (ty : Itasca.types.ValueType)
    (layout : CompilerLayout compiler before) (reachable : compiler.reachable = true)
    (found : compiler.function.locals.val[index.val]? = some ty)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 32#u16 index 0#u32 0#u128 ⦃ out =>
      out.1 = .Ok () → ∃ localSlot,
        localSlot.val = offset (compilerLocals compiler) index.val ∧
        Lowered compiler out.2 (move (Itasca.Translate.valueType ty) compiler.height localSlot)
          (types.map Itasca.Translate.valueType) ⦄ := by
  obtain ⟨localSlot, atSlot, slotPosition⟩ := layout.local_slot index ty found
  have sourceType : (compilerLocals compiler)[index.val]? = some (Itasca.Translate.valueType ty) := by
    simp [compilerLocals, List.getElem?_map, found]
  have different : localSlot ≠ compiler.height := by
    have smaller := layout.local_before_operand_region sourceType
    intro equal
    rw [equal] at slotPosition
    rw [← slotPosition, layout.localSlots, layout.height] at smaller
    omega
  have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state 32#u16 index 0#u32 0#u128 = (do
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
    rw [if_pos reachable]
    rfl
  rw [run]
  step as ⟨i, hi⟩
  have iVal : i.val = index.val := by scalar_tac
  have offsetsBound : i.val < compiler.local_offsets.val.length := by rw [iVal]; exact (List.getElem?_eq_some_iff.mp atSlot).1
  step as ⟨src, hsrc⟩
  have srcEq : src = localSlot := by
    simp only [iVal] at hsrc
    exact hsrc.trans (List.getElem?_eq_some_iff.mp atSlot).2
  rw [srcEq]
  step as ⟨j, hj⟩
  have jVal : j.val = index.val := by scalar_tac
  have localsBound : j.val < compiler.function.locals.val.length := by rw [jVal]; exact (List.getElem?_eq_some_iff.mp found).1
  step as ⟨rawType, htype⟩
  have typeEq : rawType = ty := by
    simp only [jVal] at htype
    exact htype.trans (List.getElem?_eq_some_iff.mp found).2
  rw [typeEq, copy_observe_eq ops compiler state ty compiler.height localSlot different]
  apply WP.spec_mono (finish_op ops law compiler state types _ before layout concrete codeFits sourceFits coordinateFits)
  intro out result success
  exact ⟨localSlot, slotPosition, result success⟩


theorem last_operand {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (front : List valtype) (ty : valtype)
    (layout : CompilerLayout compiler (front ++ [ty])) :
    ∃ operand : U32, runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok operand) ∧
      operand.val = slots (compilerLocals compiler) + slots front := by
  obtain ⟨r, call, operand, rfl, position⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout 1#usize (by decide) (by simp))
  exact ⟨operand, call, by simpa [offset, List.take_append] using position⟩

set_option maxRecDepth 4096 in
@[step] theorem lower_local_write {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (before : List valtype) (index : U32) (ty : Itasca.types.ValueType) (tee : Bool)
    (layout : CompilerLayout compiler (before ++ [Itasca.Translate.valueType ty]))
    (reachable : compiler.reachable = true)
    (found : compiler.function.locals.val[index.val]? = some ty)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (if tee then 34#u16 else 33#u16) index 0#u32 0#u128 ⦃ out =>
      out.1 = .Ok () → ∃ (localSlot operand : U32),
        localSlot.val = offset (compilerLocals compiler) index.val ∧
        operand.val = slots (compilerLocals compiler) + slots before ∧
        Lowered compiler out.2 (move (Itasca.Translate.valueType ty) localSlot operand)
          (types.map Itasca.Translate.valueType) ⦄ := by
  obtain ⟨localSlot, atSlot, slotPosition⟩ := layout.local_slot index ty found
  obtain ⟨operand, operandRead, operandPosition⟩ := last_operand ops compiler before _ layout
  have sourceType : (compilerLocals compiler)[index.val]? = some (Itasca.Translate.valueType ty) := by
    simp [compilerLocals, List.getElem?_map, found]
  have different : operand ≠ localSlot := by
    have smaller := layout.local_before_operand_region sourceType
    intro equal
    rw [← equal] at slotPosition
    rw [← slotPosition, layout.localSlots, operandPosition] at smaller
    omega
  have run : runtime.compiler.lower.FunctionCompiler.op ops compiler state (if tee then 34#u16 else 33#u16) index 0#u32 0#u128 = (do
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
    cases tee <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> rw [if_pos reachable] <;> rfl
  rw [run]
  step as ⟨i, hi⟩
  have iVal : i.val = index.val := by scalar_tac
  have offsetsBound : i.val < compiler.local_offsets.val.length := by rw [iVal]; exact (List.getElem?_eq_some_iff.mp atSlot).1
  step as ⟨dst, hdst⟩
  have dstEq : dst = localSlot := by
    simp only [iVal] at hdst
    exact hdst.trans (List.getElem?_eq_some_iff.mp atSlot).2
  rw [dstEq, operandRead]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step as ⟨j, hj⟩
  have jVal : j.val = index.val := by scalar_tac
  have localsBound : j.val < compiler.function.locals.val.length := by rw [jVal]; exact (List.getElem?_eq_some_iff.mp found).1
  step as ⟨rawType, htype⟩
  have typeEq : rawType = ty := by
    simp only [jVal] at htype
    exact htype.trans (List.getElem?_eq_some_iff.mp found).2
  rw [typeEq]
  have copyEq := copy_observe_eq ops compiler state ty localSlot operand different
  simp only [core.result.Result.Insts.CoreOpsTry.branch] at copyEq
  rw [copyEq]
  apply WP.spec_mono (finish_op ops law compiler state types _ _ layout concrete codeFits sourceFits coordinateFits)
  intro out result success
  exact ⟨localSlot, operand, slotPosition, operandPosition, result success⟩

end Exec.Code
