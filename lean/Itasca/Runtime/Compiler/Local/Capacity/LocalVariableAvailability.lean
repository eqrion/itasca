import Itasca.Runtime.Compiler.Local.Capacity.FinishBudgetAvailability
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

set_option maxRecDepth 4096 in
theorem lower_local_get_live_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (demand : CallbackDemand compiler state bound)
    (before : List valtype) (index : U32) (ty : Itasca.types.ValueType)
    (layout : CompilerLayout compiler before) (reachable : compiler.reachable = true)
    (found : compiler.function.locals.val[index.val]? = some ty)
 :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 32#u16 index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
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
  erw [typeEq, copy_observe_eq ops compiler state ty compiler.height localSlot different]
  exact finish_op_available_effect ops bound available compiler state demand _

set_option maxRecDepth 4096 in
theorem lower_local_write_live_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (demand : CallbackDemand compiler state bound)
    (before : List valtype) (index : U32) (ty : Itasca.types.ValueType) (tee : Bool)
    (layout : CompilerLayout compiler (before ++ [Itasca.Translate.valueType ty]))
    (reachable : compiler.reachable = true)
    (found : compiler.function.locals.val[index.val]? = some ty)
 :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (if tee then 34#u16 else 33#u16) index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
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
  erw [copyEq]
  exact finish_op_available_effect ops bound available compiler state demand _

/-- Local accesses in unreachable code only rebuild the observed stack;
valid live accesses use the checked local and operand coordinates above. -/
theorem compiler_local_variable_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (before : List valtype)
    (index : U32) (ty : Itasca.types.ValueType) (write tee : Bool)
    (layout : compiler.reachable = true → CompilerLayout compiler
      (if write then before ++ [Itasca.Translate.valueType ty] else before))
    (found : compiler.reachable = true → compiler.function.locals.val[index.val]? = some ty) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (if write then (if tee then 34#u16 else 33#u16) else 32#u16) index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · cases write
    · exact lower_local_get_live_available ops bound available compiler state demand before index ty
        (layout live) live (found live)
    · exact lower_local_write_live_available ops bound available compiler state demand before index ty tee
        (layout live) live (found live)
  · unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Code
