import Itasca.Runtime.Compiler.Local.Relations.Select.SelectLowering
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal

/-!
Operand correspondence and lowering for untyped select.

Main declarations: `select_operands` and `compiler_select_lowered`. A direct consumer is `Compiler.Local.Relations.Operations.CoreBasicEmissions`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem select_operands {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (front : List valtype) (ty : valtype)
    (layout : CompilerLayout compiler (front ++ [ty, ty, .I32])) :
    ∃ left right condition : U32,
      runtime.compiler.FunctionCompiler.operand ops compiler 3#usize = .ok (.Ok left) ∧
      runtime.compiler.FunctionCompiler.operand ops compiler 2#usize = .ok (.Ok right) ∧
      runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok condition) ∧
      left.val = slots (compilerLocals compiler) + slots front ∧
      right.val = left.val + width ty ∧ condition.val = right.val + width ty := by
  obtain ⟨_, readLeft, left, rfl, leftPosition⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout 3#usize (by decide) (by simp))
  obtain ⟨_, readRight, right, rfl, rightPosition⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout 2#usize (by decide) (by simp))
  obtain ⟨_, readCondition, condition, rfl, conditionPosition⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout 1#usize (by decide) (by simp))
  have leftSlot : left.val = slots (compilerLocals compiler) + slots front := by
    simpa [offset, List.take_append] using leftPosition
  have rightSlot : right.val = left.val + width ty := by
    have take : front.take (front.length + 1) = front := List.take_of_length_le (by omega)
    rw [leftSlot]
    simpa [offset, List.take_append, slots_append, slots, take, Nat.add_assoc] using rightPosition
  have conditionSlot : condition.val = right.val + width ty := by
    have take : front.take (front.length + 2) = front := List.take_of_length_le (by omega)
    rw [rightSlot, leftSlot]
    simpa [offset, List.take_append, slots_append, slots, take, Nat.add_assoc] using conditionPosition
  exact ⟨left, right, condition, readLeft, readRight, readCondition, leftSlot, rightSlot, conditionSlot⟩

@[step] theorem compiler_select_lowered {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (front : List valtype) (ty : valtype)
    (layout : CompilerLayout compiler (front ++ [ty, ty, .I32]))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [ty])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 27#u16 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () → ∃ left right condition : U32,
        left.val = slots (compilerLocals compiler) + slots front ∧
        right.val = left.val + width ty ∧ condition.val = right.val + width ty ∧
        Lowered compiler out.2 (selectInstruction (decide (width ty = 2)) left right condition)
          (front ++ [ty]) ⦄ := by
  obtain ⟨left, right, condition, hl, hr, hc, lp, rp, cp⟩ := select_operands ops compiler front ty layout
  obtain ⟨difference, subtract, differenceVal⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := right) (y := left) (by omega))
  have dw : difference.val = width ty := by omega
  have wide : (difference = 2#u32) ↔ width ty = 2 := by
    constructor
    · intro h
      have v : difference.val = 2 := by simpa using congrArg UScalar.val h
      omega
    · intro h; apply UScalar.eq_of_val_eq; simpa [h] using dw
  have dispatch := lower_select_eq ops compiler state left right condition difference false reachable hl hr hc subtract
  simp only [Bool.false_eq_true, ite_false] at dispatch
  rw [dispatch]
  simp only [wide]
  step with finish_op ops law compiler state types
    (selectInstruction (decide (width ty = 2)) left right condition) _ layout concrete
    codeFits sourceFits coordinateFits as ⟨out, lowered, success⟩
  exact ⟨left, right, condition, lp, rp, cp, by simpa only [typed] using lowered success⟩
end Itasca.Runtime.Compiler
