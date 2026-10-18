import Exec.Code.Local.Lowering.Float.FloatLowering
import Exec.Code.Local.Lowering.Common.LoweringEqz
namespace Exec.Code
open Aeneas Aeneas.Std Abs.Float

/-- Scalar numeric operands occupy one word each. Unary operations reuse
the same source slot in both scalar operands. -/
theorem float_operands {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (front : List valtype) (op : Instruction)
    (layout : CompilerLayout compiler (front ++ List.replicate op.arity (valtype_numtype op.input))) :
    ∃ left right : U32,
      runtime.compiler.FunctionCompiler.operand ops compiler (floatDepth op) = .ok (.Ok left) ∧
      runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok right) ∧
      left.val = slots (compilerLocals compiler) + slots front ∧
      right.val = left.val + (op.arity - 1) := by
  rcases op.arity_valid with unary | binary
  · have one : floatDepth op = 1#usize := by simp [floatDepth,unary]
    have shape : List.replicate op.arity (valtype_numtype op.input) = [valtype_numtype op.input] := by simp [unary]
    rw [shape] at layout
    obtain ⟨operand,read,position⟩ := last_operand ops compiler front (valtype_numtype op.input) layout
    exact ⟨operand,operand,one ▸ read,read,position,by simp [unary]⟩
  · have two : floatDepth op = 2#usize := by simp [floatDepth,binary]
    have shape : List.replicate op.arity (valtype_numtype op.input) = [valtype_numtype op.input,valtype_numtype op.input] := by simp [binary]
    rw [shape] at layout
    obtain ⟨r,readLeft,left,rfl,leftPosition⟩ := WP.spec_imp_exists
      (compiler_operand ops compiler _ layout 2#usize (by decide) (by simp))
    obtain ⟨r,readRight,right,rfl,rightPosition⟩ := WP.spec_imp_exists
      (compiler_operand ops compiler _ layout 1#usize (by decide) (by simp))
    have leftSlot : left.val = slots (compilerLocals compiler) + slots front := by
      simpa [offset,List.take_append] using leftPosition
    have rightSlot : right.val = left.val + (op.arity - 1) := by
      have take : front.take (front.length+1) = front := List.take_of_length_le (by omega)
      rw [leftSlot]
      have scalarWidth : width (valtype_numtype op.input) = 1 := by cases op.input <;> rfl
      simpa [offset,List.take_append,slots_append,slots,scalarWidth,take,Nat.add_assoc,binary] using rightPosition
    exact ⟨left,right,two ▸ readLeft,readRight,leftSlot,rightSlot⟩

@[step] theorem compiler_float_lowered {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.types.ValueType)
    (front : List valtype) (op : Instruction)
    (layout : CompilerLayout compiler (front ++ List.replicate op.arity (valtype_numtype op.input)))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [valtype_numtype op.output])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () → ∃ left right : U32,
        left.val = slots (compilerLocals compiler) + slots front ∧
        right.val = left.val + (op.arity - 1) ∧
        Lowered compiler out.2 (floatInstruction op left left right) (front ++ [valtype_numtype op.output]) ⦄ := by
  obtain ⟨left, right, hl, hr, leftPosition, rightPosition⟩ := float_operands ops compiler front op layout
  rw [lower_float_eq ops compiler state op left right reachable hl hr]
  step with finish_op ops law compiler state types (floatInstruction op left left right) _ layout concrete
    codeFits sourceFits coordinateFits as ⟨out, lowered, success⟩
  exact ⟨left, right, leftPosition, rightPosition, by simpa only [typed] using lowered success⟩
end Exec.Code
