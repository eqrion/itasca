import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericLowering
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal

/-!
Canonical integer operands occupy one word each. Unary operations reuse the same source slot in both scalar operands.

Main declarations: `numeric_operands` and `compiler_numeric_lowered`. A direct consumer is `Compiler.Local.Lowering.Integer.NumericInstructionPublication`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std SourceMachine.Numeric

/-- Canonical integer operands occupy one word each. Unary operations reuse
the same source slot in both scalar operands. -/
theorem numeric_operands {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (front : List valtype) (op : Instruction)
    (layout : CompilerLayout compiler (front ++ List.replicate op.arity (integerType op.input))) :
    ∃ left right : U32,
      runtime.compiler.FunctionCompiler.operand ops compiler (integerDepth op) = .ok (.Ok left) ∧
      runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok right) ∧
      left.val = slots (compilerLocals compiler) + slots front ∧
      right.val = left.val + (op.arity - 1) := by
  cases op with
  | binary ty operator =>
    simpa only [Instruction.arity, Instruction.input, integerDepth, List.replicate_succ,
      List.replicate_zero, ↓reduceIte, Nat.reduceSub] using binary_operands ops compiler front ty layout
  | compare ty operator =>
    simpa only [Instruction.arity, Instruction.input, integerDepth, List.replicate_succ,
      List.replicate_zero, ↓reduceIte, Nat.reduceSub] using binary_operands ops compiler front ty layout
  | unary ty operator =>
    obtain ⟨operand, read, position⟩ := last_operand ops compiler front (integerType ty) layout
    exact ⟨operand, operand, read, read, position, by simp [Instruction.arity]⟩
  | eqz ty =>
    obtain ⟨operand, read, position⟩ := last_operand ops compiler front (integerType ty) layout
    exact ⟨operand, operand, read, read, position, by simp [Instruction.arity]⟩
  | conversion operator =>
    obtain ⟨operand, read, position⟩ := last_operand ops compiler front (integerType operator.input) layout
    exact ⟨operand, operand, read, read, position, by simp [Instruction.arity]⟩

@[step] theorem compiler_numeric_lowered {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (front : List valtype) (op : Instruction)
    (layout : CompilerLayout compiler (front ++ List.replicate op.arity (integerType op.input)))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translate.valueType = front ++ [integerType op.output])
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (integerOpcode op) 0#u32 0#u32 0#u128
      ⦃ out => out.1 = .Ok () → ∃ left right : U32,
        left.val = slots (compilerLocals compiler) + slots front ∧
        right.val = left.val + (op.arity - 1) ∧
        Lowered compiler out.2 (integerInstruction op left left right) (front ++ [integerType op.output]) ⦄ := by
  obtain ⟨left, right, hl, hr, leftPosition, rightPosition⟩ := numeric_operands ops compiler front op layout
  rw [lower_numeric_eq ops compiler state op left right reachable hl hr]
  step with finish_op ops law compiler state types (integerInstruction op left left right) _ layout concrete
    codeFits sourceFits coordinateFits as ⟨out, lowered, success⟩
  exact ⟨left, right, leftPosition, rightPosition, by simpa only [typed] using lowered success⟩
end Itasca.Runtime.Compiler
