import Itasca.Runtime.Compiler.Local.Lowering.Float.FloatLowering
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Local.Capacity.ControlCapacity
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal
import Itasca.Spec.Checks

/-!
Sections, each formerly its own module: FloatEffects, FloatOperands, FloatEncoding.
-/

/-! ## FloatEffects -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std SourceMachine.Float
set_option maxRecDepth 4096
theorem compiler_float_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Instruction)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (floatOpcode op) 0#u32 0#u32 0#u128 = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · rw [lower_float_dispatch ops before state op reach] at accepted
    unfold floatLowering at accepted
    repeat' metadata_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_float_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Instruction)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (floatOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (), after)) :
    SourceProgress before after := by
  by_cases reach : before.reachable = true
  · rw [lower_float_dispatch ops before state op reach] at accepted
    unfold floatLowering at accepted
    repeat' sources_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_sources ops law before after state (.Ok ()) accepted

theorem compiler_float_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Instruction)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (floatOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  by_cases reach : before.reachable = true
  · rw [lower_float_dispatch ops before state op reach] at accepted
    unfold floatLowering at accepted
    repeat' cursor_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact compiler_observe_cursor ops law before after state (.Ok ()) accepted rfl

theorem compiler_float_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (op : Instruction)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (floatOpcode op) 0#u32 0#u32 0#u128 = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  by_cases reach : before.reachable = true
  · rw [lower_float_dispatch ops before state op reach] at accepted
    unfold floatLowering at accepted
    repeat' capacity_step accepted using ops, law
  · rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (Bool.eq_false_of_not_eq_true reach)] at accepted
    exact ⟨(compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).1,
      (compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).2 rfl⟩

end Itasca.Runtime.Compiler

end

/-! ## FloatOperands -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std SourceMachine.Float

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
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
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
end Itasca.Runtime.Compiler

end

/-! ## FloatEncoding -/

section

namespace Itasca.Runtime.Compiler
open Itasca

theorem float_source_declared (op : SourceMachine.Float.Instruction) (refs : List funcidx) :
    DeclaredReferences.Instruction refs op.source := by
  cases op <;> simp [SourceMachine.Float.Instruction.source,DeclaredReferences.Instruction,DeclaredReferences.instructionIndices]
end Itasca.Runtime.Compiler

end
