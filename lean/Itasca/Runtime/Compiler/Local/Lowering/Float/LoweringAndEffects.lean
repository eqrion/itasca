import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Compiler.Local.Lowering.Emission.OpEquations
import Itasca.Runtime.SourceMachine.Float.Descriptors
import Itasca.Runtime.Equations.Bytecode
import Itasca.Generated.Funs
import Itasca.Runtime.Compiler.Local.Lowering.Integer.Lowering
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Source.SourceTactics
import Itasca.Runtime.Compiler.Local.Capacity.ControlCapacity
import Itasca.Runtime.Compiler.Local.Lowering.LoweringLocal
import Itasca.Spec.Typing

/-!
Proofs for Runtime / Compiler / Local / Lowering / Float.

This module collects Lowering, Effects.
Each section documents its contracts and consumers.
-/

/-! ## Lowering -/

section

/-!
# Lowering

Floating-point opcode selection and lowering agree with the source instruction descriptors.
-/

/-! ## FloatOpcode -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

def floatOpcode (op : SourceMachine.Float.Instruction) : U16 :=
  UScalar.ofNat op.opcode (by have := op.opcode_bound; change op.opcode ≤ 65535; omega)

theorem float_instruction_make (op : SourceMachine.Float.Instruction) (dst a b : U32) :
    runtime.bytecode.Instr.make_scalar (floatOpcode op) dst a b =
      .ok (some (floatInstruction op dst a b)) := by
  cases op with
  | unary ty operator => cases ty <;> cases operator <;> rfl
  | binary ty operator => cases ty <;> cases operator <;> rfl
  | compare ty operator => cases ty <;> cases operator <;> rfl
  | convert source target sign => cases source <;> cases target <;> cases sign <;> rfl
  | truncate source target sign saturating => cases source <;> cases target <;> cases sign <;> cases saturating <;> rfl
  | reinterpretFloat source => cases source <;> rfl
  | reinterpretInt source => cases source <;> rfl
  | promote | demote => rfl

theorem float_opcode_binary (op : SourceMachine.Float.Instruction) :
    runtime.compiler.lower.scalar_binary (floatOpcode op) = .ok (decide (op.arity = 2)) := by
  cases op with
  | unary ty operator => cases ty <;> cases operator <;> rfl
  | binary ty operator => cases ty <;> cases operator <;> rfl
  | compare ty operator => cases ty <;> cases operator <;> rfl
  | convert source target sign => cases source <;> cases target <;> cases sign <;> rfl
  | truncate source target sign saturating => cases source <;> cases target <;> cases sign <;> cases saturating <;> rfl
  | reinterpretFloat source => cases source <;> rfl
  | reinterpretInt source => cases source <;> rfl
  | promote | demote => rfl
end Itasca.Compiler

end

/-! ## FloatLowering -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std SourceMachine.Float

/-- The shared scalar lowering path, before resolving its source operands. -/
noncomputable def floatLowering {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Instruction) : Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) := do
    let binary ← runtime.compiler.lower.scalar_binary (floatOpcode op)
    let depth ← if binary
                  then Result.ok 2#usize
                  else Result.ok 1#usize
    let r ←
      runtime.compiler.FunctionCompiler.operand ops compiler depth
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let r1 ←
        runtime.compiler.FunctionCompiler.operand ops compiler
          1#usize
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let o ← runtime.bytecode.Instr.make_scalar (floatOpcode op) val val val1
        let r2 ←
          core.option.Option.ok_or o
            _root_.Itasca.error.VisitError.OutOfMemory
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          runtime.compiler.lower.FunctionCompiler.finish_op ops
            compiler state val2
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          Result.ok (r3, compiler)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        Result.ok (r2, compiler)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      Result.ok (r1, compiler)

set_option maxRecDepth 4096 in
theorem lower_float_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Instruction) (reachable : compiler.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128 =
      floatLowering ops compiler state op := by
  have allowed : (69 ≤ (floatOpcode op).val ∧ (floatOpcode op).val ≤ 196) ∨
      (256 ≤ (floatOpcode op).val ∧ (floatOpcode op).val ≤ 263) := by
    cases op with
    | unary ty operator => cases ty <;> cases operator <;> decide
    | binary ty operator => cases ty <;> cases operator <;> decide
    | compare ty operator => cases ty <;> cases operator <;> decide
    | convert source target sign => cases source <;> cases target <;> cases sign <;> decide
    | truncate source target sign saturating => cases source <;> cases target <;> cases sign <;> cases saturating <;> decide
    | reinterpretFloat source => cases source <;> decide
    | reinterpretInt source => cases source <;> decide
    | promote | demote => decide
  exact runtime.compiler.lower.FunctionCompiler.op.scalar ops compiler state (floatOpcode op)
    0#u32 0#u32 0#u128 reachable allowed

def floatDepth (op : Instruction) : Usize := if op.arity = 2 then 2#usize else 1#usize

theorem lower_float_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Instruction) (left right : U32) (reachable : compiler.reachable = true)
    (hleft : runtime.compiler.FunctionCompiler.operand ops compiler (floatDepth op) = .ok (.Ok left))
    (hright : runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok right)) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (floatInstruction op left left right) := by
  rw [lower_float_dispatch ops compiler state op reachable]
  unfold floatLowering
  rw [float_opcode_binary]
  by_cases binary : op.arity = 2
  · simp only [floatDepth, binary, ↓reduceIte] at hleft
    simp only [binary, ↓reduceIte, decide_true, bind_ok,
      hleft, hright, core.result.Result.Insts.CoreOpsTry.branch, float_instruction_make,
      core.option.Option.ok_or]
  · simp only [floatDepth, binary, ↓reduceIte] at hleft
    have same : left = right := by simpa only [Result.ok.injEq, core.result.Result.Ok.injEq] using hleft.symm.trans hright
    subst right
    simp only [binary, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok,
      hleft, core.result.Result.Insts.CoreOpsTry.branch, float_instruction_make,
      core.option.Option.ok_or]
end Itasca.Compiler

end

end

/-! ## Effects -/

section

open Itasca.Representation

/-!
# Effects

Floating-point instructions preserve their source shape and produce the specified emitted-code effects.
-/

/-! ## FloatEffects -/

section

namespace Itasca.Compiler
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

end Itasca.Compiler

end

/-! ## FloatOperands -/

section

namespace Itasca.Compiler
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
    (typed : types.map Itasca.Translation.valueType = front ++ [valtype_numtype op.output])
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
end Itasca.Compiler

end

/-! ## FloatEncoding -/

section

namespace Itasca.Compiler
open Itasca

theorem float_source_declared (op : SourceMachine.Float.Instruction) (refs : List funcidx) :
    Spec.DeclaredReferences.Instruction refs op.source := by
  cases op <;> simp [SourceMachine.Float.Instruction.source,Spec.DeclaredReferences.Instruction,Spec.DeclaredReferences.instructionIndices]
end Itasca.Compiler

end

end
