import Itasca.Runtime.Compiler.Local.Lowering.Emission.OpEquations
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal

/-!
Sections, each formerly its own module: SelectLowering, SelectOperands.
-/

/-! ## SelectLowering -/

section

/-!
The bytecode lowering of untyped select.

Main declarations: `selectLowering` and `selectInstruction`. A direct consumer is `Compiler.Local.Relations.Emission.CoreLoweringEffects`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
open Aeneas.Std.Result
set_option maxRecDepth 4096

noncomputable def selectLowering {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) := do
  let r ←
    runtime.compiler.FunctionCompiler.operand ops compiler
      3#usize
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ←
      runtime.compiler.FunctionCompiler.operand ops compiler
        2#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r2 ←
        runtime.compiler.FunctionCompiler.operand ops compiler
          1#usize
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let i ← val1 - val
        let instruction ←
          if i = 2#u32
          then ok (runtime.bytecode.Instr.Select2 val val1 val2)
          else ok (runtime.bytecode.Instr.Select val val1 val2)
        runtime.compiler.lower.FunctionCompiler.finish_op ops
          compiler state instruction
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        ok (r3, compiler)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r2, compiler)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
        residual
    ok (r1, compiler)

def selectInstruction (wide : Bool) (left right condition : U32) : runtime.bytecode.Instr :=
  if wide then .Select2 left right condition else .Select left right condition

theorem lower_select_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (left right condition difference : U32) (typed : Bool)
    (reachable : compiler.reachable = true)
    (hleft : runtime.compiler.FunctionCompiler.operand ops compiler 3#usize = .ok (.Ok left))
    (hright : runtime.compiler.FunctionCompiler.operand ops compiler 2#usize = .ok (.Ok right))
    (hcondition : runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok condition))
    (hdifference : (right - left) = Result.ok difference) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (if typed then 28#u16 else 27#u16) 0#u32 0#u32 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state
        (selectInstruction (decide (difference = 2#u32)) left right condition) := by
  have dispatch : runtime.compiler.lower.FunctionCompiler.op ops compiler state
      (if typed then 28#u16 else 27#u16) 0#u32 0#u32 0#u128 =
      selectLowering ops compiler state := by
    exact runtime.compiler.lower.FunctionCompiler.op.select ops compiler state (if typed then 28#u16 else 27#u16)
      0#u32 0#u32 0#u128 reachable (by cases typed <;> decide)
  rw [dispatch]
  unfold selectLowering
  simp only [hleft, hright, hcondition, hdifference, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch, selectInstruction]
  split <;> simp_all

end Itasca.Runtime.Compiler

end

/-! ## SelectOperands -/

section

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

end
