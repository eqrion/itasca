import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Compiler.Local.Lowering.Emission.OpEquations
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Runtime.Compiler.Local.Lowering.LoweringLocal

/-!
Proofs for Runtime / Compiler / Local / Relations / Global.

This module collects GlobalLowering, GlobalOperands.
Each section documents its contracts and consumers.
-/

/-! ## GlobalLowering -/

section

/-!
# Global lowering equations

Global get/set dispatch and vector-width facts identify the exact instructions selected from concrete validator operands. Safety and emission proofs use these equations.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std
open Aeneas.Std.Result
set_option maxRecDepth 4096

@[step] theorem top_is_v128_total (values : Slice Itasca.code.StackType) :
    runtime.compiler.lower.top_is_v128 values ⦃ _ => True ⦄ := by
  unfold runtime.compiler.lower.top_is_v128
  simp only [core.slice.Slice.is_empty, Slice.len_val, bind_ok]
  split
  · simp [WP.spec_ok]
  · step as ⟨index, indexEq⟩
    step as ⟨value, found⟩
    cases value with
    | Bot => simp [WP.spec_ok]
    | Val ty => cases ty <;> simp [WP.spec_ok]

noncomputable def globalGetLowering {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (index : U32) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) := do
  let s := alloc.vec.Vec.deref state.vals
  let wide ← runtime.compiler.lower.top_is_v128 s
  let instruction ←
    if wide
    then ok (runtime.bytecode.Instr.GlobalGet2 compiler.height index)
    else ok (runtime.bytecode.Instr.GlobalGet compiler.height index)
  runtime.compiler.lower.FunctionCompiler.finish_op ops compiler
    state instruction

noncomputable def globalSetLowering {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (index : U32) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) := do
  let r ←
    runtime.compiler.FunctionCompiler.operand ops compiler
      1#usize
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let i ← compiler.height - val
    let instruction ←
      if i = 2#u32
      then ok (runtime.bytecode.Instr.GlobalSet2 val index)
      else ok (runtime.bytecode.Instr.GlobalSet val index)
    runtime.compiler.lower.FunctionCompiler.finish_op ops
      compiler state instruction
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
        residual
    ok (r1, compiler)

theorem lower_global_get_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (index : U32) (wide : Bool) (reachable : compiler.reachable = true)
    (top : runtime.compiler.lower.top_is_v128 (alloc.vec.Vec.deref state.vals) = .ok wide) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 35#u16 index 0#u32 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state
        (globalGetInstruction wide compiler.height index) := by
  have dispatch : runtime.compiler.lower.FunctionCompiler.op ops compiler state 35#u16 index 0#u32 0#u128 =
      globalGetLowering ops compiler state index := by
    exact runtime.compiler.lower.FunctionCompiler.op.global_get ops compiler state index 0#u32 0#u128 reachable
  rw [dispatch]
  unfold globalGetLowering
  dsimp only
  rw [top]
  cases wide <;> simp [bind_ok, globalGetInstruction]

theorem lower_global_set_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (index src difference : U32) (reachable : compiler.reachable = true)
    (operand : runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok src))
    (hdifference : (compiler.height - src) = Result.ok difference) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 36#u16 index 0#u32 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state
        (globalSetInstruction (decide (difference = 2#u32)) src index) := by
  have dispatch : runtime.compiler.lower.FunctionCompiler.op ops compiler state 36#u16 index 0#u32 0#u128 =
      globalSetLowering ops compiler state index := by
    exact runtime.compiler.lower.FunctionCompiler.op.global_set ops compiler state index 0#u32 0#u128 reachable
  rw [dispatch]
  unfold globalSetLowering
  simp only [operand, hdifference, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    globalSetInstruction]
  split <;> simp_all

def valueIsVector : Itasca.wasm_types.ValueType → Bool
  | .V128 => true
  | _ => false

theorem top_is_v128_shape (values : Slice Itasca.code.StackType)
    (front : List Itasca.code.StackType) (ty : Itasca.wasm_types.ValueType)
    (shape : values.val = front ++ [.Val ty]) :
    runtime.compiler.lower.top_is_v128 values = .ok (valueIsVector ty) := by
  have total : runtime.compiler.lower.top_is_v128 values ⦃ result => result = valueIsVector ty ⦄ := by
    unfold runtime.compiler.lower.top_is_v128
    simp [core.slice.Slice.is_empty, Slice.len_val, shape]
    step as ⟨last, lastEq⟩
    step as ⟨value, found⟩
    have index : last.val = front.length := by simp only [Slice.len_val, shape] at lastEq; scalar_tac
    have valueEq : value = .Val ty := by simpa [shape, index] using found
    subst value
    rw [valueEq]
    cases ty <;> simp [valueIsVector]
  obtain ⟨result, actual, equal⟩ := WP.spec_imp_exists total
  simpa only [equal] using actual
end Itasca.Compiler

end

/-! ## GlobalOperands -/

section

open Itasca.Representation

/-!
# Global operand emission

Concrete operand types and compiler layout determine global get/set lowering. The resulting code relation accounts for scalar/vector slot widths and the updated operand stack.
-/
namespace Itasca.Compiler
open Aeneas Aeneas.Std

@[step] theorem compiler_global_get_lowered {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (front : List Itasca.wasm_types.ValueType)
    (ty : Itasca.wasm_types.ValueType) (index : U32)
    (layout : CompilerLayout compiler (front.map Itasca.Translation.valueType))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = (front ++ [ty]).map Itasca.code.StackType.Val)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 35#u16 index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () →
        Lowered compiler out.2
          (globalGetInstruction (decide (width (Itasca.Translation.valueType ty) = 2)) compiler.height index)
          ((front ++ [ty]).map Itasca.Translation.valueType) ⦄ := by
  have top := top_is_v128_shape (alloc.vec.Vec.deref state.vals)
    (front.map Itasca.code.StackType.Val) ty (by simpa [alloc.vec.Vec.deref] using concrete)
  have wide : valueIsVector ty = decide (width (Itasca.Translation.valueType ty) = 2) := by
    cases ty <;> rfl
  rw [lower_global_get_eq ops compiler state index (valueIsVector ty) reachable top, wide]
  exact finish_op ops law compiler state (front ++ [ty]) _ _ layout concrete codeFits sourceFits coordinateFits

@[step] theorem compiler_global_set_lowered {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (types : List Itasca.wasm_types.ValueType)
    (front : List valtype) (ty : valtype) (index : U32)
    (layout : CompilerLayout compiler (front ++ [ty]))
    (reachable : compiler.reachable = true)
    (concrete : state.vals.val = types.map Itasca.code.StackType.Val)
    (typed : types.map Itasca.Translation.valueType = front)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 36#u16 index 0#u32 0#u128
      ⦃ out => out.1 = .Ok () → ∃ source : U32,
        source.val = slots (compilerLocals compiler) + slots front ∧
        Lowered compiler out.2 (globalSetInstruction (decide (width ty = 2)) source index) front ⦄ := by
  obtain ⟨source, read, position⟩ := last_operand ops compiler front ty layout
  have height := layout.height
  simp only [slots_append, slots, Nat.add_zero] at height
  obtain ⟨difference, subtract, differenceVal⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := compiler.height) (y := source) (by omega))
  have dw : difference.val = width ty := by omega
  have wide : (difference = 2#u32) ↔ width ty = 2 := by
    constructor
    · intro h
      have v : difference.val = 2 := by simpa using congrArg UScalar.val h
      omega
    · intro h; apply UScalar.eq_of_val_eq; simpa [h] using dw
  rw [lower_global_set_eq ops compiler state index source difference reachable read subtract]
  simp only [wide]
  step with finish_op ops law compiler state types
    (globalSetInstruction (decide (width ty = 2)) source index) _ layout concrete
    codeFits sourceFits coordinateFits as ⟨out, lowered, success⟩
  exact ⟨source, position, by simpa only [typed] using lowered success⟩
end Itasca.Compiler

end
