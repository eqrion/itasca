import Itasca.Runtime.Code.Local.Lowering.Common.Lowering
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
open Aeneas.Std.Result
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

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

def globalGetInstruction (wide : Bool) (dst index : U32) : runtime.bytecode.Instr :=
  if wide then .GlobalGet2 dst index else .GlobalGet dst index

def globalSetInstruction (wide : Bool) (src index : U32) : runtime.bytecode.Instr :=
  if wide then .GlobalSet2 src index else .GlobalSet src index

theorem lower_global_get_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (index : U32) (wide : Bool) (reachable : compiler.reachable = true)
    (top : runtime.compiler.lower.top_is_v128 (alloc.vec.Vec.deref state.vals) = .ok wide) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state 35#u16 index 0#u32 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state
        (globalGetInstruction wide compiler.height index) := by
  have dispatch : runtime.compiler.lower.FunctionCompiler.op ops compiler state 35#u16 index 0#u32 0#u128 =
      globalGetLowering ops compiler state index := by
    unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_pos reachable]
    rfl
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
    unfold runtime.compiler.lower.FunctionCompiler.op
    rw [if_pos reachable]
    rfl
  rw [dispatch]
  unfold globalSetLowering
  simp only [operand, hdifference, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    globalSetInstruction]
  split <;> simp_all

def valueIsVector : Itasca.types.ValueType → Bool
  | .V128 => true
  | _ => false

theorem top_is_v128_shape (values : Slice Itasca.code.StackType)
    (front : List Itasca.code.StackType) (ty : Itasca.types.ValueType)
    (shape : values.val = front ++ [.Val ty]) :
    runtime.compiler.lower.top_is_v128 values = .ok (valueIsVector ty) := by
  have total : runtime.compiler.lower.top_is_v128 values ⦃ result => result = valueIsVector ty ⦄ := by
    unfold runtime.compiler.lower.top_is_v128
    simp [core.slice.Slice.is_empty, Slice.len_val, shape]
    step as ⟨last, lastEq⟩
    step as ⟨value, found⟩
    have index : last.val = front.length := by simp only [Slice.len_val, shape, List.length_append, List.length_singleton] at lastEq; scalar_tac
    have valueEq : value = .Val ty := by simpa [shape, index] using found
    subst value
    rw [valueEq]
    cases ty <;> simp [valueIsVector]
  obtain ⟨result, actual, equal⟩ := WP.spec_imp_exists total
  simpa only [equal] using actual
end Itasca.Runtime.Code
