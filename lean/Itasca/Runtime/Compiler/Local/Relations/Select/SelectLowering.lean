import Itasca.Runtime.Compiler.Local.Lowering.Emission.Lowering

/-!
The bytecode lowering of untyped select.

Main declarations: `selectLowering` and `selectInstruction`. A direct consumer is `Compiler.Local.Relations.Emission.CoreLoweringEffects`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
open Aeneas.Std.Result
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

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
    cases typed <;> unfold runtime.compiler.lower.FunctionCompiler.op <;>
      rw [if_pos reachable] <;> rfl
  rw [dispatch]
  unfold selectLowering
  simp only [hleft, hright, hcondition, hdifference, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch, selectInstruction]
  split <;> simp_all
end Itasca.Runtime.Code
