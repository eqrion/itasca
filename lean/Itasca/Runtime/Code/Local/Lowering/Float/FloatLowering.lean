import Itasca.Runtime.Code.Local.Lowering.Float.FloatOpcode
import Itasca.Runtime.Code.Local.Lowering.Common.LoweringArithmetic
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Abs.Float

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

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
theorem lower_float_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Instruction) (reachable : compiler.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (floatOpcode op) 0#u32 0#u32 0#u128 =
      floatLowering ops compiler state op := by
  cases op with
  | unary ty operator => cases ty <;> cases operator <;> (unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl)
  | binary ty operator => cases ty <;> cases operator <;> (unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl)
  | compare ty operator => cases ty <;> cases operator <;> (unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl)
  | convert source target sign => cases source <;> cases target <;> cases sign <;> (unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl)
  | truncate source target sign saturating => cases source <;> cases target <;> cases sign <;> cases saturating <;> (unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl)
  | reinterpretFloat source => cases source <;> (unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl)
  | reinterpretInt source => cases source <;> (unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl)
  | promote | demote => skip <;> (unfold runtime.compiler.lower.FunctionCompiler.op; rw [if_pos reachable]; rfl)

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
  rw [floatOpcode_binary]
  by_cases binary : op.arity = 2
  · simp only [floatDepth, binary, ↓reduceIte] at hleft
    simp only [binary, ↓reduceIte, decide_true, bind_ok,
      hleft, hright, core.result.Result.Insts.CoreOpsTry.branch, floatInstruction_make,
      core.option.Option.ok_or]
  · simp only [floatDepth, binary, ↓reduceIte] at hleft
    have same : left = right := by simpa only [Result.ok.injEq, core.result.Result.Ok.injEq] using hleft.symm.trans hright
    subst right
    simp only [binary, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok,
      hleft, core.result.Result.Insts.CoreOpsTry.branch, floatInstruction_make,
      core.option.Option.ok_or]
end Itasca.Runtime.Code
