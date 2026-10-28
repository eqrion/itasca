import Exec.Code.Local.Relations.Memory.MemoryOpcode
import Exec.Code.Local.Lowering.Common.Lowering
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Aeneas.Std.Result
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable def memoryLoadLowering {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Abs.Memory.Load) (offset : U32) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) := do
  let r ←
    runtime.compiler.FunctionCompiler.operand ops compiler
      1#usize
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let o ← runtime.bytecode.Instr.make_load (memoryLoadOpcode op) val val1 offset
      let r1 ←
        core.option.Option.ok_or o
          _root_.Itasca.error.VisitError.OutOfMemory
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        runtime.compiler.lower.FunctionCompiler.finish_op ops
          compiler state val2
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
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
        residual
    ok (r1, compiler)

theorem lower_memory_load_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Abs.Memory.Load) (offset alignment : U32) (reachable : compiler.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryLoadOpcode op) offset alignment 0#u128 =
      memoryLoadLowering ops compiler state op offset := by
  cases op with
  | full ty => cases ty <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> rw [if_pos reachable] <;> rfl
  | packed ty width sign =>
    cases ty <;> cases width <;> cases sign <;>
      unfold runtime.compiler.lower.FunctionCompiler.op <;> rw [if_pos reachable] <;> rfl

noncomputable def memoryStoreLowering {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Abs.Memory.Store) (offset : U32) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) := do
  let r ←
    runtime.compiler.FunctionCompiler.operand ops compiler
      2#usize
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ←
      runtime.compiler.FunctionCompiler.operand ops compiler
        1#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let o ← runtime.bytecode.Instr.make_store (memoryStoreOpcode op) val val1 offset
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

theorem lower_memory_store_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Abs.Memory.Store) (offset alignment : U32) (reachable : compiler.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryStoreOpcode op) offset alignment 0#u128 =
      memoryStoreLowering ops compiler state op offset := by
  cases op with
  | full ty => cases ty <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> rw [if_pos reachable] <;> rfl
  | packed ty width =>
    cases ty <;> cases width <;>
      unfold runtime.compiler.lower.FunctionCompiler.op <;> rw [if_pos reachable] <;> rfl

theorem lower_memory_load_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Abs.Memory.Load) (offset alignment address : U32) (reachable : compiler.reachable = true)
    (operand : runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok address)) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryLoadOpcode op) offset alignment 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (memoryLoadInstruction op address address offset) := by
  rw [lower_memory_load_dispatch ops compiler state op offset alignment reachable]
  unfold memoryLoadLowering
  simp only [operand, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    memoryLoadInstruction_make, core.option.Option.ok_or]

theorem lower_memory_store_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (op : Abs.Memory.Store) (offset alignment address value : U32) (reachable : compiler.reachable = true)
    (addressOperand : runtime.compiler.FunctionCompiler.operand ops compiler 2#usize = .ok (.Ok address))
    (valueOperand : runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok value)) :
    runtime.compiler.lower.FunctionCompiler.op ops compiler state (memoryStoreOpcode op) offset alignment 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops compiler state (memoryStoreInstruction op address value offset) := by
  rw [lower_memory_store_dispatch ops compiler state op offset alignment reachable]
  unfold memoryStoreLowering
  simp only [addressOperand, valueOperand, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    memoryStoreInstruction_make, core.option.Option.ok_or]
end Itasca.Runtime.Code
