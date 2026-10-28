import Exec.Code.Local.Relations.Common.PairSuccess
import Exec.Code.Local.Relations.Common.StatefulSuccess
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Aeneas.Std.Result Itasca.ResultFacts
set_option maxRecDepth 4096

noncomputable def indirectCallLowering {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (a b : U32) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) := do
  let i ← lift (UScalar.cast .Usize a)
  let signature ← Slice.index_usize before.signatures i
  let o ← lift (U32.checked_add signature.param_slots 1#u32)
  let r ←
    core.option.Option.ok_or o _root_.Itasca.error.VisitError.OutOfMemory
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let o1 ← lift (U32.checked_sub before.height val)
    let r1 ←
      core.option.Option.ok_or o1
        _root_.Itasca.error.VisitError.OutOfMemory
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let (r2, paired) ←
        runtime.compiler.FunctionCompiler.pair ops before b a
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let r3 ←
          runtime.compiler.FunctionCompiler.operand ops paired
            1#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          runtime.compiler.lower.FunctionCompiler.finish_op
            ops paired state (runtime.bytecode.Instr.CallIndirect
            val2 val3 val1)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          ok (r4, paired)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        ok (r3, paired)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      ok (r2, before)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
        residual
    ok (r1, before)

theorem lower_indirect_call_dispatch {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (a b : U32)
    (reachable : before.reachable = true) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 =
      indirectCallLowering ops before state a b := by
  unfold runtime.compiler.lower.FunctionCompiler.op
  rw [if_pos reachable]
  rfl

theorem lower_indirect_call_eq {A : Type} (ops : runtime.platform.Alloc A)
    (before paired : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (a b total base entry index : U32) (signature : runtime.compiler.Signature)
    (reachable : before.reachable = true)
    (read : Slice.index_usize before.signatures (UScalar.cast .Usize a) = .ok signature)
    (added : U32.checked_add signature.param_slots 1#u32 = some total)
    (subtracted : U32.checked_sub before.height total = some base)
    (pair : runtime.compiler.FunctionCompiler.pair ops before b a = .ok (.Ok entry,paired))
    (operand : runtime.compiler.FunctionCompiler.operand ops paired 1#usize = .ok (.Ok index)) :
    runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 =
      runtime.compiler.lower.FunctionCompiler.finish_op ops paired state (.CallIndirect entry index base) := by
  rw [lower_indirect_call_dispatch ops before state a b reachable]
  simp only [indirectCallLowering,lift,bind_ok,read,added,subtracted,pair,operand,uncurry_apply_pair,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]

/-- A successful indirect call exposes the actual pair allocation after its
checked argument-base arithmetic. -/
theorem lower_indirect_call_pair_success {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (a b total base : U32) (signature : runtime.compiler.Signature)
    (reachable : before.reachable = true)
    (read : Slice.index_usize before.signatures (UScalar.cast .Usize a) = .ok signature)
    (added : U32.checked_add signature.param_slots 1#u32 = some total)
    (subtracted : U32.checked_sub before.height total = some base)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 = .ok (.Ok (),after)) :
    ∃ entry paired, runtime.compiler.FunctionCompiler.pair ops before b a = .ok (.Ok entry,paired) := by
  rw [lower_indirect_call_dispatch ops before state a b reachable] at accepted
  simp only [indirectCallLowering,lift,bind_ok,read,added,subtracted,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch] at accepted
  obtain ⟨⟨result,paired⟩,pair,rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok entry => exact ⟨entry,paired,pair⟩
end Itasca.Runtime.Code
