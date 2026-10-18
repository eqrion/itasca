import Exec.Code.Local.Capacity.CapacityTactic
import Exec.Code.Local.Lowering.Integer.LoweringInteger
import Exec.Code.Local.Lowering.Common.LoweringEqz
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
theorem compiler_integer_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ty : Inn) (operation : IntegerBinary)
    (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (binaryOpcode ty operation) a b bits = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state (binaryOpcode ty operation) a b bits = (do
        let binary ← runtime.compiler.lower.scalar_binary (binaryOpcode ty operation)
        let depth ← if binary
                      then Result.ok 2#usize
                      else Result.ok 1#usize
        let r ←
          runtime.compiler.FunctionCompiler.operand ops before depth
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let r1 ←
            runtime.compiler.FunctionCompiler.operand ops before
              1#usize
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue val1 =>
            let o ← runtime.bytecode.Instr.make_scalar (binaryOpcode ty operation) val val val1
            let r2 ←
              core.option.Option.ok_or o
                _root_.Itasca.error.VisitError.OutOfMemory
            let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
            match cf2 with
            | core.ops.control_flow.ControlFlow.Continue val2 =>
              runtime.compiler.lower.FunctionCompiler.finish_op ops
                before state val2
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r3 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
                  residual
              Result.ok (r3, before)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r2 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
                residual
            Result.ok (r2, before)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r1 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          Result.ok (r1, before)) := by
      cases ty <;> cases operation <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> rw [if_pos reach] <;> rfl
    rw [run] at accepted
    repeat' capacity_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact ⟨(compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).1,
      (compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).2 rfl⟩

theorem compiler_eqz_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ty : Inn)
    (a b : U32) (bits : U128)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state (eqzOpcode ty) a b bits = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  by_cases reach : before.reachable = true
  · have run : runtime.compiler.lower.FunctionCompiler.op ops before state (eqzOpcode ty) a b bits = (do
        let binary ← runtime.compiler.lower.scalar_binary (eqzOpcode ty)
        let depth ← if binary
                      then Result.ok 2#usize
                      else Result.ok 1#usize
        let r ←
          runtime.compiler.FunctionCompiler.operand ops before depth
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let r1 ←
            runtime.compiler.FunctionCompiler.operand ops before
              1#usize
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue val1 =>
            let o ← runtime.bytecode.Instr.make_scalar (eqzOpcode ty) val val val1
            let r2 ←
              core.option.Option.ok_or o
                _root_.Itasca.error.VisitError.OutOfMemory
            let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
            match cf2 with
            | core.ops.control_flow.ControlFlow.Continue val2 =>
              runtime.compiler.lower.FunctionCompiler.finish_op ops
                before state val2
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r3 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
                  residual
              Result.ok (r3, before)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r2 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
                residual
            Result.ok (r2, before)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r1 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
              residual
          Result.ok (r1, before)) := by
      cases ty <;> unfold runtime.compiler.lower.FunctionCompiler.op <;> rw [if_pos reach] <;> rfl
    rw [run] at accepted
    repeat' capacity_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact ⟨(compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).1,
      (compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).2 rfl⟩

theorem compiler_integer_callback_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ty : Inn) (operation : IntegerBinary)
    (accepted : binaryCallback ops before state ty operation = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  rw [binaryCallback_eq] at accepted
  exact compiler_integer_capacity ops law before after state ty operation _ _ _ accepted

theorem compiler_eqz_callback_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ty : Inn)
    (accepted : eqzCallback ops before state ty = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  rw [eqzCallback_eq] at accepted
  exact compiler_eqz_capacity ops law before after state ty _ _ _ accepted


end Exec.Code
