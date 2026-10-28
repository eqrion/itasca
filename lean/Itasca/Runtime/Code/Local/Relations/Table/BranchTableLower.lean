import Itasca.Runtime.Code.Local.Relations.Table.BranchTableTrace
import Itasca.Runtime.Code.Local.Relations.Table.BranchTableSuccess
import Itasca.Runtime.Code.Local.Initializer.InitializerProofs
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

/-- Successful lowering retains the exact side-table start/count, selector
lookup, dispatch emission, and finite sequence of target branches. -/
theorem compiler_lower_table_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before = .ok (.Ok (),after)) :
    ∃ start len selector emitted,
      start.val = before.function.jump_tables.val.length ∧
      len.val = before.table_depths.val.length ∧
      runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok (.Ok selector) ∧
      Emitted before emitted (.JumpTable selector start len) ∧
      TableBranchRun ops emitted 0 after := by
  unfold runtime.compiler.control.FunctionCompiler.lower_table_branches at accepted
  obtain ⟨startResult,startCalled,rest⟩ := bind_ok_inv _ _ _ accepted
  cases startResult with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok start =>
    have startSpec := bounded_index (alloc.vec.Vec.len before.function.jump_tables)
    rw [startCalled, WP.spec_ok] at startSpec
    have startEq := startSpec start rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨lenResult,lenCalled,rest⟩ := bind_ok_inv _ _ _ rest
    cases lenResult with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok len =>
      have lenSpec := bounded_index (alloc.vec.Vec.len before.table_depths)
      rw [lenCalled, WP.spec_ok] at lenSpec
      have lenEq := lenSpec len rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨operand,operandCalled,rest⟩ := bind_ok_inv _ _ _ rest
      cases operand with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok selector =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨⟨emittedStatus,emitted⟩,emitCalled,rest⟩ := bind_ok_inv _ _ _ rest
        cases emittedStatus with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok unit =>
          cases unit
          simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
          obtain ⟨output,loopCalled,rest⟩ := bind_ok_inv _ _ _ rest
          have statusEq : snapshotStatus output = .Ok () := by
            rcases output with ⟨signatures, functionSlots, budget, batchStart, function, frames, reachable,
              nextSource, operands, height, offsets, depths, status⟩
            exact (Prod.mk.inj (Result.ok.injEq.mp rest)).1
          have compilerEq : snapshotCompiler output = after := by
            rcases output with ⟨signatures, functionSlots, budget, batchStart, function, frames, reachable,
              nextSource, operands, height, offsets, depths, status⟩
            exact (Prod.mk.inj (Result.ok.injEq.mp rest)).2
          have trace := (compiler_table_loop_trace ops law emitted 0#usize (.Ok ()) output loopCalled statusEq).2
          rw [compilerEq] at trace
          exact ⟨start,len,selector,emitted,startEq,lenEq,operandCalled,
            compiler_emit_success ops law before emitted _ emitCalled,trace⟩
end Itasca.Runtime.Code
