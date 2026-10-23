import Exec.Code.Body.Control.Table.StructuredCompilerPrefixTerminal
import Exec.Code.Local.Callbacks.Calls.CallbackSources
import Exec.Code.Local.Callbacks.Calls.CallbackCursor
import Exec.Code.Local.Callbacks.Common.CompilerOrdinaryResults
import Exec.Code.Local.Capacity.EmissionGrowth
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts

theorem StructuredCompilerPrefix.unreachable {jumpTables : List Aeneas.Std.U32} {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (state : code.OpIterState)
    (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
      ops before state = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance .UNREACHABLE)
      state.vals.val state.pos.val ∧ after.reachable = false := by
  have sources := compiler_unreachable_sources ops law before after state accepted
  have cursor := compiler_unreachable_cursor ops law before after state accepted
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable at accepted
  split at accepted
  · rename_i reachable
    obtain ⟨⟨result, middle⟩, emitted, observed⟩ := bind_ok_inv _ _ _ accepted
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at observed
    | Ok unit =>
      cases unit
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at observed
      have emittedMetadata := compiler_emit_ordinary_result ops before middle .Unreachable (.Ok ()) emitted
      have observedMetadata := compiler_observe_ordinary_result ops law {middle with reachable := false} after state (.Ok ()) observed
      have ordinary : CompilerOrdinaryStable before after := emittedMetadata.trans (by
        exact ⟨observedMetadata.metadata, observedMetadata.capacity⟩)
      have frame := compiler_observe_frame ops law {middle with reachable := false} state
      rw [observed, WP.spec_ok] at frame
      change ObserveFrame {middle with reachable := false} after at frame
      have code := compiler_emit_code_success ops law before middle .Unreachable emitted
      have codeFinal : after.function.code.val = before.function.code.val ++ [.Unreachable] := by rw [frame]; exact code
      have dead : after.reachable = false := by rw [frame]
      exact ⟨invariant.terminate reachable dead ordinary (.unreachable _) codeFinal sources consumed (by rw [cursor]), dead⟩
  · rename_i notReachable
    have dead : before.reachable = false := Bool.eq_false_iff.mpr notReachable
    have ordinary := compiler_observe_ordinary_result ops law before after state (.Ok ()) accepted
    have frame := compiler_observe_frame ops law before state
    rw [accepted, WP.spec_ok] at frame
    change ObserveFrame before after at frame
    have deadAfter : after.reachable = false := by rw [frame]; exact dead
    have unchanged : after.function.code = before.function.code := by rw [frame]
    exact ⟨invariant.skip .UNREACHABLE dead deadAfter ordinary unchanged sources consumed (by rw [cursor]), deadAfter⟩
end Exec.Code
