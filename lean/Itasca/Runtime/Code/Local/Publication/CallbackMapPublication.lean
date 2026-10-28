import Itasca.Runtime.Code.Local.Publication.BranchMapPublication
import Itasca.Runtime.Code.Local.Publication.OrdinaryMapPublication
import Itasca.Runtime.Code.Local.Callbacks.Calls.CallbackCursor
import Itasca.Runtime.Code.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Code.Local.Callbacks.Common.CompilerTerminalMetadata

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Actual br callback retains all control-map publication bounds. -/
theorem compiler_br_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops before state depth types = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at called
  split at called
  · obtain ⟨⟨result,middle⟩,emitted,rest⟩ := bind_ok_inv _ _ _ called
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unit =>
      cases unit
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
      have bounds := compiler_branch_map_publication ops law before middle depth 0#u32 false held emitted
      have cursor := compiler_branch_cursor ops law before middle depth 0#u32 false emitted
      exact compiler_observe_map_publication ops law {middle with reachable := false} after state
        (bounds.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl) (by simpa only [cursor] using forward) rest
  · exact compiler_observe_map_publication ops law before after state held forward called

/-- Actual br_if callback retains all control-map publication bounds. -/
theorem compiler_br_if_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops before state depth types = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at called
  split at called
  · obtain ⟨⟨result,middle⟩,emitted,rest⟩ := bind_ok_inv _ _ _ called
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unit =>
      cases unit
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
      have bounds := compiler_branch_map_publication ops law before middle depth 1#u32 true held emitted
      have cursor := compiler_branch_cursor ops law before middle depth 1#u32 true emitted
      exact compiler_observe_map_publication ops law middle after state
        bounds (by simpa only [cursor] using forward) rest
  · exact compiler_observe_map_publication ops law before after state held forward called

/-- Actual unreachable callback retains all control-map publication bounds. -/
theorem compiler_unreachable_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (held : ControlMapPublication before) (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops before state = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable at called
  split at called
  · obtain ⟨⟨result,middle⟩,emitted,rest⟩ := bind_ok_inv _ _ _ called
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unit =>
      cases unit
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
      have bounds := compiler_emit_map_publication ops law before middle .Unreachable held emitted
      have cursor := compiler_emit_cursor ops before middle .Unreachable (.Ok ()) emitted
      exact compiler_observe_map_publication ops law {middle with reachable := false} after state
        (bounds.retained ⟨rfl,le_rfl⟩ rfl rfl le_rfl le_rfl) (by simpa only [cursor] using forward) rest
  · exact compiler_observe_map_publication ops law before after state held forward called

/-- Actual RETURN preserves maps and owners while emitting its return instruction. -/
theorem compiler_return_map_publication {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (held : ControlMapPublication before)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state = .ok (.Ok (),after)) :
    ControlMapPublication after := by
  apply held.ordinary (compiler_return_ordinary_result ops law before after state (.Ok ()) called)
    (compiler_return_code_mono ops law before after state called)
  rw [compiler_return_cursor ops law before after state called]
  exact forward

end Itasca.Runtime.Code
