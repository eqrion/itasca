import Exec.Code.Local.Checking.NumericInstructionPrefix
import Exec.Code.Local.Checking.BranchExitSlotBounds

namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Actual operand observation preserves every recorded forward-exit region. -/
theorem compiler_observe_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  have frame := compiler_observe_frame ops law before state
  rw [called,WP.spec_ok] at frame
  dsimp only at frame
  have frames : after.frames = before.frames := by rw [frame]
  exact held.retained (congrArg alloc.vec.Vec.val frames) (compiler_observe_stable ops law before after state called).capacity

/-- Lift a source-derived raw branch preservation proof through actual br and
its final dead-stack observation. Forward/loop adapters discharge the local
branch premise; no body-level target trace is assumed here. -/
theorem compiler_br_callback_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (held : FrameExitSlotBounds before)
    (branch : before.reachable = true → ∀ middle,
      runtime.compiler.control.FunctionCompiler.branch ops before depth 0#u32 false = .ok (.Ok (),middle) →
      FrameExitSlotBounds middle)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops before state depth types = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at called
  split at called
  · rename_i live
    obtain ⟨⟨status,middle⟩,emitted,rest⟩ := bind_ok_inv _ _ _ called
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unit =>
      cases unit
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
      have checked := branch live middle emitted
      apply compiler_observe_exit_slots ops law {middle with reachable := false} after state _ rest
      exact checked.retained rfl le_rfl
  · exact compiler_observe_exit_slots ops law before after state held called

/-- Lift source-derived conditional branch checking through actual br_if and
its stack observation, including a dead prefix that emits no branch. -/
theorem compiler_br_if_callback_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (held : FrameExitSlotBounds before)
    (branch : before.reachable = true → ∀ middle,
      runtime.compiler.control.FunctionCompiler.branch ops before depth 1#u32 true = .ok (.Ok (),middle) →
      FrameExitSlotBounds middle)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops before state depth types = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at called
  split at called
  · rename_i live
    obtain ⟨⟨status,middle⟩,emitted,rest⟩ := bind_ok_inv _ _ _ called
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unit =>
      cases unit
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
      exact compiler_observe_exit_slots ops law middle after state (branch live middle emitted) rest
  · exact compiler_observe_exit_slots ops law before after state held called

end Exec.Code
