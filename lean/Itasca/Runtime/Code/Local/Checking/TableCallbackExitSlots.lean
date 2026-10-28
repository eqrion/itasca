import Itasca.Runtime.Code.Local.Checking.BranchCallbackExitSlots
import Itasca.Runtime.Code.Local.Checking.TableExitSlotBounds

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Collecting a table label preserves instruction checks and pending owners. -/
theorem compiler_table_label_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (held : FrameExitSlotBounds before)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
      ops before state depth = .ok (.Ok (),after)) : FrameExitSlotBounds after := by
  obtain ⟨budget,depths,frame,_⟩ := compiler_table_label_success ops law before after state depth called
  exact held.retained (by rw [frame]) (by rw [frame])

/-- Lift the source-derived raw table proof through the final default label,
scratch-buffer clearing, and dead-stack observation of the actual callback. -/
theorem compiler_br_table_callback_exit_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (held : FrameExitSlotBounds before)
    (lower : ∀ labeled,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
        ops before state fallback = .ok (.Ok (),labeled) → labeled.reachable = true → ∀ lowered,
      runtime.compiler.control.FunctionCompiler.lower_table_branches ops labeled = .ok (.Ok (),lowered) →
      FrameExitSlotBounds lowered)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types = .ok (.Ok (),after)) : FrameExitSlotBounds after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at called
  obtain ⟨⟨result,labeled⟩,labelCalled,rest⟩ := bind_ok_inv _ _ _ called
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok unit =>
    cases unit
    have checked := compiler_table_label_exit_slots ops law before labeled state fallback held labelCalled
    simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
    split at rest
    · rename_i live
      obtain ⟨⟨result,lowered⟩,lowerCalled,rest⟩ := bind_ok_inv _ _ _ rest
      cases result with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unit =>
        cases unit
        have loweredChecked := lower labeled labelCalled live lowered lowerCalled
        simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
        obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
        exact compiler_observe_exit_slots ops law {lowered with reachable := false,table_depths := cleared}
          after state (loweredChecked.retained rfl le_rfl) observed
    · obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
      exact compiler_observe_exit_slots ops law {labeled with table_depths := cleared}
        after state (checked.retained rfl le_rfl) observed

end Itasca.Runtime.Code
