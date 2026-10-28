import Itasca.Runtime.Code.Local.Callbacks.Control.FixupElsePreservation
import Itasca.Runtime.Code.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private theorem observe_budget {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (), after)) :
    FixupBudget after.frames.val after.function.code.val.length :=
  budget.ordinary (compiler_observe_ordinary_result ops law before after state (.Ok ()) accepted)
    (compiler_observe_code_mono ops law before after state (.Ok ()) accepted)

theorem compiler_br_fixup_budget {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth types = .ok (.Ok (), after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at accepted
  split at accepted
  · obtain ⟨⟨status,middle⟩,called,rest⟩ := bind_ok_inv _ _ _ accepted
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok value =>
      cases value
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
      have kept := compiler_branch_fixup_budget ops law before middle depth 0#u32 false budget called
      exact observe_budget ops law {middle with reachable := false} after state kept rest
  · exact observe_budget ops law before after state budget accepted

theorem compiler_br_if_fixup_budget {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth types = .ok (.Ok (), after)) :
    FixupBudget after.frames.val after.function.code.val.length := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at accepted
  split at accepted
  · obtain ⟨⟨status,middle⟩,called,rest⟩ := bind_ok_inv _ _ _ accepted
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok value =>
      cases value
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at rest
      have kept := compiler_branch_fixup_budget ops law before middle depth 1#u32 true budget called
      exact observe_budget ops law middle after state kept rest
  · exact observe_budget ops law before after state budget accepted

end Itasca.Runtime.Code
