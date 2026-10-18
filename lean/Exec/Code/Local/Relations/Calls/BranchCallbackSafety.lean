import Exec.Code.Local.Relations.Control.BranchSafety
import Exec.Code.Local.Relations.Control.BranchIfSafetyComplete
import Exec.Code.Local.Callbacks.Common.FixupBudget
namespace Exec.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem branch_depth_target (frames : alloc.vec.Vec runtime.compiler.Frame) (depth : U32)
    (bound : depth.val < frames.val.length) :
    ∃ index : Usize, ∃ frame, frames.val[index.val]? = some frame ∧
      index.val + depth.val + 1 = frames.val.length := by
  let index := Usize.ofNatCore (frames.val.length-depth.val-1) (by
    have h := (alloc.vec.Vec.len frames).hBounds
    change frames.val.length < 2^UScalarTy.Usize.numBits at h
    omega)
  have inside : index.val < frames.val.length := by
    change frames.val.length-depth.val-1 < frames.val.length
    omega
  refine ⟨index,frames.val[index.val],by simp [inside],?_⟩
  change frames.val.length-depth.val-1+depth.val+1=frames.val.length
  omega

@[step] theorem compiler_br_callback_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (depthFits : depth.val < compiler.frames.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (codeFits : compiler.function.code.val.length+2 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length+2 ≤ Usize.max)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops compiler state depth types ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
  split
  · obtain ⟨index,frame,lookup,position⟩ := branch_depth_target compiler.frames depth depthFits
    step with compiler_branch_total ops law compiler frame index depth lookup position
      (fixups.lookup lookup (by omega)) codeFits sourceFits coordinate as ⟨status,after⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      exact compiler_observe_stack ops law {after with reachable := false} state
  · exact compiler_observe_stack ops law compiler state

@[step] theorem compiler_br_if_callback_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (depthFits : depth.val < compiler.frames.val.length)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (pcBound : compiler.function.code.val.length+3 < 2^32)
    (codeFits : compiler.function.code.val.length+3 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length+3 ≤ Usize.max)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops compiler state depth types ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
  split
  · obtain ⟨index,frame,lookup,position⟩ := branch_depth_target compiler.frames depth depthFits
    step with compiler_branch_if_total_raw ops law compiler frame index depth lookup position
      (fixups.lookup lookup (by omega)) pcBound codeFits sourceFits coordinate as ⟨status,after⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      exact compiler_observe_stack ops law after state
  · exact compiler_observe_stack ops law compiler state
end Exec.Code
