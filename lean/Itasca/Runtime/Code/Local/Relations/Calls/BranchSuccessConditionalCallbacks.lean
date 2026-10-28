import Itasca.Runtime.Code.Local.Relations.Control.BranchSuccessConditionalLoop
import Itasca.Runtime.Code.Local.Relations.Common.ConditionalCertificates
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
theorem compiler_branch_if_forward_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val + frame.results.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (resumePosition : resume.val = compiler.function.code.val.length +
      (if frame.results = 0#u32 ∨ source = frame.height then 1 else 3))
    (fixupsBefore : ∀ site, site ∈ frame.fixups.val → site.val < compiler.function.code.val.length)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true = .ok (.Ok (), after)) : ∃ fixups,
        after.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
        ConditionalHole after.function.code.val fixups.val compiler.function.code.val.length
          frame.height source frame.results condition resume ∧
        after.function.code.val = compiler.function.code.val ++
          branchIfInstructions frame.height source frame.results core.num.U32.MAX condition resume ∧
        ∃ site, site.val = compiler.function.code.val.length +
          (if frame.results = 0#u32 ∨ source = frame.height then 0 else 2) ∧
          fixups.val = frame.fixups.val ++ [site] := by
  by_cases elided : frame.results = 0#u32 ∨ source = frame.height
  · have effect := branch_if_elided_forward_success ops law compiler frame index depth source condition lookup
      position forward elided sourcePosition conditionAt after accepted
    obtain ⟨code, fixups, site, sitePosition, frames, appended⟩ := effect
    refine ⟨fixups, frames, ?_, ?_, ?_⟩
    · simp only [ConditionalHole, if_pos elided]
      exact ⟨site, by simp [appended], sitePosition, by simp [code], by simpa [elided] using resumePosition⟩
    · simpa [branchIfInstructions, elided] using code
    · exact ⟨site, by simpa [elided] using sitePosition, appended⟩
  · have nonempty : frame.results ≠ 0#u32 := fun eq => elided (Or.inl eq)
    have different : source ≠ frame.height := fun eq => elided (Or.inr eq)
    have effect := branch_if_transfer_forward_success ops law compiler frame index depth source condition resume lookup
      position forward nonempty different sourcePosition conditionAt (by simpa [elided] using resumePosition)
      after accepted
    obtain ⟨code, fixups, site, sitePosition, frames, appended⟩ := effect
    refine ⟨fixups, frames, ?_, ?_, ?_⟩
    · simp only [ConditionalHole, if_neg elided]
      refine ⟨by simp [code], ?_, by simp [code], site, by simp [appended], sitePosition,
        by simp [code], by simpa [elided] using resumePosition⟩
      intro old member
      simp only [appended, List.mem_append, List.mem_singleton] at member
      rcases member with prior | rfl
      · have bound := fixupsBefore old prior
        omega
      · omega
    · simpa [branchIfInstructions, elided] using code
    · exact ⟨site, by simpa [elided] using sitePosition, appended⟩


theorem compiler_branch_if_loop_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop)
    (sourcePosition : source.val + frame.params.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (resumePosition : resume.val = compiler.function.code.val.length +
      (if frame.params = 0#u32 ∨ source = frame.height then 1 else 3))
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true = .ok (.Ok (), after)) :
    after.function.code.val = compiler.function.code.val ++
      branchIfInstructions frame.height source frame.params frame.start_pc condition resume ∧
    after.frames = compiler.frames := by
  by_cases elided : frame.params = 0#u32 ∨ source = frame.height
  · have effect := branch_if_elided_loop_success ops law compiler frame index depth source condition lookup
      position kind elided sourcePosition conditionAt after accepted
    simpa [branchIfInstructions, elided] using effect
  · have nonempty : frame.params ≠ 0#u32 := fun eq => elided (Or.inl eq)
    have different : source ≠ frame.height := fun eq => elided (Or.inr eq)
    have effect := branch_if_transfer_loop_success ops law compiler frame index depth source condition resume lookup
      position kind nonempty different sourcePosition conditionAt (by simpa [elided] using resumePosition) after accepted
    simpa [branchIfInstructions, elided] using effect

theorem callback_branch_if_forward_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (resultType : Itasca.signature.ResultType)
    (reachable : compiler.reachable = true)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val + frame.results.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (resumePosition : resume.val = compiler.function.code.val.length +
      (if frame.results = 0#u32 ∨ source = frame.height then 1 else 3))
    (fixupsBefore : ∀ site, site ∈ frame.fixups.val → site.val < compiler.function.code.val.length)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops compiler state depth resultType = .ok (.Ok (), after)) : ∃ fixups,
        after.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
        ConditionalHole after.function.code.val fixups.val compiler.function.code.val.length
          frame.height source frame.results condition resume ∧
        after.function.code.val = compiler.function.code.val ++
          branchIfInstructions frame.height source frame.results core.num.U32.MAX condition resume ∧
        ∃ site, site.val = compiler.function.code.val.length +
          (if frame.results = 0#u32 ∨ source = frame.height then 0 else 2) ∧
          fixups.val = frame.fixups.val ++ [site] := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at accepted
  rw [if_pos reachable] at accepted
  obtain ⟨⟨result, changed⟩, branchCall, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    cases value
    have effect := compiler_branch_if_forward_success ops law compiler frame index depth source condition resume
      lookup position forward sourcePosition conditionAt resumePosition fixupsBefore changed branchCall
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    have observed := compiler_observe ops law changed state
    rw [rest, WP.spec_ok] at observed
    dsimp only at observed
    obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed rfl
    obtain ⟨fixups, frames, hole, code, site⟩ := effect
    exact ⟨fixups, by simpa [hframes] using frames, by simpa [hcode] using hole,
      by simpa [hcode] using code, site⟩

theorem callback_branch_if_loop_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (resultType : Itasca.signature.ResultType)
    (reachable : compiler.reachable = true)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop)
    (sourcePosition : source.val + frame.params.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (resumePosition : resume.val = compiler.function.code.val.length +
      (if frame.params = 0#u32 ∨ source = frame.height then 1 else 3))
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops compiler state depth resultType = .ok (.Ok (), after)) :
    after.function.code.val = compiler.function.code.val ++
      branchIfInstructions frame.height source frame.params frame.start_pc condition resume ∧
    after.frames = compiler.frames := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at accepted
  rw [if_pos reachable] at accepted
  obtain ⟨⟨result, changed⟩, branchCall, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    cases value
    have effect := compiler_branch_if_loop_success ops law compiler frame index depth source condition resume
      lookup position kind sourcePosition conditionAt resumePosition changed branchCall
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    have observed := compiler_observe ops law changed state
    rw [rest, WP.spec_ok] at observed
    dsimp only at observed
    obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed rfl
    obtain ⟨code, frames⟩ := effect
    exact ⟨by simpa [hcode] using code, by simpa [hframes] using frames⟩

end Itasca.Runtime.Code
