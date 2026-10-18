import Exec.Code.Local.Relations.Table.BranchTableSkipForward
import Exec.Code.Local.Relations.Table.BranchTableSkipLoop
namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
theorem compiler_branch_forward_skip_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val + frame.results.val + skip.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false = .ok (.Ok (), after)) : ∃ fixups,
        after.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
        BranchHole after.function.code.val fixups.val compiler.function.code.val.length
          frame.height source frame.results ∧
        after.function.code.val = compiler.function.code.val ++
          branchInstructions frame.height source frame.results core.num.U32.MAX ∧
        ∃ site, site.val = compiler.function.code.val.length +
          (if frame.results = 0#u32 ∨ source = frame.height then 0 else 1) ∧
          fixups.val = frame.fixups.val ++ [site] := by
  by_cases elided : frame.results = 0#u32 ∨ source = frame.height
  · have effect := branch_elided_forward_skip_success ops law compiler frame index depth source skip lookup
      position forward elided sourcePosition after accepted
    obtain ⟨code, fixups, site, position, frames, appended⟩ := effect
    refine ⟨fixups, frames, ?_, ?_, ?_⟩
    · simp only [BranchHole, if_pos elided]
      exact ⟨site, by simp [appended], position, by simp [code, core.num.U32.MAX, U32.rMax]⟩
    · simpa [branchInstructions, elided] using code
    · exact ⟨site, by simpa [elided] using position, appended⟩
  · have nonempty : frame.results ≠ 0#u32 := fun eq => elided (Or.inl eq)
    have different : source ≠ frame.height := fun eq => elided (Or.inr eq)
    have effect := branch_transfer_forward_skip_success ops law compiler frame index depth source skip lookup
      position forward nonempty different sourcePosition after accepted
    obtain ⟨code, fixups, site, position, frames, appended⟩ := effect
    refine ⟨fixups, frames, ?_, ?_, ?_⟩
    · simp only [BranchHole, if_neg elided]
      exact ⟨by simp [code], site, by simp [appended], position, by simp [code, core.num.U32.MAX, U32.rMax]⟩
    · simpa [branchInstructions, elided] using code
    · exact ⟨site, by simpa [elided] using position, appended⟩

theorem compiler_branch_loop_skip_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source skip : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop)
    (sourcePosition : source.val + frame.params.val + skip.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth skip false = .ok (.Ok (), after)) :
        after.function.code.val = compiler.function.code.val ++
          branchInstructions frame.height source frame.params frame.start_pc ∧
        after.frames = compiler.frames := by
  by_cases elided : frame.params = 0#u32 ∨ source = frame.height
  · have effect := branch_elided_loop_skip_success ops law compiler frame index depth source skip lookup
      position kind elided sourcePosition after accepted
    simpa [branchInstructions, elided] using effect
  · have nonempty : frame.params ≠ 0#u32 := fun eq => elided (Or.inl eq)
    have different : source ≠ frame.height := fun eq => elided (Or.inr eq)
    have effect := branch_transfer_loop_skip_success ops law compiler frame index depth source skip lookup
      position kind nonempty different sourcePosition after accepted
    simpa [branchInstructions, elided] using effect
end Exec.Code
