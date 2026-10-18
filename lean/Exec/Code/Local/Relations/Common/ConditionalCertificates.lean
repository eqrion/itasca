import Exec.Code.Local.Lowering.Common.LoweringConditionalTransfer
namespace Exec.Code
open Aeneas Aeneas.Std

/-- A forward conditional branch keeps its false-edge resume distinct from
the fixups for its selected source label. -/
def ConditionalHole (code : List Bytecode) (sites : List Usize)
    (pc : Nat) (dst src count cond resume : U32) : Prop :=
  if count = 0#u32 ∨ src = dst then
    ∃ site, site ∈ sites ∧ site.val = pc ∧
      code[pc]? = some (.JumpIfNonZero cond core.num.U32.MAX) ∧ resume.val = pc + 1
  else
    code[pc]? = some (.JumpIfZero cond resume) ∧
    (∀ site, site ∈ sites → pc ≠ site.val) ∧
    code[pc + 1]? = some (transferInstruction dst src count) ∧
    ∃ site, site ∈ sites ∧ site.val = pc + 2 ∧
      code[pc + 2]? = some (.Jump core.num.U32.MAX) ∧ resume.val = pc + 3

theorem ConditionalHole.resolve {code sites pc dst src count cond resume}
    (hole : ConditionalHole code sites pc dst src count cond resume) (target : U32) :
    Segment (patchCode code sites target) pc
      (branchIfInstructions dst src count target cond resume) resume.val := by
  by_cases empty : count = 0#u32 ∨ src = dst
  · simp only [ConditionalHole, if_pos empty] at hole
    obtain ⟨site, member, position, fetched, next⟩ := hole
    have patched := patchCode_target code sites target core.num.U32.MAX site (.nonzero cond) member
      (by simpa [position, BranchKind.instruction] using fetched)
    simp only [branchIfInstructions, if_pos empty, next]
    exact Segment.single (by simpa [position, BranchKind.instruction] using patched)
  · simp only [ConditionalHole, if_neg empty] at hole
    obtain ⟨guard, separate, copied, site, member, position, fetched, next⟩ := hole
    have guardPreserved := (patchCode_other code sites target pc separate).trans guard
    have copyFixed : retarget (transferInstruction dst src count) target = transferInstruction dst src count := by
      unfold transferInstruction
      split <;> first | rfl | split <;> rfl
    have copyPreserved := patchCode_fixed code sites target (pc + 1) _ copyFixed copied
    have patched := patchCode_target code sites target core.num.U32.MAX site .jump member
      (by simpa [position, BranchKind.instruction] using fetched)
    have first := Segment.single guardPreserved
    have second := Segment.single copyPreserved
    have third := Segment.single (by simpa [position, BranchKind.instruction] using patched)
    have together := first.append (second.append (by simpa [Nat.add_assoc] using third))
    simpa [branchIfInstructions, empty, next, Nat.add_assoc] using together

@[step] theorem compiler_branch_if_forward {A : Type} (ops : runtime.platform.Alloc A)
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
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 3 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 3 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true ⦃ out =>
      out.1 = .Ok () → ∃ fixups,
        out.2.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
        ConditionalHole out.2.function.code.val fixups.val compiler.function.code.val.length
          frame.height source frame.results condition resume ∧
        out.2.function.code.val = compiler.function.code.val ++
          branchIfInstructions frame.height source frame.results core.num.U32.MAX condition resume ∧
        ∃ site, site.val = compiler.function.code.val.length +
          (if frame.results = 0#u32 ∨ source = frame.height then 0 else 2) ∧
          fixups.val = frame.fixups.val ++ [site] ⦄ := by
  by_cases elided : frame.results = 0#u32 ∨ source = frame.height
  · apply WP.spec_mono (branch_if_elided_forward ops law compiler frame index depth source condition lookup
      position forward elided sourcePosition conditionAt fixupsFit (by omega) (by omega) coordinateFits)
    intro out effect accepted
    obtain ⟨code, fixups, site, sitePosition, frames, appended⟩ := effect accepted
    refine ⟨fixups, frames, ?_, ?_, ?_⟩
    · simp only [ConditionalHole, if_pos elided]
      exact ⟨site, by simp [appended], sitePosition, by simp [code], by simpa [elided] using resumePosition⟩
    · simpa [branchIfInstructions, elided] using code
    · exact ⟨site, by simpa [elided] using sitePosition, appended⟩
  · have nonempty : frame.results ≠ 0#u32 := fun eq => elided (Or.inl eq)
    have different : source ≠ frame.height := fun eq => elided (Or.inr eq)
    apply WP.spec_mono (branch_if_transfer_forward ops law compiler frame index depth source condition resume lookup
      position forward nonempty different sourcePosition conditionAt (by simpa [elided] using resumePosition)
      fixupsFit codeFits offsetsFit coordinateFits)
    intro out effect accepted
    obtain ⟨code, fixups, site, sitePosition, frames, appended⟩ := effect accepted
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

@[step] theorem callback_branch_if_forward {A : Type} (ops : runtime.platform.Alloc A)
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
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 3 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 3 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops compiler state depth resultType ⦃ out =>
      out.1 = .Ok () → ∃ fixups,
        out.2.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
        ConditionalHole out.2.function.code.val fixups.val compiler.function.code.val.length
          frame.height source frame.results condition resume ∧
        out.2.function.code.val = compiler.function.code.val ++
          branchIfInstructions frame.height source frame.results core.num.U32.MAX condition resume ∧
        ∃ site, site.val = compiler.function.code.val.length +
          (if frame.results = 0#u32 ∨ source = frame.height then 0 else 2) ∧
          fixups.val = frame.fixups.val ++ [site] ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
  rw [if_pos reachable]
  step with compiler_branch_if_forward ops law compiler frame index depth source condition resume
    lookup position forward sourcePosition conditionAt resumePosition fixupsBefore fixupsFit codeFits offsetsFit coordinateFits
    as ⟨result, changed, effect⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    cases value
    obtain ⟨fixups, frames, hole, code, site⟩ := effect rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with compiler_observe ops law changed state as ⟨out, observed, accepted⟩
    obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed accepted
    exact ⟨fixups, by simpa [hframes] using frames, by simpa [hcode] using hole,
      by simpa [hcode] using code, site⟩

end Exec.Code
