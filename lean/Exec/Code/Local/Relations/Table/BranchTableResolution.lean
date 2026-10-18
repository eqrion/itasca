import Exec.Code.Local.Relations.Table.BranchTableSites
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Resolve one physical table arm under any admissible completion plan. The
plan is rewound without adding a synthetic source BR instruction. -/
theorem TableTargetCode.resolve {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    (effect : TableTargetCode before after depth) (locals : List valtype)
    (labels : List LabelTarget) (groups : List FixupTarget)
    (sites : ∀ frame ∈ before.frames.val, FrameSites before.function.code.val frame)
    (plans : FramePlans after.function.code.val.length locals after.frames.val labels groups) :
    ∃ previous label guard frame source index,
      FramePlans before.function.code.val.length locals before.frames.val labels previous ∧
      labels[depth.val]? = some label ∧ label.branchLive = true ∧
      before.frames.val[index]? = some frame ∧ index + depth.val + 1 = before.frames.val.length ∧
      FrameFuture before.function.code.val.length locals frame label guard ∧
      source.val + (frameBranchWidth frame).val + 1 = before.height.val ∧
      resolvedCode after.function.code.val groups = resolvedCode before.function.code.val previous ++
        branchInstructions frame.height source (frameBranchWidth frame) label.target := by
  obtain ⟨fragment,codeSuffix,_⟩ := effect.code_prefix
  have order : before.function.code.val.length ≤ after.function.code.val.length := by
    simp only [codeSuffix,List.length_append]
    omega
  cases effect with
  | loop index frame source lookup position kind operands code frames =>
    have prior : FramePlans before.function.code.val.length locals before.frames.val labels groups := by
      rw [← frames]
      exact plans.before order
    obtain ⟨label,guard,labelAt,future⟩ := prior.lookup lookup position
    refine ⟨groups,label,guard,frame,source,index.val,prior,labelAt,future.loopLive kind,
      lookup,position,future,?_,?_⟩
    · simpa only [frameBranchWidth,kind] using operands
    · rw [code,resolvedCode_append_code _ _ _ (prior.inside sites),future.loopTarget kind]
      simp only [frameBranchWidth,kind]
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    obtain ⟨label,earlier,later,labelAt,live,previous,grouped⟩ := plans.before_mark fixups frames lookup position
    have prior := previous.before order
    obtain ⟨sameLabel,guard,sameAt,future⟩ := prior.lookup lookup position
    have labelEq : sameLabel = label := Option.some.inj (sameAt.symm.trans labelAt)
    subst sameLabel
    have width : frameBranchWidth frame = frame.results := by
      cases equation : frame.kind <;> simp_all [frameBranchWidth]
    refine ⟨_,label,guard,frame,source,index.val,prior,labelAt,live,lookup,position,future,?_,?_⟩
    · simpa only [width] using operands
    · rw [code,grouped,appended,width]
      exact resolvedCode_new_br before.function.code.val earlier later ⟨frame.fixups.val,label.target⟩
        frame.height source frame.results core.num.U32.MAX site sitePosition (prior.inside sites)
end Exec.Code
