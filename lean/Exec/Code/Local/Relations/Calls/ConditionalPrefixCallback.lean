import Exec.Code.Local.Relations.Common.ConditionalCertificates
import Exec.Code.Local.Relations.Common.ResolvedConditionalPrefix
namespace Exec.Code
open Aeneas Aeneas.Std

/-- The actual BR_IF callback extends the source prefix to its false-edge
continuation, while retaining the exact selected-label fixup for the true edge. -/
@[step] theorem callback_branch_if_forward_prefix {A : Type} (ops : runtime.platform.Alloc A)
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
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (types functions : List functype) (returns locals initial stack : List valtype)
    (labels : List LabelTarget) (label : LabelTarget) (before after : List FixupTarget)
    (target : U32) (prior : List instr) (start : Nat)
    (labelAt : labels[depth.val]? = some label) (live : label.branchLive = true)
    (labelTarget : label.target = target)
    (layout : BranchLayout locals stack label frame.height source frame.results)
    (conditionSlot : condition.val = slots locals + slots stack)
    (inside : FixupsInside (before ++ ⟨frame.fixups.val, target⟩ :: after) compiler.function.code.val.length)
    (prefixCode : CodePrefix types functions returns locals
      (resolvedCode compiler.function.code.val (before ++ ⟨frame.fixups.val, target⟩ :: after))
      labels initial prior start compiler.function.code.val.length (stack ++ [.I32])) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops compiler state depth resultType ⦃ out =>
      out.1 = .Ok () → ∃ fixups,
        out.2.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
        CodePrefix types functions returns locals
          (resolvedCode out.2.function.code.val (before ++ ⟨fixups.val, target⟩ :: after))
          labels initial (prior ++ [.BR_IF (.mk_uN depth.val)]) start
          resume.val stack ⦄ := by
  apply WP.spec_mono (callback_branch_if_forward ops law compiler state resultType reachable frame index depth source condition resume
    lookup position forward sourcePosition conditionAt resumePosition fixupsBefore fixupsFit codeFits offsetsFit coordinateFits)
  intro out effect accepted
  obtain ⟨fixups, frames, hole, code, site, sitePosition, appended⟩ := effect accepted
  refine ⟨fixups, frames, ?_⟩
  rw [code, appended]
  exact prefixCode.resolved_branchIf inside sitePosition resumePosition labelAt live labelTarget layout conditionSlot

end Exec.Code
