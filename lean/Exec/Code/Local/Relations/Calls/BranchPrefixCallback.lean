import Exec.Code.Local.Lowering.Control.LoweringForwardBranch
import Exec.Code.Local.Relations.Control.ResolvedBranchPrefix
namespace Exec.Code
open Aeneas Aeneas.Std

/-- The actual BR callback updates its selected physical frame and closes the
retained resolved source prefix. All earlier open fixups stay in their groups. -/
@[step] theorem callback_branch_forward_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (resultType : Itasca.signature.ResultType)
    (reachable : compiler.reachable = true)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val + frame.results.val = compiler.height.val)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (types functions : List functype) (returns locals initial stack : List valtype)
    (labels : List LabelTarget) (label : LabelTarget) (before after : List FixupTarget)
    (target : U32) (prior : List instr) (start : Nat)
    (labelAt : labels[depth.val]? = some label) (live : label.branchLive = true)
    (labelTarget : label.target = target)
    (layout : BranchLayout locals stack label frame.height source frame.results)
    (inside : FixupsInside (before ++ ⟨frame.fixups.val, target⟩ :: after) compiler.function.code.val.length)
    (prefixCode : CodePrefix types functions returns locals
      (resolvedCode compiler.function.code.val (before ++ ⟨frame.fixups.val, target⟩ :: after))
      labels initial prior start compiler.function.code.val.length stack) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops compiler state depth resultType ⦃ out =>
      out.1 = .Ok () → out.2.reachable = false ∧ ∃ fixups,
        out.2.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
        DeadCodePrefix types functions returns locals
          (resolvedCode out.2.function.code.val (before ++ ⟨fixups.val, target⟩ :: after))
          labels initial (prior ++ [.BR (.mk_uN depth.val)]) start
          (compiler.function.code.val.length + (branchInstructions frame.height source frame.results target).length) ⦄ := by
  apply WP.spec_mono (callback_branch_forward ops law compiler state resultType reachable frame index depth source
    lookup position forward sourcePosition fixupsFit codeFits offsetsFit coordinateFits)
  intro out effect accepted
  obtain ⟨dead, fixups, frames, hole, code, site, sitePosition, appended⟩ := effect accepted
  refine ⟨dead, fixups, frames, ?_⟩
  rw [code, appended]
  exact prefixCode.resolved_branch inside sitePosition labelAt live labelTarget layout

end Exec.Code
