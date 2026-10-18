import Exec.Code.Local.Lowering.Control.LoweringLoopBranch
import Exec.Code.Local.Relations.Common.Prefix
import Exec.Code.Local.Relations.Common.ResolvedPrefix
namespace Exec.Code
open Aeneas Aeneas.Std

@[step] theorem callback_branch_loop_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (resultType : Itasca.signature.ResultType)
    (reachable : compiler.reachable = true)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop)
    (sourcePosition : source.val + frame.params.val = compiler.height.val)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (types functions : List functype) (returns locals initial stack : List valtype)
    (labels : List LabelTarget) (label : LabelTarget) (groups : List FixupTarget)
    (prior : List instr) (start : Nat)
    (labelAt : labels[depth.val]? = some label) (live : label.branchLive = true)
    (labelTarget : label.target = frame.start_pc)
    (layout : BranchLayout locals stack label frame.height source frame.params)
    (inside : FixupsInside groups compiler.function.code.val.length)
    (prefixCode : CodePrefix types functions returns locals
      (resolvedCode compiler.function.code.val groups)
      labels initial prior start compiler.function.code.val.length stack) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops compiler state depth resultType ⦃ out =>
      out.1 = .Ok () → out.2.reachable = false ∧ out.2.frames = compiler.frames ∧
        DeadCodePrefix types functions returns locals (resolvedCode out.2.function.code.val groups)
          labels initial (prior ++ [.BR (.mk_uN depth.val)]) start out.2.function.code.val.length ⦄ := by
  apply WP.spec_mono (callback_branch_loop ops law compiler state resultType reachable frame index depth source
    lookup position kind sourcePosition codeFits offsetsFit coordinateFits)
  intro out effect accepted
  obtain ⟨dead, code, frames⟩ := effect accepted
  refine ⟨dead, frames, ?_⟩
  rw [code, resolvedCode_append_code _ _ _ inside]
  apply (prefixCode.extend _).terminal
  apply DeadCodePrefix.branch labelAt live layout
  refine ⟨resolvedCode compiler.function.code.val groups, [], ?_, resolvedCode_length _ _, ?_⟩
  · simp [labelTarget]
  · simp [labelTarget]

end Exec.Code
