import Exec.Code.Local.Callbacks.Control.CloseScope
import Exec.Code.Local.Relations.Control.PrefixControl
import Exec.Code.Local.Relations.Common.SuspendedPrefix
import Exec.Code.Local.Relations.Common.ResolvedPrefix
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Actual block END closes the source zipper: its physical fixup pass removes
the innermost resolution group, then the saved parent consumes the complete
block certificate, preserving dead suffix elision when both exits are dead. -/
@[step] theorem close_block_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (kind : frame.kind = .Block) (noIf : frame.if_pc = none)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (types functions : List functype) (returns locals : List valtype) (labels : List LabelTarget)
    (groups : List FixupTarget) (initial front params results : List valtype)
    (prior body : List instr) (bt : blocktype) (parentStart bodyStart : Nat)
    (signature : BlockSignature types bt params results)
    (parent : SuspendedPrefix types functions returns locals
      (resolvedCode compiler.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
      labels initial prior parentStart bodyStart (front ++ params))
    (bodyCode : CodeRel types functions returns locals
      (resolvedCode compiler.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
      (⟨front, results, results, target, target.val, [], [], compiler.reachable, frame.end_reachable⟩ :: labels)
      (front ++ params) body bodyStart target.val (front ++ results)) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () → out.2.frames = rest ∧
        out.2.reachable = (compiler.reachable || frame.end_reachable) ∧
        (if out.2.reachable then
          CodePrefix types functions returns locals (resolvedCode out.2.function.code.val groups)
            labels initial (prior ++ [.BLOCK bt body]) parentStart target.val (front ++ results)
        else DeadCodePrefix types functions returns locals (resolvedCode out.2.function.code.val groups)
            labels initial (prior ++ [.BLOCK bt body]) parentStart target.val) ⦄ := by
  apply WP.spec_mono (close_scope_effect ops law compiler state frame rest target frames
    (by simp [kind]) noIf position branches mapFits coordinateFits)
  intro out effect accepted
  obtain ⟨popped, reachable, code, control⟩ := effect accepted
  have restored : out.2.reachable = (compiler.reachable || frame.end_reachable) := by
    simpa [scopeExitLive, kind] using reachable
  have resolved : resolvedCode out.2.function.code.val groups =
      resolvedCode compiler.function.code.val (⟨frame.fixups.val, target⟩ :: groups) := by
    simp only [code, resolvedCode]
  refine ⟨popped, restored, ?_⟩
  rw [resolved]
  split
  · exact parent.resume (CodePrefix.block signature bodyCode)
  · rename_i dead
    have normalDead : compiler.reachable = false := by
      cases live : compiler.reachable <;> simp_all
    have branchDead : frame.end_reachable = false := by
      cases live : frame.end_reachable <;> simp_all
    apply parent.resume_dead (DeadCodePrefix.block signature ?_)
    simpa only [normalDead, branchDead] using bodyCode

@[step] theorem close_loop_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (kind : frame.kind = .Loop) (noIf : frame.if_pc = none)
    (noBranchExit : frame.end_reachable = false)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (types functions : List functype) (returns locals : List valtype) (labels : List LabelTarget)
    (groups : List FixupTarget) (initial front params results : List valtype)
    (prior body : List instr) (bt : blocktype) (parentStart : Nat) (entry : U32)
    (signature : BlockSignature types bt params results)
    (head : (resolvedCode compiler.function.code.val (⟨frame.fixups.val, target⟩ :: groups))[entry.val]? = some .LoopHead)
    (parent : SuspendedPrefix types functions returns locals
      (resolvedCode compiler.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
      labels initial prior parentStart entry.val (front ++ params))
    (bodyCode : CodeRel types functions returns locals
      (resolvedCode compiler.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
      (⟨front, params, results, entry, target.val, [.LOOP bt body], [], compiler.reachable, true⟩ :: labels)
      (front ++ params) body (entry.val + 1) target.val (front ++ results)) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () → out.2.frames = rest ∧
        out.2.reachable = compiler.reachable ∧
        (if out.2.reachable then
          CodePrefix types functions returns locals (resolvedCode out.2.function.code.val groups)
            labels initial (prior ++ [.LOOP bt body]) parentStart target.val (front ++ results)
        else DeadCodePrefix types functions returns locals (resolvedCode out.2.function.code.val groups)
            labels initial (prior ++ [.LOOP bt body]) parentStart target.val) ⦄ := by
  apply WP.spec_mono (close_scope_effect ops law compiler state frame rest target frames
    (by simp [kind]) noIf position branches mapFits coordinateFits)
  intro out effect accepted
  obtain ⟨popped, reachable, code, control⟩ := effect accepted
  have restored : out.2.reachable = compiler.reachable := by
    simpa [scopeExitLive, kind, noBranchExit] using reachable
  have resolved : resolvedCode out.2.function.code.val groups =
      resolvedCode compiler.function.code.val (⟨frame.fixups.val, target⟩ :: groups) := by
    simp only [code, resolvedCode]
  refine ⟨popped, restored, ?_⟩
  rw [resolved]
  split
  · exact parent.resume (CodePrefix.loop signature head bodyCode)
  · rename_i dead
    have normalDead : compiler.reachable = false := by
      cases live : compiler.reachable <;> simp_all
    apply parent.resume_dead (DeadCodePrefix.loop signature head ?_)
    simpa only [normalDead] using bodyCode

end Exec.Code
