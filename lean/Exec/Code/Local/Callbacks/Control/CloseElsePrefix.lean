import Exec.Code.Local.Callbacks.Control.CloseScope
import Exec.Code.Local.Relations.Control.PrefixControl
import Exec.Code.Local.Relations.Common.SuspendedPrefix
import Exec.Code.Local.Relations.Common.ResolvedPrefix
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Closing an explicit ELSE resolves the common exit and plugs both completed
arms into the saved enclosing prefix. Dead arms preserve omitted source tails. -/
@[step] theorem close_else_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (kind : frame.kind = .Else) (noIf : frame.if_pc = none)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (types functions : List functype) (returns locals : List valtype) (labels : List LabelTarget)
    (groups : List FixupTarget) (initial front params results : List valtype)
    (prior yes no : List instr) (bt : blocktype) (parentStart pc yesExit : Nat)
    (noEntry condition : U32) (yesNormal yesBranch noBranch : Bool)
    (branchFlags : frame.end_reachable = (yesNormal || yesBranch || noBranch))
    (signature : BlockSignature types bt params results)
    (conditionSlot : condition.val = slots locals + slots (front ++ params))
    (parent : SuspendedPrefix types functions returns locals
      (resolvedCode compiler.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
      labels initial prior parentStart pc (front ++ params ++ [.I32]))
    (guard : (resolvedCode compiler.function.code.val (⟨frame.fixups.val, target⟩ :: groups))[pc]? =
        some (.JumpIfZero condition noEntry))
    (yesCode : CodeRel types functions returns locals
      (resolvedCode compiler.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
      (⟨front, results, results, target, yesExit, [], [], yesNormal, yesBranch⟩ :: labels)
      (front ++ params) yes (pc + 1) yesExit (front ++ results))
    (skip : Segment (resolvedCode compiler.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
      yesExit (if yesNormal then [.Jump target] else []) noEntry.val)
    (noCode : CodeRel types functions returns locals
      (resolvedCode compiler.function.code.val (⟨frame.fixups.val, target⟩ :: groups))
      (⟨front, results, results, target, target.val, [], [], compiler.reachable, noBranch⟩ :: labels)
      (front ++ params) no noEntry.val target.val (front ++ results)) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () → out.2.frames = rest ∧
        out.2.reachable = (yesNormal || yesBranch || compiler.reachable || noBranch) ∧
        (if out.2.reachable then
          CodePrefix types functions returns locals (resolvedCode out.2.function.code.val groups)
            labels initial (prior ++ [.IFELSE bt yes no]) parentStart target.val (front ++ results)
        else DeadCodePrefix types functions returns locals (resolvedCode out.2.function.code.val groups)
            labels initial (prior ++ [.IFELSE bt yes no]) parentStart target.val) ⦄ := by
  apply WP.spec_mono (close_scope_effect ops law compiler state frame rest target frames
    (by simp [kind]) noIf position branches mapFits coordinateFits)
  intro out effect accepted
  obtain ⟨popped, reachable, code, control⟩ := effect accepted
  have restored : out.2.reachable = (yesNormal || yesBranch || compiler.reachable || noBranch) := by
    simpa [scopeExitLive, kind, branchFlags, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm] using reachable
  have resolved : resolvedCode out.2.function.code.val groups =
      resolvedCode compiler.function.code.val (⟨frame.fixups.val, target⟩ :: groups) := by
    simp only [code, resolvedCode]
  refine ⟨popped, restored, ?_⟩
  rw [resolved]
  split
  · exact parent.resume (CodePrefix.ifElse signature conditionSlot guard yesCode (.emitted skip) noCode)
  · rename_i dead
    have flags : yesNormal = false ∧ yesBranch = false ∧ compiler.reachable = false ∧ noBranch = false := by
      rw [restored] at dead
      simpa only [Bool.or_eq_true, not_or, Bool.not_eq_true, and_assoc] using dead
    obtain ⟨yn, yb, nn, nb⟩ := flags
    apply parent.resume_dead (DeadCodePrefix.ifElse (yesExit := yesExit) signature conditionSlot guard ?_ ?_ ?_)
    · simpa only [yn, yb] using yesCode
    · simpa only [yn, Bool.false_eq_true, ite_false] using skip
    · simpa only [nn, nb] using noCode

end Exec.Code
