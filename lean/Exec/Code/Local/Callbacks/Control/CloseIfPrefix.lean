import Exec.Code.Local.Callbacks.Control.CloseGuardedScope
import Exec.Code.Local.Relations.Control.IfEndPrefix
import Exec.Code.Local.Relations.Common.SuspendedPrefix
import Exec.Code.Local.Relations.Common.ResolvedPrefix
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Actual END of an IF with no ELSE resolves both the guard and the body
branches at the shared exit. The implicit arm is the identity on parameters. -/
@[step] theorem close_if_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (kind : frame.kind = .Then) (entered : frame.entry_reachable = true)
    (guard : Usize) (condition old : U32) (hasIf : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (types functions : List functype) (returns locals : List valtype) (labels : List LabelTarget)
    (groups : List FixupTarget) (initial front params : List valtype)
    (prior body : List instr) (bt : blocktype) (parentStart : Nat)
    (signature : BlockSignature types bt params params)
    (conditionSlot : condition.val = slots locals + slots (front ++ params))
    (parent : SuspendedPrefix types functions returns locals
      (resolvedCode compiler.function.code.val (⟨[guard], target⟩ :: ⟨frame.fixups.val, target⟩ :: groups))
      labels initial prior parentStart guard.val (front ++ params ++ [.I32]))
    (guardResolved : (resolvedCode compiler.function.code.val
      (⟨[guard], target⟩ :: ⟨frame.fixups.val, target⟩ :: groups))[guard.val]? =
        some (.JumpIfZero condition target))
    (bodyCode : CodeRel types functions returns locals
      (resolvedCode compiler.function.code.val (⟨[guard], target⟩ :: ⟨frame.fixups.val, target⟩ :: groups))
      (⟨front, params, params, target, target.val, [], [], compiler.reachable, frame.end_reachable⟩ :: labels)
      (front ++ params) body (guard.val + 1) target.val (front ++ params)) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () → out.2.frames = rest ∧ out.2.reachable = true ∧
        CodePrefix types functions returns locals (resolvedCode out.2.function.code.val groups)
          labels initial (prior ++ [.IFELSE bt body []]) parentStart target.val (front ++ params) ⦄ := by
  apply WP.spec_mono (close_guarded_scope_effect ops law compiler state frame rest target frames
    guard condition old (by simp [kind]) hasIf guardCode position branches mapFits coordinateFits)
  intro out effect accepted
  obtain ⟨popped, reachable, code, control⟩ := effect accepted
  have restored : out.2.reachable = true := by
    simpa [scopeExitLive, kind, entered] using reachable
  have resolved : resolvedCode out.2.function.code.val groups =
      resolvedCode compiler.function.code.val (⟨[guard], target⟩ :: ⟨frame.fixups.val, target⟩ :: groups) := by
    simp only [code, resolvedCode, patchCode, guardCode, retarget]
  refine ⟨popped, restored, ?_⟩
  rw [resolved]
  exact parent.resume (CodePrefix.ifEnd signature conditionSlot guardResolved bodyCode)

end Exec.Code
