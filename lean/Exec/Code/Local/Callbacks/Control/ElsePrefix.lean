import Exec.Code.Local.Callbacks.Control.EnterElse
import Exec.Code.Local.Callbacks.Common.OpenPrefix
import Exec.Code.Local.Relations.Common.PrefixClose
namespace Exec.Code
open Aeneas Aeneas.Std

theorem resolvedCode_guard_set (code : List Bytecode) (groups : List FixupTarget)
    (guard : Usize) (condition old target : U32)
    (found : code[guard.val]? = some (.JumpIfZero condition old)) :
    resolvedCode (code.set guard.val (.JumpIfZero condition target)) groups =
      resolvedCode code (⟨[guard], target⟩ :: groups) := by
  simp only [resolvedCode, patchCode, found, retarget]

/-- The actual ELSE update resolves its guard and appends one forward skip.
The resolved view of the completed then body is preserved as an exact prefix. -/
theorem resolvedCode_else_live (code : List Bytecode) (groups : List FixupTarget)
    (fixups : List Usize) (guard site : Usize) (condition old noEntry exit : U32)
    (found : code[guard.val]? = some (.JumpIfZero condition old))
    (position : site.val = code.length)
    (inside : FixupsInside (⟨fixups, exit⟩ :: groups) code.length) :
    resolvedCode ((code ++ [runtime.bytecode.Instr.Jump core.num.U32.MAX]).set guard.val (.JumpIfZero condition noEntry))
      (⟨fixups ++ [site], exit⟩ :: groups) =
      resolvedCode code (⟨[guard], noEntry⟩ :: ⟨fixups, exit⟩ :: groups) ++ [.Jump exit] := by
  have guardBound := (List.getElem?_eq_some_iff.mp found).1
  rw [List.set_append_left guard.val _ guardBound]
  have inside' : FixupsInside ([] ++ ⟨fixups, exit⟩ :: groups)
      (code.set guard.val (.JumpIfZero condition noEntry)).length := by
    simpa using inside
  have eq := resolvedCode_new_branch (code.set guard.val (.JumpIfZero condition noEntry)) [] [] groups
    ⟨fixups, exit⟩ .jump core.num.U32.MAX site (by simpa using position) inside'
  simpa only [List.append_nil, List.nil_append, BranchKind.instruction,
    resolvedCode_guard_set code (⟨fixups, exit⟩ :: groups) guard condition old noEntry found] using eq


/-- The actual live ELSE callback freezes the completed then prefix, emits its
skip, and opens the empty else prefix without changing the saved parent. -/
@[step] theorem else_live_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (guard : Usize) (condition noEntry exit : U32)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = true) (guardPc : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (position : noEntry.val = compiler.function.code.val.length + 1)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (types functions : List functype) (returns locals initial front params results : List valtype)
    (labels : List LabelTarget) (groups : List FixupTarget) (priorSource yes : List instr)
    (start bodyStart : Nat) (yesBranch : Bool)
    (inside : FixupsInside (⟨frame.fixups.val, exit⟩ :: groups) compiler.function.code.val.length)
    (parent : SuspendedPrefix types functions returns locals
      (resolvedCode compiler.function.code.val (⟨[guard], noEntry⟩ :: ⟨frame.fixups.val, exit⟩ :: groups))
      labels initial priorSource start guard.val (front ++ params ++ [.I32]))
    (yesPrefix : CodePrefix types functions returns locals
      (resolvedCode compiler.function.code.val (⟨[guard], noEntry⟩ :: ⟨frame.fixups.val, exit⟩ :: groups))
      (⟨front, results, results, exit, compiler.function.code.val.length, [], [], true, yesBranch⟩ :: labels)
      (front ++ params) yes bodyStart compiler.function.code.val.length (front ++ results)) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () → out.2.reachable = frame.entry_reachable ∧ ∃ fixups,
        fixups.val = frame.fixups.val ++ [alloc.vec.Vec.len compiler.function.code] ∧
        out.2.frames.val = prior ++ [{ frame with kind := .Else, if_pc := none, end_reachable := true, fixups }] ∧
        SuspendedPrefix types functions returns locals
          (resolvedCode out.2.function.code.val (⟨fixups.val, exit⟩ :: groups))
          labels initial priorSource start guard.val (front ++ params ++ [.I32]) ∧
        CodeRel types functions returns locals
          (resolvedCode out.2.function.code.val (⟨fixups.val, exit⟩ :: groups))
          (⟨front, results, results, exit, compiler.function.code.val.length, [], [], true, yesBranch⟩ :: labels)
          (front ++ params) yes bodyStart compiler.function.code.val.length (front ++ results) ∧
        Segment (resolvedCode out.2.function.code.val (⟨fixups.val, exit⟩ :: groups))
          compiler.function.code.val.length [.Jump exit] noEntry.val ∧
        ∀ child : LabelTarget, CodePrefix types functions returns locals
          (resolvedCode out.2.function.code.val (⟨fixups.val, exit⟩ :: groups))
          (child :: labels) (front ++ params) [] noEntry.val noEntry.val (front ++ params) ⦄ := by
  apply WP.spec_mono (compiler_else_live ops law compiler state bt frame prior guard condition noEntry
    frames reachable guardPc guardCode position fixupsFit codeFits offsetsFit coordinateFits)
  intro out effect accepted
  obtain ⟨live, code, fixups, appended, frameEq⟩ := effect accepted
  have resolved : resolvedCode out.2.function.code.val (⟨fixups.val, exit⟩ :: groups) =
      resolvedCode compiler.function.code.val (⟨[guard], noEntry⟩ :: ⟨frame.fixups.val, exit⟩ :: groups) ++ [.Jump exit] := by
    rw [code, appended]
    exact resolvedCode_else_live _ _ _ _ _ _ _ _ _ guardCode rfl inside
  refine ⟨live, fixups, appended, frameEq, ?_, ?_, ?_, ?_⟩
  · rw [resolved]
    exact parent.extend _
  · rw [resolved]
    exact (yesPrefix.finish (by simp [resolvedCode_length]) (NormalLive.cons rfl)).extend _
  · rw [resolved]
    exact ⟨resolvedCode compiler.function.code.val (⟨[guard], noEntry⟩ :: ⟨frame.fixups.val, exit⟩ :: groups), [], by simp, resolvedCode_length _ _, by simpa using position⟩
  · intro child
    exact CodePrefix.empty _ _ _ _ _ _ _ _

/-- A terminal then arm emits no ELSE skip. Its dead prefix is completed at
the retained logical endpoint before the else arm becomes the active prefix. -/
@[step] theorem else_dead_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (guard : Usize) (condition noEntry exit : U32)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = false) (guardPc : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition core.num.U32.MAX))
    (position : noEntry.val = compiler.function.code.val.length)
    (types functions : List functype) (returns locals initial front params results : List valtype)
    (labels : List LabelTarget) (groups : List FixupTarget) (priorSource yes : List instr)
    (start bodyStart : Nat) (yesBranch : Bool)
    (parent : SuspendedPrefix types functions returns locals
      (resolvedCode compiler.function.code.val (⟨[guard], noEntry⟩ :: ⟨frame.fixups.val, exit⟩ :: groups))
      labels initial priorSource start guard.val (front ++ params ++ [.I32]))
    (yesPrefix : DeadCodePrefix types functions returns locals
      (resolvedCode compiler.function.code.val (⟨[guard], noEntry⟩ :: ⟨frame.fixups.val, exit⟩ :: groups))
      (⟨front, results, results, exit, compiler.function.code.val.length, [], [], false, yesBranch⟩ :: labels)
      (front ++ params) yes bodyStart compiler.function.code.val.length) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () → out.2.reachable = frame.entry_reachable ∧
        out.2.frames.val = prior ++ [{ frame with kind := .Else, if_pc := none }] ∧
        SuspendedPrefix types functions returns locals
          (resolvedCode out.2.function.code.val (⟨frame.fixups.val, exit⟩ :: groups))
          labels initial priorSource start guard.val (front ++ params ++ [.I32]) ∧
        CodeRel types functions returns locals
          (resolvedCode out.2.function.code.val (⟨frame.fixups.val, exit⟩ :: groups))
          (⟨front, results, results, exit, compiler.function.code.val.length, [], [], false, yesBranch⟩ :: labels)
          (front ++ params) yes bodyStart compiler.function.code.val.length (front ++ results) ∧
        Segment (resolvedCode out.2.function.code.val (⟨frame.fixups.val, exit⟩ :: groups))
          compiler.function.code.val.length [] noEntry.val ∧
        ∀ child : LabelTarget, CodePrefix types functions returns locals
          (resolvedCode out.2.function.code.val (⟨frame.fixups.val, exit⟩ :: groups))
          (child :: labels) (front ++ params) [] noEntry.val noEntry.val (front ++ params) ⦄ := by
  apply WP.spec_mono (compiler_else_dead ops law compiler state bt frame prior guard condition noEntry
    frames reachable guardPc guardCode position)
  intro out effect accepted
  obtain ⟨live, code, frameEq⟩ := effect accepted
  have resolved : resolvedCode out.2.function.code.val (⟨frame.fixups.val, exit⟩ :: groups) =
      resolvedCode compiler.function.code.val (⟨[guard], noEntry⟩ :: ⟨frame.fixups.val, exit⟩ :: groups) := by
    rw [code]
    exact resolvedCode_guard_set _ _ _ _ _ _ guardCode
  refine ⟨live, frameEq, ?_, ?_, ?_, ?_⟩
  · rw [resolved]
    exact parent
  · rw [resolved]
    exact yesPrefix.finish _ _ (Nat.le_refl _) (by simp [resolvedCode_length])
  · rw [resolved]
    exact ⟨resolvedCode compiler.function.code.val (⟨[guard], noEntry⟩ :: ⟨frame.fixups.val, exit⟩ :: groups), [], by simp, resolvedCode_length _ _, by simpa using position⟩
  · intro child
    exact CodePrefix.empty _ _ _ _ _ _ _ _

end Exec.Code
