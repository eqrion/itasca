import Itasca.Runtime.Compiler.Local.Source.SourceEntryChain
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseScope
import Itasca.Runtime.Compiler.Local.Relations.Control.ResolvedBranchPrefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringTrap
import Itasca.Binary.Wasm1.EncodingUnique
import Itasca.Binary.Wasm2.EncodingUnique

/-!
Sections, each formerly its own module: DormantFrames, ResolvedConditionalPrefix, LabelWiden, ConditionalCertificates, ResolvedLiteral, ConsumedPrefix.
-/

/-! ## DormantFrames -/

section

/-!
Unentered frames cannot acquire live exits or forward-branch fixups.

Main declarations: `DormantFrame` and `DormantFrames`. A direct consumer is `Compiler.Local.Relations.Table.BranchTableScopeFrames`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Unentered frames cannot acquire live exits or forward-branch fixups. -/
def DormantFrame (frame : runtime.compiler.Frame) : Prop :=
  frame.entry_reachable = false → frame.end_reachable = false ∧ frame.fixups.val = []

def DormantFrames (frames : List runtime.compiler.Frame) : Prop :=
  ∀ frame ∈ frames, DormantFrame frame

theorem DormantFrame.entered {frame} (live : frame.entry_reachable = true) : DormantFrame frame := by
  simp [DormantFrame, live]

theorem DormantFrame.fresh {frame} (ends : frame.end_reachable = false) (fixups : frame.fixups.val = []) :
    DormantFrame frame := fun _ => ⟨ends, fixups⟩

theorem DormantFrames.push {frames} (clean : DormantFrames frames) (frame : runtime.compiler.Frame)
    (fresh : DormantFrame frame) : DormantFrames (frames ++ [frame]) := by
  intro other member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact clean other member
  · exact fresh

theorem DormantFrames.pop {frames frame} (clean : DormantFrames (frames ++ [frame])) : DormantFrames frames :=
  fun other member => clean other (List.mem_append_left _ member)

theorem DormantFrames.record_branch {frames} (clean : DormantFrames frames)
    (index : Nat) (frame : runtime.compiler.Frame) (fixups : alloc.vec.Vec Usize)
    (entered : frame.entry_reachable = true) :
    DormantFrames (frames.set index {frame with fixups, end_reachable := true}) := by
  intro other member
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact clean other old
  · exact DormantFrame.entered entered

theorem DormantFrames.replace_last {frames frame} (clean : DormantFrames (frames ++ [frame]))
    (next : runtime.compiler.Frame) (fresh : DormantFrame next) : DormantFrames (frames ++ [next]) :=
  clean.pop.push next fresh

/-- The complete live prefix supplies the selected frame's entry liveness;
therefore adding a branch preserves dormant-frame cleanliness. -/
theorem ScopeFrameStack.record_branch_dormant {A : Type} {locals parents current}
    {compiler : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals compiler parents current)
    (chain : SourceEntryChain parents current) (live : current.entered = true)
    (clean : DormantFrames compiler.frames.val) (index : Nat) (frame : runtime.compiler.Frame)
    (fixups : alloc.vec.Vec Usize) (found : compiler.frames.val[index]? = some frame) :
    DormantFrames (compiler.frames.val.set index {frame with fixups, end_reachable := true}) :=
  clean.record_branch index frame fixups (stack.frame_entered chain live frame (List.mem_of_getElem? found))
theorem ScopeFrameStack.dormant_initial {A : Type} {locals current}
    {compiler : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals compiler [] current)
    (live : current.entered = true) : DormantFrames compiler.frames.val := by
  intro frame member
  exact DormantFrame.entered (stack.frame_entered (.root current live) live frame member)
end Itasca.Runtime.Compiler

end

/-! ## ResolvedConditionalPrefix -/

section

/-!
Resolving a newly appended conditional branch.

Main declarations: `resolved_code_new_br_if`. A direct consumer is `Compiler.Body.Control.Control.CumulativePointControl`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem resolved_code_new_br_if (code : List Bytecode) (before after : List FixupTarget)
    (group : FixupTarget) (dst src count old condition resume : U32) (site : Usize)
    (position : site.val = code.length + (if count = 0#u32 ∨ src = dst then 0 else 2))
    (inside : FixupsInside (before ++ group :: after) code.length) :
    resolvedCode (code ++ branchIfInstructions dst src count old condition resume)
      (before ++ {group with sites := group.sites ++ [site]} :: after) =
      resolvedCode code (before ++ group :: after) ++ branchIfInstructions dst src count group.target condition resume := by
  by_cases elided : count = 0#u32 ∨ src = dst
  · simpa [branchIfInstructions, elided, BranchKind.instruction] using
      resolved_code_new_branch code [] before after group (.nonzero condition) old site (by simpa [elided] using position) inside
  · simpa [branchIfInstructions, elided, BranchKind.instruction, List.append_assoc] using
      resolved_code_new_branch code [.JumpIfZero condition resume, transferInstruction dst src count]
        before after group .jump old site (by simpa [elided] using position) inside

end Itasca.Runtime.Compiler

end

/-! ## LabelWiden -/

section

/-!
Increasing a label's permitted exits preserves literal code evidence. An already dead exit can safely be overapproximated as live.

Main declarations: `LabelWiden` and `LabelsWiden`. A direct consumer is `Compiler.Module.CompileSlice`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Increasing a label's permitted exits preserves literal code evidence.
An already dead exit can safely be overapproximated as live. -/
structure LabelWiden (left right : LabelTarget) : Prop where
  front : left.front = right.front
  branchTypes : left.branchTypes = right.branchTypes
  resultTypes : left.resultTypes = right.resultTypes
  target : left.target = right.target
  normalExit : left.normalExit = right.normalExit
  normalLive : left.normalLive = true → right.normalLive = true
  branchLive : left.branchLive = true → right.branchLive = true

theorem LabelWiden.refl (label : LabelTarget) : LabelWiden label label :=
  ⟨rfl, rfl, rfl, rfl, rfl, id, id⟩

def LabelsWiden := List.Forall₂ LabelWiden

theorem LabelsWiden.lookup {left right : List LabelTarget} (shape : LabelsWiden left right)
    {index : Nat} {label : LabelTarget} (found : left[index]? = some label) :
    ∃ other, right[index]? = some other ∧ LabelWiden label other := by
  induction shape generalizing index with
  | nil => simp at found
  | @cons leftHead rightHead leftTail rightTail head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst label
              exact ⟨rightHead, rfl, head⟩
    | succ index => exact ih found

theorem LabelsWiden.normal {left right} (shape : LabelsWiden left right)
    (live : NormalLive left) : NormalLive right := by
  intro label found
  cases shape with
  | nil => simp at found
  | @cons a b leftTail rightTail head tail =>
    have eq : b = label := by simpa using found
    subst label
    exact head.normalLive (live a rfl)

end Itasca.Runtime.Compiler

end

/-! ## ConditionalCertificates -/

section

/-!
A forward conditional branch keeps its false-edge resume distinct from the fixups for its selected source label.

Main declarations: `ConditionalHole`. A direct consumer is `Compiler.Local.Relations.Calls.BranchSuccessConditionalCallbacks`.
-/

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## ResolvedLiteral -/

section

/-!
Fixups cannot alter literal instructions whose constructors carry no branch destination, even before a stronger site-disjointness fact is used.

Main declarations: `resolved_code_fixed` and `resolved_code_loop_head`. A direct consumer is `Compiler.Module.CompileSlice`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Fixups cannot alter literal instructions whose constructors carry no
branch destination, even before a stronger site-disjointness fact is used. -/
theorem resolved_code_fixed (code : List Bytecode) (groups : List FixupTarget)
    (index : Nat) (instruction : Bytecode)
    (found : code[index]? = some instruction)
    (fixed : ∀ target, retarget instruction target = instruction) :
    (resolvedCode code groups)[index]? = some instruction := by
  induction groups generalizing code with
  | nil => exact found
  | cons group rest ih =>
    apply ih
    rw [patch_code_get]
    split <;> simp [found, fixed]

theorem resolved_code_loop_head (code : List Bytecode) (groups : List FixupTarget)
    (index : Nat) (found : code[index]? = some .LoopHead) :
    (resolvedCode code groups)[index]? = some .LoopHead :=
  resolved_code_fixed code groups index .LoopHead found (fun _ => rfl)

end Itasca.Runtime.Compiler

end

/-! ## ConsumedPrefix -/

section

/-!
Two actual consumed spans with the same start agree up to the earlier cursor, retaining an exact token encoding for the remaining suffix.

Main declarations: `Consumed.prefix_of_le` and `Consumed.next_of_prefix`. A direct consumer is `Compiler.Local.Relations.Syntax.ExecutableTokens`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Two actual consumed spans with the same start agree up to the earlier
cursor, retaining an exact token encoding for the remaining suffix. -/
theorem Consumed.prefix_of_le {data start xs ys next last}
    (short : Consumed data start xs next) (long : Consumed data start ys last)
    (order : next.val ≤ last.val) :
    ∃ suffix, ys = xs ++ suffix ∧ Consumed data next suffix last := by
  induction xs generalizing start ys with
  | nil =>
    have equal := short.empty_eq rfl
    subst next
    exact ⟨ys, rfl, long⟩
  | cons token rest ih =>
    obtain ⟨middle, first, remaining⟩ := Consumed.cons_iff.mp short
    cases ys with
    | nil =>
      have equal := long.empty_eq rfl
      have stepBound := first.span
      have restBound := remaining.span
      subst last
      omega
    | cons other tail =>
      obtain ⟨otherMiddle, otherFirst, otherRemaining⟩ := Consumed.cons_iff.mp long
      obtain ⟨rfl, rfl⟩ := first.unique otherFirst
      obtain ⟨suffix, equal, suffixCode⟩ := ih remaining otherRemaining
      exact ⟨suffix, by simp only [List.cons_append, equal], suffixCode⟩

/-- An unfinished reader prefix has a next token from the original complete
encoding, before any opcode-specific parser proof is selected. -/
theorem Consumed.next_of_prefix {data start tokens allTokens position finish}
    (before : Consumed data start tokens position)
    (complete : Consumed data start allTokens finish) (remaining : position.val < finish.val) :
    ∃ token next suffix, allTokens = tokens ++ token :: suffix ∧
      At data position token next ∧ Consumed data next suffix finish := by
  obtain ⟨rest, equal, encoded⟩ := before.prefix_of_le complete (Nat.le_of_lt remaining)
  cases rest with
  | nil =>
    have same := encoded.empty_eq rfl
    subst finish
    omega
  | cons token suffix =>
    obtain ⟨next, atToken, afterToken⟩ := Consumed.cons_iff.mp encoded
    exact ⟨token, next, suffix, equal, atToken, afterToken⟩
end Itasca.Wasm2

end
