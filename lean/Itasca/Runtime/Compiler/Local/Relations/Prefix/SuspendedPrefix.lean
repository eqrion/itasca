import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupAlgebra
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels

/-!
Sections, each formerly its own module: ResolvedPrefix, Concatenation, Extension, Prefix, SuspendedPrefix.
-/

/-! ## ResolvedPrefix -/

section

/-!
One open label's retained physical fixup sites and its eventual static exit. The target is a source-layout coordinate, not an execution predicate.

Main declarations: `FixupTarget` and `resolvedCode`. A direct consumer is `Compiler.Local.Relations.Control.ResolvedBranchPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- One open label's retained physical fixup sites and its eventual static exit.
The target is a source-layout coordinate, not an execution predicate. -/
structure FixupTarget where
  sites : List Usize
  target : U32

def resolvedCode (code : List Bytecode) : List FixupTarget → List Bytecode
  | [] => code
  | group :: rest => resolvedCode (patchCode code group.sites group.target) rest

def FixupsInside (groups : List FixupTarget) (length : Nat) : Prop :=
  ∀ group, group ∈ groups → ∀ site, site ∈ group.sites → site.val < length

theorem resolved_code_length (code : List Bytecode) (groups : List FixupTarget) :
    (resolvedCode code groups).length = code.length := by
  induction groups generalizing code with
  | nil => rfl
  | cons group rest ih => simp [resolvedCode, ih, patch_code_length]

theorem resolved_code_append_code (code emitted : List Bytecode) (groups : List FixupTarget)
    (inside : FixupsInside groups code.length) :
    resolvedCode (code ++ emitted) groups = resolvedCode code groups ++ emitted := by
  induction groups generalizing code with
  | nil => rfl
  | cons group rest ih =>
    simp only [resolvedCode]
    rw [patch_code_append_code _ _ _ _ (inside group (by simp))]
    apply ih
    intro g member site atSite
    simpa [patch_code_length] using inside g (List.mem_cons_of_mem _ member) site atSite

/-- A newly emitted forward branch belongs to exactly its selected label group.
Resolving that extended schedule appends the branch with its final static target
and leaves all earlier resolved instructions unchanged. -/
theorem resolved_code_new_branch (code emitted : List Bytecode) (before after : List FixupTarget)
    (group : FixupTarget) (kind : BranchKind) (old : U32) (site : Usize)
    (position : site.val = code.length + emitted.length)
    (inside : FixupsInside (before ++ group :: after) code.length) :
    resolvedCode (code ++ emitted ++ [kind.instruction old])
      (before ++ {group with sites := group.sites ++ [site]} :: after) =
      resolvedCode code (before ++ group :: after) ++ emitted ++ [kind.instruction group.target] := by
  induction before generalizing code with
  | nil =>
    simp only [List.nil_append, resolvedCode]
    rw [patch_code_new_branch code emitted group.sites kind old group.target site position
      (inside group (by simp))]
    rw [List.append_assoc, resolved_code_append_code]
    · simp [List.append_assoc]
    · intro g member pc atPc
      simpa [patch_code_length] using inside g (by simp [member]) pc atPc
  | cons head rest ih =>
    simp only [List.cons_append, resolvedCode]
    have headInside : ∀ pc, pc ∈ head.sites → pc.val < code.length :=
      inside head (by simp)
    rw [List.append_assoc, patch_code_append_code _ _ _ _ headInside, ← List.append_assoc]
    apply ih
    · simpa [patch_code_length] using position
    · intro g member pc atPc
      simpa [patch_code_length] using inside g (List.mem_cons_of_mem _ member) pc atPc

end Itasca.Runtime.Compiler

end

/-! ## Concatenation -/

section

/-!
Changing a label's retained source continuation does not change its instruction layout, target, or reachability.

Main declarations: `LabelShape` and `LabelsShape`. A direct consumer is `Compiler.Local.Relations.Prefix.LabelWiden`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Changing a label's retained source continuation does not change its
instruction layout, target, or reachability. -/
structure LabelShape (left right : LabelTarget) : Prop where
  front : left.front = right.front
  branchTypes : left.branchTypes = right.branchTypes
  resultTypes : left.resultTypes = right.resultTypes
  target : left.target = right.target
  normalExit : left.normalExit = right.normalExit
  normalLive : left.normalLive = right.normalLive
  branchLive : left.branchLive = right.branchLive

theorem LabelShape.refl (label : LabelTarget) : LabelShape label label :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def LabelsShape := List.Forall₂ LabelShape

theorem LabelsShape.refl (labels : List LabelTarget) : LabelsShape labels labels := by
  induction labels with
  | nil => exact .nil
  | cons label rest ih => exact .cons (LabelShape.refl label) ih

theorem LabelsShape.lookup {left right : List LabelTarget} (shape : LabelsShape left right)
    {index : Nat} {label : LabelTarget} (found : left[index]? = some label) :
    ∃ other, right[index]? = some other ∧ LabelShape label other := by
  induction shape generalizing index with
  | nil => simp at found
  | @cons leftHead rightHead leftTail rightTail head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst label
              exact ⟨rightHead, rfl, head⟩
    | succ index => exact ih found

theorem LabelsShape.normal {left right} (shape : LabelsShape left right)
    (live : NormalLive left) : NormalLive right := by
  intro label found
  cases shape with
  | nil => simp at found
  | @cons a b leftTail rightTail head tail =>
    have eq : b = label := by simpa using found
    subst label
    rw [← head.normalLive]
    exact live a rfl

end Itasca.Runtime.Compiler

end

/-! ## Extension -/

section

/-!
Extension of source/code segment and guarded-skip certificates.

Main declarations: `Segment.extend` and `IfSkip.extend`. A direct consumer is `Compiler.Local.Relations.Prefix.Prefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem Segment.extend {code pc instructions next} (segment : Segment code pc instructions next)
    (suffix : List Bytecode) : Segment (code ++ suffix) pc instructions next := by
  obtain ⟨front, back, rfl, position, endpoint⟩ := segment
  exact ⟨front, back ++ suffix, by simp only [List.append_assoc], position, endpoint⟩

theorem fetch_extend {code : List Bytecode} {pc : Nat} {instruction : Bytecode}
    (found : code[pc]? = some instruction) (suffix : List Bytecode) :
    (code ++ suffix)[pc]? = some instruction :=
  (List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1).trans found

theorem IfSkip.extend {code yesExit noEntry exit yesNormal}
    (skip : IfSkip code yesExit noEntry exit yesNormal) (suffix : List Bytecode) :
    IfSkip (code ++ suffix) yesExit noEntry exit yesNormal := by
  cases skip with
  | emitted fragment => exact .emitted (fragment.extend suffix)
  | direct normal otherwise => exact .direct normal otherwise

end Itasca.Runtime.Compiler

end

/-! ## Prefix -/

section

/-!
A builder invariant for a still-open source prefix. Its hole is another syntactic CodeRel certificate, never an execution or simulation premise. Unlike a completed CodeRel, an unfinished hole does not assert a live normal exit; a later RETURN or branch can close it without certifying unreachable suffixes.

Main declarations: `CodePrefix` and `DeadCodePrefix`. A direct consumer is `Compiler.Local.Relations.Control.ResolvedBranchPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- A builder invariant for a still-open source prefix. Its hole is another
syntactic CodeRel certificate, never an execution or simulation premise. Unlike
a completed CodeRel, an unfinished hole does not assert a live normal exit;
a later RETURN or branch can close it without certifying unreachable suffixes. -/
def CodePrefix (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget)
    (before : List valtype) (source : List instr) (pc cursor : Nat) (stack : List valtype) : Prop :=
  ∀ suffix tail next final, CodeRel types functions returns locals (code ++ suffix) labels stack tail cursor next final →
    CodeRel types functions returns locals (code ++ suffix) labels before (source ++ tail) pc next final

theorem CodePrefix.empty (types functions returns locals code labels stack pc) :
    CodePrefix types functions returns locals code labels stack [] pc pc stack := by
  intro suffix tail next final rest
  simpa using rest

/-- A terminal prefix gives a certificate even for arbitrary uncompiled source
suffixes. The proof is obtained from a literal terminal bytecode constructor. -/
def DeadCodePrefix (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget)
    (before : List valtype) (source : List instr) (pc cursor : Nat) : Prop :=
  ∀ suffix tail next final, cursor ≤ next → next ≤ (code ++ suffix).length →
    CodeRel types functions returns locals (code ++ suffix) labels before (source ++ tail) pc next final

end Itasca.Runtime.Compiler

end

/-! ## SuspendedPrefix -/

section

/-!
A suspended parent owns only the bytecode before its child-entry cursor. Later child emission and fixups may freely change the remaining suffix.

Main declarations: `SuspendedPrefix`. A direct consumer is `Compiler.Local.Callbacks.Fixups.OpenPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- A suspended parent owns only the bytecode before its child-entry cursor.
Later child emission and fixups may freely change the remaining suffix. -/
def SuspendedPrefix (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget) (before : List valtype)
    (source : List instr) (start cursor : Nat) (stack : List valtype) : Prop :=
  cursor ≤ code.length ∧
    CodePrefix types functions returns locals (code.take cursor) labels before source start cursor stack

end Itasca.Runtime.Compiler

end
