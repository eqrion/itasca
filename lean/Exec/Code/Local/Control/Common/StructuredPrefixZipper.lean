import Exec.Code.Local.Control.Common.StructuredSuspendedPrefix
import Exec.Code.Local.Relations.Common.PrefixZipper
namespace Exec.Code
open Aeneas.Std
/-- A terminal suspended parent owns just the code before its child, exactly
as a live suspended parent does. No instruction in an unentered child is needed. -/
def StructuredSuspendedTerminal (emission : List valtype → instr → List Bytecode → List valtype → Prop) (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget) (before : List valtype)
    (source : List instr) (start cursor : Nat) : Prop :=
  cursor ≤ code.length ∧ StructuredDeadPrefix emission types functions returns locals (code.take cursor)
    labels before source start cursor

theorem StructuredSuspendedTerminal.full {emission types functions returns locals code labels before source start cursor}
    (saved : StructuredSuspendedTerminal emission types functions returns locals code labels before source start cursor) :
    StructuredDeadPrefix emission types functions returns locals code labels before source start cursor := by
  simpa only [List.take_append_drop] using saved.2.extend (code.drop cursor)

theorem StructuredSuspendedTerminal.stable {emission types functions returns locals code labels before source start cursor}
    (saved : StructuredSuspendedTerminal emission types functions returns locals code labels before source start cursor)
    (changed : List Bytecode) (bound : cursor ≤ changed.length)
    (same : changed.take cursor = code.take cursor) :
    StructuredSuspendedTerminal emission types functions returns locals changed labels before source start cursor :=
  ⟨bound, same ▸ saved.2⟩

theorem StructuredSuspendedTerminal.extend {emission types functions returns locals code labels before source start cursor}
    (saved : StructuredSuspendedTerminal emission types functions returns locals code labels before source start cursor)
    (emitted : List Bytecode) :
    StructuredSuspendedTerminal emission types functions returns locals (code ++ emitted) labels before source start cursor := by
  have bound := saved.1
  exact saved.stable (code ++ emitted) (by simp; omega) (List.take_append_of_le_length bound)

theorem StructuredDeadPrefix.suspend {emission types functions returns locals code labels before source start}
    (current : StructuredDeadPrefix emission types functions returns locals code labels before source start code.length) :
    StructuredSuspendedTerminal emission types functions returns locals code labels before source start code.length :=
  ⟨Nat.le_refl _, by simpa using current⟩

/-- A parent either waits for an entered child's typed result, already has a
terminal prefix, or itself belongs to an unentered source subtree. -/
def StructuredParentPrefix (emission : List valtype → instr → List Bytecode → List valtype → Prop) (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget) (parent child : SourceScope) : Prop :=
  if parent.entered then
    if child.entered then
      StructuredSuspendedPrefix emission types functions returns locals code labels parent.input parent.source
        parent.bodyPc child.entry child.arguments
    else StructuredSuspendedTerminal emission types functions returns locals code labels parent.input parent.source
        parent.bodyPc child.entry
  else True

theorem StructuredParentPrefix.extend {emission types functions returns locals code labels parent child}
    (saved : StructuredParentPrefix emission types functions returns locals code labels parent child)
    (emitted : List Bytecode) :
    StructuredParentPrefix emission types functions returns locals (code ++ emitted) labels parent child := by
  unfold StructuredParentPrefix at *
  split at saved
  · split at saved
    · simpa only [‹parent.entered = true›, ‹child.entered = true›, ite_true] using saved.extend emitted
    · simpa only [‹parent.entered = true›, ‹¬child.entered = true›, ite_true, ite_false, Bool.false_eq_true] using saved.extend emitted
  · simp_all

/-- The saved parent chain mirrors the source validator zipper. Each parent
owns its prefix before the next child's opening instruction. -/
inductive StructuredParentPrefixes (emission : List valtype → instr → List Bytecode → List valtype → Prop) (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) : List SourceScope → List LabelTarget → SourceScope → Prop where
  | root (current) : StructuredParentPrefixes emission types functions returns locals code [] [] current
  | push {parents labels parent} (prior : StructuredParentPrefixes emission types functions returns locals code parents labels parent)
      (label child) (shape : ScopeLabel parent label)
      (bound : child.entry ≤ code.length)
      (saved : StructuredParentPrefix emission types functions returns locals code (label :: labels) parent child) :
      StructuredParentPrefixes emission types functions returns locals code (parents ++ [parent]) (label :: labels) child

theorem StructuredParentPrefixes.extend {emission types functions returns locals code parents labels current}
    (saved : StructuredParentPrefixes emission types functions returns locals code parents labels current)
    (emitted : List Bytecode) :
    StructuredParentPrefixes emission types functions returns locals (code ++ emitted) parents labels current := by
  induction saved with
  | root current => exact .root current
  | push prior label child shape bound saved ih =>
    exact .push ih label child shape (by simp; omega) (saved.extend emitted)


/-- Terminal evidence remains valid when the physical builder advances past
an unentered source subtree. The logical continuation cannot precede it. -/
theorem StructuredDeadPrefix.delay {emission types functions returns locals code labels before source start cursor}
    (current : StructuredDeadPrefix emission types functions returns locals code labels before source start cursor)
    {later : Nat} (order : cursor ≤ later) :
    StructuredDeadPrefix emission types functions returns locals code labels before source start later := by
  intro suffix tail next final nextOrder bound
  exact current suffix tail next final (order.trans nextOrder) bound

theorem StructuredSuspendedTerminal.close_child {emission types functions returns locals code labels before source start cursor}
    (saved : StructuredSuspendedTerminal emission types functions returns locals code labels before source start cursor)
    (instruction : instr) :
    StructuredDeadPrefix emission types functions returns locals code labels before (source ++ [instruction]) start code.length :=
  (saved.full.skip_source [instruction]).delay saved.1

theorem StructuredParentPrefix.resume {emission types functions returns locals code labels parent child}
    (saved : StructuredParentPrefix emission types functions returns locals code labels parent child)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    {source next stack}
    (closed : StructuredPrefix emission types functions returns locals code labels child.arguments source child.entry next stack) :
    StructuredPrefix emission types functions returns locals code labels parent.input (parent.source ++ source)
      parent.bodyPc next stack := by
  simp only [StructuredParentPrefix, parentEntered, childEntered, ite_true] at saved
  exact saved.resume closed

theorem StructuredParentPrefix.resume_dead {emission types functions returns locals code labels parent child}
    (saved : StructuredParentPrefix emission types functions returns locals code labels parent child)
    (parentEntered : parent.entered = true) (childEntered : child.entered = true)
    {source next}
    (closed : StructuredDeadPrefix emission types functions returns locals code labels child.arguments source child.entry next) :
    StructuredDeadPrefix emission types functions returns locals code labels parent.input (parent.source ++ source)
      parent.bodyPc next := by
  simp only [StructuredParentPrefix, parentEntered, childEntered, ite_true] at saved
  exact saved.resume_dead closed

theorem StructuredParentPrefix.close_unentered {emission types functions returns locals code labels parent child}
    (saved : StructuredParentPrefix emission types functions returns locals code labels parent child)
    (parentEntered : parent.entered = true) (childEntered : child.entered = false)
    (instruction : instr) :
    StructuredDeadPrefix emission types functions returns locals code labels parent.input (parent.source ++ [instruction])
      parent.bodyPc code.length := by
  simp only [StructuredParentPrefix, parentEntered, childEntered, Bool.false_eq_true, ite_true, ite_false] at saved
  exact saved.close_child instruction

end Exec.Code
