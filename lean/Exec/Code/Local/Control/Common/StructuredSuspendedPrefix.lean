import Exec.Code.Local.Control.Common.StructuredPrefix
namespace Exec.Code
open Aeneas.Std

/-- A suspended parent owns only the bytecode before its child-entry cursor.
Later child emission and fixups may freely change the remaining suffix. -/
def StructuredSuspendedPrefix (emission : List valtype → instr → List Bytecode → List valtype → Prop) (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget) (before : List valtype)
    (source : List instr) (start cursor : Nat) (stack : List valtype) : Prop :=
  cursor ≤ code.length ∧
    StructuredPrefix emission types functions returns locals (code.take cursor) labels before source start cursor stack

theorem StructuredSuspendedPrefix.full {emission types functions returns locals code labels before source start cursor stack}
    (suspended : StructuredSuspendedPrefix emission types functions returns locals code labels before source start cursor stack) :
    StructuredPrefix emission types functions returns locals code labels before source start cursor stack := by
  simpa only [List.take_append_drop] using suspended.2.extend (code.drop cursor)

theorem StructuredSuspendedPrefix.stable {emission types functions returns locals code labels before source start cursor stack}
    (suspended : StructuredSuspendedPrefix emission types functions returns locals code labels before source start cursor stack)
    (changed : List Bytecode) (bound : cursor ≤ changed.length)
    (same : changed.take cursor = code.take cursor) :
    StructuredSuspendedPrefix emission types functions returns locals changed labels before source start cursor stack :=
  ⟨bound, same ▸ suspended.2⟩

theorem StructuredSuspendedPrefix.extend {emission types functions returns locals code labels before source start cursor stack}
    (suspended : StructuredSuspendedPrefix emission types functions returns locals code labels before source start cursor stack)
    (emitted : List Bytecode) :
    StructuredSuspendedPrefix emission types functions returns locals (code ++ emitted) labels before source start cursor stack := by
  have bound := suspended.1
  apply suspended.stable (code ++ emitted) (by simp; omega)
  exact List.take_append_of_le_length suspended.1

theorem StructuredPrefix.suspend {emission types functions returns locals code labels before source start stack}
    (current : StructuredPrefix emission types functions returns locals code labels before source start code.length stack) :
    StructuredSuspendedPrefix emission types functions returns locals code labels before source start code.length stack :=
  ⟨Nat.le_refl _, by simpa using current⟩

/-- Once the child is closed, its syntactic certificate is appended to the
saved parent prefix at the exact retained entry cursor. -/
theorem StructuredSuspendedPrefix.resume {emission types functions returns locals code labels before source start cursor stack
    more finish output}
    (suspended : StructuredSuspendedPrefix emission types functions returns locals code labels before source start cursor stack)
    (child : StructuredPrefix emission types functions returns locals code labels stack more cursor finish output) :
    StructuredPrefix emission types functions returns locals code labels before (source ++ more) start finish output :=
  suspended.full.append child

theorem StructuredSuspendedPrefix.resume_dead {emission types functions returns locals code labels before source start cursor stack
    more finish}
    (suspended : StructuredSuspendedPrefix emission types functions returns locals code labels before source start cursor stack)
    (child : StructuredDeadPrefix emission types functions returns locals code labels stack more cursor finish) :
    StructuredDeadPrefix emission types functions returns locals code labels before (source ++ more) start finish :=
  suspended.full.terminal child

end Exec.Code

