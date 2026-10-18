import Exec.Code.Local.Relations.Common.Prefix
namespace Exec.Code
open Aeneas.Std

/-- A suspended parent owns only the bytecode before its child-entry cursor.
Later child emission and fixups may freely change the remaining suffix. -/
def SuspendedPrefix (types functions : List functype) (returns locals : List valtype)
    (code : List Bytecode) (labels : List LabelTarget) (before : List valtype)
    (source : List instr) (start cursor : Nat) (stack : List valtype) : Prop :=
  cursor ≤ code.length ∧
    CodePrefix types functions returns locals (code.take cursor) labels before source start cursor stack

theorem SuspendedPrefix.full {types functions returns locals code labels before source start cursor stack}
    (suspended : SuspendedPrefix types functions returns locals code labels before source start cursor stack) :
    CodePrefix types functions returns locals code labels before source start cursor stack := by
  simpa only [List.take_append_drop] using suspended.2.extend (code.drop cursor)

theorem SuspendedPrefix.stable {types functions returns locals code labels before source start cursor stack}
    (suspended : SuspendedPrefix types functions returns locals code labels before source start cursor stack)
    (changed : List Bytecode) (bound : cursor ≤ changed.length)
    (same : changed.take cursor = code.take cursor) :
    SuspendedPrefix types functions returns locals changed labels before source start cursor stack :=
  ⟨bound, same ▸ suspended.2⟩

theorem SuspendedPrefix.extend {types functions returns locals code labels before source start cursor stack}
    (suspended : SuspendedPrefix types functions returns locals code labels before source start cursor stack)
    (emitted : List Bytecode) :
    SuspendedPrefix types functions returns locals (code ++ emitted) labels before source start cursor stack := by
  have bound := suspended.1
  apply suspended.stable (code ++ emitted) (by simp; omega)
  exact List.take_append_of_le_length suspended.1

theorem CodePrefix.suspend {types functions returns locals code labels before source start stack}
    (current : CodePrefix types functions returns locals code labels before source start code.length stack) :
    SuspendedPrefix types functions returns locals code labels before source start code.length stack :=
  ⟨Nat.le_refl _, by simpa using current⟩

/-- Once the child is closed, its syntactic certificate is appended to the
saved parent prefix at the exact retained entry cursor. -/
theorem SuspendedPrefix.resume {types functions returns locals code labels before source start cursor stack
    more finish output}
    (suspended : SuspendedPrefix types functions returns locals code labels before source start cursor stack)
    (child : CodePrefix types functions returns locals code labels stack more cursor finish output) :
    CodePrefix types functions returns locals code labels before (source ++ more) start finish output :=
  suspended.full.append child

theorem SuspendedPrefix.resume_dead {types functions returns locals code labels before source start cursor stack
    more finish}
    (suspended : SuspendedPrefix types functions returns locals code labels before source start cursor stack)
    (child : DeadCodePrefix types functions returns locals code labels stack more cursor finish) :
    DeadCodePrefix types functions returns locals code labels before (source ++ more) start finish :=
  suspended.full.terminal child

end Exec.Code
