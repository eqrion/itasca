import Exec.Code.Local.Control.Table.StructuredPrefixWithTables
namespace Exec.Code
open Aeneas.Std

theorem StructuredPrefixWithTables.finish {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code labels before source start cursor stack}
    (current : StructuredPrefixWithTables (jumpTables := jumpTables) emit types functions returns locals code labels before source start cursor stack)
    (bound : cursor ≤ code.length) (live : NormalLive labels) :
    StructuredCodeWithTables emit types functions returns locals code jumpTables labels before source start cursor stack := by
  have closed := current [] [] cursor stack (.nil labels stack cursor (by simpa using bound) live)
  simpa using closed

theorem StructuredDeadPrefixWithTables.finish {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals code labels before source start cursor}
    (current : StructuredDeadPrefixWithTables (jumpTables := jumpTables) emit types functions returns locals code labels before source start cursor)
    (next : Nat) (output : List valtype) (order : cursor ≤ next) (bound : next ≤ code.length) :
    StructuredCodeWithTables emit types functions returns locals code jumpTables labels before source start next output := by
  have closed := current [] [] next output order (by simpa using bound)
  simpa using closed

end Exec.Code

