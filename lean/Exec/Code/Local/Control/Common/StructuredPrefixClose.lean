import Exec.Code.Local.Control.Common.StructuredPrefix
namespace Exec.Code
open Aeneas.Std

theorem StructuredPrefix.finish {emit types functions returns locals code labels before source start cursor stack}
    (current : StructuredPrefix emit types functions returns locals code labels before source start cursor stack)
    (bound : cursor ≤ code.length) (live : NormalLive labels) :
    StructuredCode emit types functions returns locals code labels before source start cursor stack := by
  have closed := current [] [] cursor stack (.nil labels stack cursor (by simpa using bound) live)
  simpa using closed

theorem StructuredDeadPrefix.finish {emit types functions returns locals code labels before source start cursor}
    (current : StructuredDeadPrefix emit types functions returns locals code labels before source start cursor)
    (next : Nat) (output : List valtype) (order : cursor ≤ next) (bound : next ≤ code.length) :
    StructuredCode emit types functions returns locals code labels before source start next output := by
  have closed := current [] [] next output order (by simpa using bound)
  simpa using closed

end Exec.Code

