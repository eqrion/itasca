import Exec.Code.Local.Relations.Common.Prefix
namespace Exec.Code
open Aeneas.Std

theorem CodePrefix.finish {types functions returns locals code labels before source start cursor stack}
    (current : CodePrefix types functions returns locals code labels before source start cursor stack)
    (bound : cursor ≤ code.length) (live : NormalLive labels) :
    CodeRel types functions returns locals code labels before source start cursor stack := by
  have closed := current [] [] cursor stack (.nil labels stack cursor (by simpa using bound) live)
  simpa using closed

theorem DeadCodePrefix.finish {types functions returns locals code labels before source start cursor}
    (current : DeadCodePrefix types functions returns locals code labels before source start cursor)
    (next : Nat) (output : List valtype) (order : cursor ≤ next) (bound : next ≤ code.length) :
    CodeRel types functions returns locals code labels before source start next output := by
  have closed := current [] [] next output order (by simpa using bound)
  simpa using closed

end Exec.Code
