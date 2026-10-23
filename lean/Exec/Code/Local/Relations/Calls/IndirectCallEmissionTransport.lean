import Exec.Code.Local.Relations.Calls.IndirectCallEmission
namespace Exec.Code
open Aeneas.Std

theorem IndirectCallEmission.context {pairs C D before instruction emitted after}
    (types : D.TYPES = C.TYPES) (locals : D.LOCALS = C.LOCALS) (tables : D.TABLES = C.TABLES)
    (emission : IndirectCallEmission pairs C before instruction emitted after) :
    IndirectCallEmission pairs D before instruction emitted after := by
  cases emission with
  | call front params results typeIndex tableIndex entry index base bounds signature table pair basePosition indexPosition =>
    exact .call front params results typeIndex tableIndex entry index base bounds
      (by simpa only [types] using signature) (by simpa only [tables] using table) pair
      (by simpa only [locals] using basePosition) indexPosition
end Exec.Code
