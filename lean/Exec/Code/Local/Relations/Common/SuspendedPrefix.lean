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

end Exec.Code
