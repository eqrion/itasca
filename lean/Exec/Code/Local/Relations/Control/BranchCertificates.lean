import Exec.Code.Local.Control.Common.StructuredComposition
import Exec.Code.Local.Callbacks.Common.Fixups
namespace Exec.Code
open Aeneas Aeneas.Std

def BranchHole (code : List Bytecode) (sites : List Usize)
    (pc : Nat) (dst src count : U32) : Prop :=
  if count = 0#u32 ∨ src = dst then
    ∃ site, site ∈ sites ∧ site.val = pc ∧ code[pc]? = some (.Jump 4294967295#u32)
  else
    code[pc]? = some (transferInstruction dst src count) ∧
    ∃ site, site ∈ sites ∧ site.val = pc + 1 ∧ code[pc + 1]? = some (.Jump 4294967295#u32)

end Exec.Code
