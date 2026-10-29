import Itasca.Runtime.Compiler.Local.Control.Segments.Structured
namespace Itasca.Runtime.Code
open Aeneas.Std
/-- An emitted table destination has the ordinary branch layout and exact
transfer/jump fragment for its source depth. -/
def BranchTableEntry (locals : List valtype) (labels : List LabelTarget)
    (stack : List valtype) (code : List Bytecode) (depth : labelidx) (entry : U32) (next : Nat) : Prop :=
  ∃ label dst src count fragmentEnd,
    labels[proj_uN_0 depth]? = some label ∧ label.branchLive = true ∧
    BranchLayout locals stack label dst src count ∧
    Segment code entry.val (branchInstructions dst src count label.target) fragmentEnd ∧
    fragmentEnd ≤ next ∧ next ≤ code.length

/-- Pure compiler evidence for a branch table, including its default entry.
Every retained side-table PC is tied to an emitted branch fragment. -/
structure BranchTableLayout (jumpTables : List U32) (locals : List valtype)
    (labels : List LabelTarget) (stack : List valtype) (code : List Bytecode)
    (depths : List labelidx) (fallback : labelidx) (pc next : Nat)
    (selector start len : U32) : Prop where
  selectorSlot : selector.val = slots locals + slots stack
  length : len.val = depths.length+1
  instruction : code[pc]? = some (.JumpTable selector start len)
  arithmetic : start.val + depths.length ≤ U32.max
  entries : ∀ index depth, (depths ++ [fallback])[index]? = some depth →
    ∃ entry, jumpTables[start.val+index]? = some entry ∧
      BranchTableEntry locals labels stack code depth entry next

end Itasca.Runtime.Code
