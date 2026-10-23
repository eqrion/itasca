import Exec.Code.Local.Lowering.Common.LoweringConditionalTransfer
namespace Exec.Code
open Aeneas Aeneas.Std

/-- A forward conditional branch keeps its false-edge resume distinct from
the fixups for its selected source label. -/
def ConditionalHole (code : List Bytecode) (sites : List Usize)
    (pc : Nat) (dst src count cond resume : U32) : Prop :=
  if count = 0#u32 ∨ src = dst then
    ∃ site, site ∈ sites ∧ site.val = pc ∧
      code[pc]? = some (.JumpIfNonZero cond core.num.U32.MAX) ∧ resume.val = pc + 1
  else
    code[pc]? = some (.JumpIfZero cond resume) ∧
    (∀ site, site ∈ sites → pc ≠ site.val) ∧
    code[pc + 1]? = some (transferInstruction dst src count) ∧
    ∃ site, site ∈ sites ∧ site.val = pc + 2 ∧
      code[pc + 2]? = some (.Jump core.num.U32.MAX) ∧ resume.val = pc + 3

end Exec.Code
