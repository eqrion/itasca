import Exec.Code.Local.Relations.Common.ResolvedPrefix
namespace Exec.Code
open Aeneas.Std

/-- Fixups cannot alter literal instructions whose constructors carry no
branch destination, even before a stronger site-disjointness fact is used. -/
theorem resolvedCode_fixed (code : List Bytecode) (groups : List FixupTarget)
    (index : Nat) (instruction : Bytecode)
    (found : code[index]? = some instruction)
    (fixed : ∀ target, retarget instruction target = instruction) :
    (resolvedCode code groups)[index]? = some instruction := by
  induction groups generalizing code with
  | nil => exact found
  | cons group rest ih =>
    apply ih
    rw [patchCode_get]
    split <;> simp [found, fixed]

theorem resolvedCode_loop_head (code : List Bytecode) (groups : List FixupTarget)
    (index : Nat) (found : code[index]? = some .LoopHead) :
    (resolvedCode code groups)[index]? = some .LoopHead :=
  resolvedCode_fixed code groups index .LoopHead found (fun _ => rfl)

end Exec.Code
