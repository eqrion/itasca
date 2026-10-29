import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedPrefix

/-!
Fixups cannot alter literal instructions whose constructors carry no branch destination, even before a stronger site-disjointness fact is used.

Main declarations: `resolved_code_fixed` and `resolved_code_loop_head`. A direct consumer is `Compiler.Module.CompileSlice`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Fixups cannot alter literal instructions whose constructors carry no
branch destination, even before a stronger site-disjointness fact is used. -/
theorem resolved_code_fixed (code : List Bytecode) (groups : List FixupTarget)
    (index : Nat) (instruction : Bytecode)
    (found : code[index]? = some instruction)
    (fixed : ∀ target, retarget instruction target = instruction) :
    (resolvedCode code groups)[index]? = some instruction := by
  induction groups generalizing code with
  | nil => exact found
  | cons group rest ih =>
    apply ih
    rw [patch_code_get]
    split <;> simp [found, fixed]

theorem resolved_code_loop_head (code : List Bytecode) (groups : List FixupTarget)
    (index : Nat) (found : code[index]? = some .LoopHead) :
    (resolvedCode code groups)[index]? = some .LoopHead :=
  resolved_code_fixed code groups index .LoopHead found (fun _ => rfl)

end Itasca.Runtime.Compiler
