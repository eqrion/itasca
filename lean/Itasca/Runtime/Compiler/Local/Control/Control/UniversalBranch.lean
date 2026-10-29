import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalTerminal
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FramePlanUpdate
import Itasca.Runtime.Compiler.Local.Relations.Control.ResolvedBranchPrefix
namespace Itasca.Runtime.Code
open Aeneas.Std

theorem scopeLabels_lookup {scopes labels} (shapes : List.Forall₂ ScopeLabel scopes labels)
    {depth : Nat} {scope label} (source : scopes[depth]? = some scope) (target : labels[depth]? = some label) :
    ScopeLabel scope label := by
  induction shapes generalizing depth with
  | nil => simp at source
  | cons shape shapes ih =>
    cases depth with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at source target; subst_vars; exact shape
    | succ depth => exact ih source target

theorem FrameSites.add_branch {code frame} (valid : FrameSites code frame)
    (dst src count old : U32) (site : Usize) (fixups : alloc.vec.Vec Usize)
    (appended : fixups.val = frame.fixups.val ++ [site])
    (position : site.val = code.length + (if count = 0#u32 ∨ src = dst then 0 else 1)) :
    FrameSites (code ++ branchInstructions dst src count old)
      {frame with end_reachable := true, fixups} := by
  have extended := valid.extend (branchInstructions dst src count old)
  refine ⟨?_, extended.guard⟩
  intro pc member
  simp only [appended, List.mem_append, List.mem_singleton] at member
  rcases member with previous | rfl
  · exact extended.branches pc previous
  · apply Or.inl
    refine ⟨old, ?_⟩
    by_cases elided : count = 0#u32 ∨ src = dst
    · simp [branchInstructions, elided, position]
    · simp [branchInstructions, elided, position, List.getElem?_append]

end Itasca.Runtime.Code
