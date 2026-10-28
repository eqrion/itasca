import Itasca.Runtime.Code.Local.Control.Control.UniversalBranch
import Itasca.Runtime.Code.Local.Relations.Common.ResolvedConditionalPrefix
namespace Itasca.Runtime.Code
open Aeneas.Std

theorem FrameSites.add_conditional {code frame} (valid : FrameSites code frame)
    (dst src count old condition resume : U32) (site : Usize) (fixups : alloc.vec.Vec Usize)
    (appended : fixups.val = frame.fixups.val ++ [site])
    (position : site.val = code.length + (if count = 0#u32 ∨ src = dst then 0 else 2)) :
    FrameSites (code ++ branchIfInstructions dst src count old condition resume)
      {frame with end_reachable := true, fixups} := by
  have extended := valid.extend (branchIfInstructions dst src count old condition resume)
  refine ⟨?_, extended.guard⟩
  intro pc member
  simp only [appended, List.mem_append, List.mem_singleton] at member
  rcases member with previous | rfl
  · exact extended.branches pc previous
  · by_cases elided : count = 0#u32 ∨ src = dst
    · exact Or.inr ⟨condition, old, by simp [branchIfInstructions, elided, position]⟩
    · exact Or.inl ⟨old, by simp [branchIfInstructions, elided, position]⟩

end Itasca.Runtime.Code
