import Exec.Code.Local.Relations.Common.Prefix
import Exec.Code.Local.Relations.Common.ResolvedPrefix
namespace Exec.Code
open Aeneas.Std

/-- Retargeting a newly emitted BR in its selected open group preserves the
previous resolved prefix and appends the final literal branch sequence. -/
theorem resolvedCode_new_br (code : List Bytecode) (before after : List FixupTarget)
    (group : FixupTarget) (dst src count old : U32) (site : Usize)
    (position : site.val = code.length + (if count = 0#u32 ∨ src = dst then 0 else 1))
    (inside : FixupsInside (before ++ group :: after) code.length) :
    resolvedCode (code ++ branchInstructions dst src count old)
      (before ++ {group with sites := group.sites ++ [site]} :: after) =
      resolvedCode code (before ++ group :: after) ++ branchInstructions dst src count group.target := by
  by_cases elided : count = 0#u32 ∨ src = dst
  · simpa [branchInstructions, elided, BranchKind.instruction] using
      resolvedCode_new_branch code [] before after group .jump old site (by simpa [elided] using position) inside
  · simpa [branchInstructions, elided, BranchKind.instruction, List.append_assoc] using
      resolvedCode_new_branch code [transferInstruction dst src count] before after group .jump old site
        (by simpa [elided] using position) inside

end Exec.Code
