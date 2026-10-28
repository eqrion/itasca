import Itasca.Runtime.Code.Local.Relations.Control.ResolvedBranchPrefix
namespace Itasca.Runtime.Code
open Aeneas.Std

theorem resolvedCode_new_br_if (code : List Bytecode) (before after : List FixupTarget)
    (group : FixupTarget) (dst src count old condition resume : U32) (site : Usize)
    (position : site.val = code.length + (if count = 0#u32 ∨ src = dst then 0 else 2))
    (inside : FixupsInside (before ++ group :: after) code.length) :
    resolvedCode (code ++ branchIfInstructions dst src count old condition resume)
      (before ++ {group with sites := group.sites ++ [site]} :: after) =
      resolvedCode code (before ++ group :: after) ++ branchIfInstructions dst src count group.target condition resume := by
  by_cases elided : count = 0#u32 ∨ src = dst
  · simpa [branchIfInstructions, elided, BranchKind.instruction] using
      resolvedCode_new_branch code [] before after group (.nonzero condition) old site (by simpa [elided] using position) inside
  · simpa [branchIfInstructions, elided, BranchKind.instruction, List.append_assoc] using
      resolvedCode_new_branch code [.JumpIfZero condition resume, transferInstruction dst src count]
        before after group .jump old site (by simpa [elided] using position) inside

end Itasca.Runtime.Code
