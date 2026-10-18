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

/-- A source BR closes the active prefix while updating exactly one future
label's fixup list. The terminal certificate permits all omitted source tails. -/
theorem CodePrefix.resolved_branch {types functions returns locals labels initial source start stack}
    {code : List Bytecode} {before after : List FixupTarget} {group : FixupTarget}
    {depth : Nat} {label : LabelTarget} {dst src count old : U32} {site : Usize}
    (prior : CodePrefix types functions returns locals (resolvedCode code (before ++ group :: after))
      labels initial source start code.length stack)
    (inside : FixupsInside (before ++ group :: after) code.length)
    (position : site.val = code.length + (if count = 0#u32 ∨ src = dst then 0 else 1))
    (lookup : labels[depth]? = some label) (live : label.branchLive = true)
    (target : label.target = group.target) (layout : BranchLayout locals stack label dst src count) :
    DeadCodePrefix types functions returns locals
      (resolvedCode (code ++ branchInstructions dst src count old)
        (before ++ {group with sites := group.sites ++ [site]} :: after))
      labels initial (source ++ [.BR (.mk_uN depth)]) start
      (code.length + (branchInstructions dst src count group.target).length) := by
  rw [resolvedCode_new_br code before after group dst src count old site position inside]
  apply (prior.extend (branchInstructions dst src count group.target)).terminal
  apply DeadCodePrefix.branch lookup live layout
  rw [target]
  exact ⟨resolvedCode code (before ++ group :: after), [], by simp,
    resolvedCode_length _ _, rfl⟩

end Exec.Code
