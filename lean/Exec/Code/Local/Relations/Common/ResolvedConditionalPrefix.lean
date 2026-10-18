import Exec.Code.Local.Relations.Control.ResolvedBranchPrefix
namespace Exec.Code
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

/-- The actual false-edge cursor remains outside the selected label's fixups.
Resolving the new branch extends the old prefix with a complete BR_IF fragment. -/
theorem CodePrefix.resolved_branchIf {types functions returns locals labels initial source start stack}
    {code : List Bytecode} {before after : List FixupTarget} {group : FixupTarget}
    {depth : Nat} {label : LabelTarget} {dst src count old condition resume : U32} {site : Usize}
    (prior : CodePrefix types functions returns locals (resolvedCode code (before ++ group :: after))
      labels initial source start code.length (stack ++ [.I32]))
    (inside : FixupsInside (before ++ group :: after) code.length)
    (position : site.val = code.length + (if count = 0#u32 ∨ src = dst then 0 else 2))
    (resumePosition : resume.val = code.length + (if count = 0#u32 ∨ src = dst then 1 else 3))
    (lookup : labels[depth]? = some label) (live : label.branchLive = true)
    (target : label.target = group.target) (layout : BranchLayout locals stack label dst src count)
    (conditionSlot : condition.val = slots locals + slots stack) :
    CodePrefix types functions returns locals
      (resolvedCode (code ++ branchIfInstructions dst src count old condition resume)
        (before ++ {group with sites := group.sites ++ [site]} :: after))
      labels initial (source ++ [.BR_IF (.mk_uN depth)]) start resume.val stack := by
  rw [resolvedCode_new_br_if code before after group dst src count old condition resume site position inside]
  apply (prior.extend (branchIfInstructions dst src count group.target condition resume)).append
  apply CodePrefix.branchIf lookup live layout conditionSlot
  rw [target]
  refine ⟨resolvedCode code (before ++ group :: after), [], by simp, resolvedCode_length _ _, ?_⟩
  by_cases empty : count = 0#u32 ∨ src = dst
  · simpa [branchIfInstructions, empty] using resumePosition
  · simpa [branchIfInstructions, empty] using resumePosition

end Exec.Code
