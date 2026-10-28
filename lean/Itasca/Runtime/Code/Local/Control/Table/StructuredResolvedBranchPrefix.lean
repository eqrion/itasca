import Itasca.Runtime.Code.Local.Control.Table.StructuredPrefix
import Itasca.Runtime.Code.Local.Relations.Control.ResolvedBranchPrefix
namespace Itasca.Runtime.Code
open Aeneas.Std
theorem StructuredPrefix.resolved_branch {jumpTables : List Aeneas.Std.U32} {emit types functions returns locals labels initial source start stack}
    {code : List Bytecode} {before after : List FixupTarget} {group : FixupTarget}
    {depth : Nat} {label : LabelTarget} {dst src count old : U32} {site : Usize}
    (prior : StructuredPrefix (jumpTables := jumpTables) emit types functions returns locals (resolvedCode code (before ++ group :: after))
      labels initial source start code.length stack)
    (inside : FixupsInside (before ++ group :: after) code.length)
    (position : site.val = code.length + (if count = 0#u32 ∨ src = dst then 0 else 1))
    (lookup : labels[depth]? = some label) (live : label.branchLive = true)
    (target : label.target = group.target) (layout : BranchLayout locals stack label dst src count) :
    StructuredDeadPrefix (jumpTables := jumpTables) emit types functions returns locals
      (resolvedCode (code ++ branchInstructions dst src count old)
        (before ++ {group with sites := group.sites ++ [site]} :: after))
      labels initial (source ++ [.BR (.mk_uN depth)]) start
      (code.length + (branchInstructions dst src count group.target).length) := by
  rw [resolvedCode_new_br code before after group dst src count old site position inside]
  apply (prior.extend (branchInstructions dst src count group.target)).terminal
  apply StructuredDeadPrefix.branch lookup live layout
  rw [target]
  exact ⟨resolvedCode code (before ++ group :: after), [], by simp,
    resolvedCode_length _ _, rfl⟩

end Itasca.Runtime.Code
