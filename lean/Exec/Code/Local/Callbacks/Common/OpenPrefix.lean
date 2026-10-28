import Exec.Code.Local.Callbacks.Control.EnterIf
import Exec.Code.Local.Relations.Common.SuspendedPrefix
import Exec.Code.Local.Relations.Common.ResolvedPrefix
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- A new IF guard is its own pending group, separate from body branches. Its
future resolution touches only the newly appended guard. -/
theorem resolvedCode_open_guard (code : List Bytecode) (groups : List FixupTarget)
    (condition old target : U32) (site : Usize) (position : site.val = code.length)
    (inside : FixupsInside groups code.length) :
    resolvedCode (code ++ [.JumpIfZero condition old]) (⟨[site], target⟩ :: groups) =
      resolvedCode code groups ++ [.JumpIfZero condition target] := by
  have allInside : FixupsInside ([] ++ ⟨[], target⟩ :: groups) code.length := by
    intro group member pc atSite
    simp only [List.nil_append, List.mem_cons] at member
    rcases member with rfl | member
    · simp at atSite
    · exact inside group member pc atSite
  simpa [resolvedCode, patchCode, BranchKind.instruction] using
    resolvedCode_new_branch code [] [] groups ⟨[], target⟩ (.zero condition) old site
      (by simpa using position) allInside

end Itasca.Runtime.Code
