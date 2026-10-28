import Itasca.Runtime.Code.Local.Callbacks.Control.EnterElse
import Itasca.Runtime.Code.Local.Callbacks.Common.OpenPrefix
import Itasca.Runtime.Code.Local.Relations.Common.Prefix
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

theorem resolvedCode_guard_set (code : List Bytecode) (groups : List FixupTarget)
    (guard : Usize) (condition old target : U32)
    (found : code[guard.val]? = some (.JumpIfZero condition old)) :
    resolvedCode (code.set guard.val (.JumpIfZero condition target)) groups =
      resolvedCode code (⟨[guard], target⟩ :: groups) := by
  simp only [resolvedCode, patchCode, found, retarget]

/-- The actual ELSE update resolves its guard and appends one forward skip.
The resolved view of the completed then body is preserved as an exact prefix. -/
theorem resolvedCode_else_live (code : List Bytecode) (groups : List FixupTarget)
    (fixups : List Usize) (guard site : Usize) (condition old noEntry exit : U32)
    (found : code[guard.val]? = some (.JumpIfZero condition old))
    (position : site.val = code.length)
    (inside : FixupsInside (⟨fixups, exit⟩ :: groups) code.length) :
    resolvedCode ((code ++ [runtime.bytecode.Instr.Jump core.num.U32.MAX]).set guard.val (.JumpIfZero condition noEntry))
      (⟨fixups ++ [site], exit⟩ :: groups) =
      resolvedCode code (⟨[guard], noEntry⟩ :: ⟨fixups, exit⟩ :: groups) ++ [.Jump exit] := by
  have guardBound := (List.getElem?_eq_some_iff.mp found).1
  rw [List.set_append_left guard.val _ guardBound]
  have inside' : FixupsInside ([] ++ ⟨fixups, exit⟩ :: groups)
      (code.set guard.val (.JumpIfZero condition noEntry)).length := by
    simpa using inside
  have eq := resolvedCode_new_branch (code.set guard.val (.JumpIfZero condition noEntry)) [] [] groups
    ⟨fixups, exit⟩ .jump core.num.U32.MAX site (by simpa using position) inside'
  simpa only [List.append_nil, List.nil_append, BranchKind.instruction,
    resolvedCode_guard_set code (⟨fixups, exit⟩ :: groups) guard condition old noEntry found] using eq

end Itasca.Runtime.Code
