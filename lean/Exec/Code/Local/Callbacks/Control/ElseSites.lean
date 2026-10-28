import Exec.Code.Local.Control.Control.UniversalBranch
import Exec.Code.Local.Callbacks.Control.ElsePrefix
namespace Itasca.Runtime.Code
open Aeneas.Std

theorem FrameSites.set_guard {code frame} (valid : FrameSites code frame)
    (guard : Usize) (condition old target : U32)
    (found : code[guard.val]? = some (.JumpIfZero condition old)) :
    FrameSites (code.set guard.val (.JumpIfZero condition target)) frame := by
  have changed := valid.patch [guard] target
  simpa [patchCode, found, retarget] using changed

theorem FrameSites.else_live {code frame} (valid : FrameSites code frame)
    (guard site : Usize) (condition old noEntry : U32) (fixups : alloc.vec.Vec Usize)
    (found : code[guard.val]? = some (.JumpIfZero condition old))
    (position : site.val = code.length) (appended : fixups.val = frame.fixups.val ++ [site]) :
    FrameSites ((code ++ [runtime.bytecode.Instr.Jump core.num.U32.MAX]).set guard.val (.JumpIfZero condition noEntry))
      {frame with kind := .Else, if_pc := none, end_reachable := true, fixups} := by
  have marked := valid.add_branch 0#u32 0#u32 0#u32 core.num.U32.MAX site fixups appended
    (by simpa using position)
  have branches : FrameSites (code ++ [runtime.bytecode.Instr.Jump core.num.U32.MAX])
      {frame with end_reachable := true, fixups} := by
    simpa [branchInstructions] using marked
  have atGuard : (code ++ [runtime.bytecode.Instr.Jump core.num.U32.MAX])[guard.val]? =
      some (.JumpIfZero condition old) := fetch_extend found _
  have patched := branches.set_guard guard condition old noEntry atGuard
  exact ⟨patched.branches, by simp⟩

theorem FrameSites.else_dead {code frame} (valid : FrameSites code frame)
    (guard : Usize) (condition old noEntry : U32)
    (found : code[guard.val]? = some (.JumpIfZero condition old)) :
    FrameSites (code.set guard.val (.JumpIfZero condition noEntry))
      {frame with kind := .Else, if_pc := none} := by
  have patched := valid.set_guard guard condition old noEntry found
  exact ⟨patched.branches, by simp⟩

end Itasca.Runtime.Code
