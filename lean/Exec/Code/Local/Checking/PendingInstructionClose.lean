import Exec.Code.Local.Checking.OpenInstructionPatch

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Exact pending sites owned by one physical frame. IF guards are patched
before its ordinary forward-branch fixups. -/
def frameInstructionSites (frame : runtime.compiler.Frame) : List Usize :=
  frame.if_pc.toList++frame.fixups.val

/-- Once all sites of the popped frame have been patched, any remaining
pending instruction still has an owner in the retained physical frame stack. -/
theorem pending_instruction_pop {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (frame : runtime.compiler.Frame) (rest : alloc.vec.Vec runtime.compiler.Frame)
    (beforeFrames : before.frames.val = rest.val++[frame]) (afterFrames : after.frames = rest)
    (index : Nat) (unpatched : ∀ site ∈ frameInstructionSites frame, site.val ≠ index)
    (owned : PendingInstructionSite before index) : PendingInstructionSite after index := by
  obtain ⟨owner,member,site,position,kind⟩ := owned
  rw [beforeFrames] at member
  rcases List.mem_append.mp member with remaining | closing
  · exact ⟨owner,by simpa only [afterFrames] using remaining,site,position,kind⟩
  · have same : owner = frame := by simpa only [List.mem_singleton] using closing
    subst owner
    have selected : site ∈ frameInstructionSites frame := by
      rcases kind with guard | branch
      · simp [frameInstructionSites,guard]
      · exact List.mem_append_right _ branch
    exact False.elim (unpatched site selected position)

/-- Popping and patching a complete frame preserves checks of every stored
instruction, including instructions skipped by source reachability. -/
theorem compiler_instruction_prefix_close {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : CompilerInstructionPrefix before) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (beforeFrames : before.frames.val = rest.val++[frame]) (afterFrames : after.frames = rest)
    (growth : InstructionCheckExtends before.function after.function)
    (code : after.function.code.val = patchCode before.function.code.val (frameInstructionSites frame) target)
    (inside : target.val ≤ after.function.code.length) : CompilerInstructionPrefix after :=
  held.patch growth (frameInstructionSites frame) target code inside
    (pending_instruction_pop frame rest beforeFrames afterFrames)

end Exec.Code
