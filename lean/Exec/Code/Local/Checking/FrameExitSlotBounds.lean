import Exec.Code.Local.Checking.OpenInstructionCompiler

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- A recorded forward exit retains enough slots for its result transfer even
when subsequent source instructions are unreachable and observations clear the
operand stack. Loop backedges do not set this flag. -/
def FrameExitSlotBounds (compiler : runtime.compiler.FunctionCompiler A) : Prop :=
  ∀ frame ∈ compiler.frames.val, frame.end_reachable = true →
    frame.height.val+frame.results.val ≤ compiler.function.slot_count.val

/-- Fixed frames retain recorded exits as slot capacity increases. -/
theorem FrameExitSlotBounds.retained {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : FrameExitSlotBounds before) (frames : after.frames.val = before.frames.val)
    (capacity : before.function.slot_count.val ≤ after.function.slot_count.val) : FrameExitSlotBounds after := by
  intro frame member live
  rw [frames] at member
  exact (held frame member live).trans capacity

/-- Fresh scope entry has no recorded forward exit. -/
theorem FrameExitSlotBounds.push {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : FrameExitSlotBounds before) (frame : runtime.compiler.Frame)
    (frames : after.frames.val = before.frames.val++[frame]) (fresh : frame.end_reachable = false)
    (capacity : before.function.slot_count.val ≤ after.function.slot_count.val) : FrameExitSlotBounds after := by
  intro selected member live
  rw [frames] at member
  rcases List.mem_append.mp member with old | last
  · exact (held selected old live).trans capacity
  · have same : selected = frame := by simpa only [List.mem_singleton] using last
    subst selected
    simp [fresh] at live

/-- Scope close removes one owner while retaining outer exit bounds. -/
theorem FrameExitSlotBounds.pop {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : FrameExitSlotBounds before) (frame : runtime.compiler.Frame)
    (frames : before.frames.val = after.frames.val++[frame])
    (capacity : before.function.slot_count.val ≤ after.function.slot_count.val) : FrameExitSlotBounds after := by
  intro selected member live
  exact (held selected (by rw [frames]; exact List.mem_append_left _ member) live).trans capacity

/-- An actual forward branch or live ELSE records a checked result interval.
Changing fixups does not change the selected frame's transfer geometry. -/
theorem FrameExitSlotBounds.record {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    (held : FrameExitSlotBounds before) (index : Nat) (frame : runtime.compiler.Frame)
    (fixups : alloc.vec.Vec Usize)
    (frames : after.frames.val = before.frames.val.set index {frame with end_reachable := true,fixups})
    (capacity : before.function.slot_count.val ≤ after.function.slot_count.val)
    (region : frame.height.val+frame.results.val ≤ after.function.slot_count.val) : FrameExitSlotBounds after := by
  intro selected member live
  rw [frames] at member
  rcases List.mem_or_eq_of_mem_set member with old | fresh
  · exact (held selected old live).trans capacity
  · subst selected
    exact region

end Itasca.Runtime.Code
