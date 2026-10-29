import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FrameSites

/-!
At a complete callback boundary, each retained fixup was paid for by an emitted branch. Address validity alone does not imply this allocation bound.

Main declarations: `FixupBudget`. A direct consumer is `Compiler.Local.Callbacks.Fixups.FixupPreservation`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- At a complete callback boundary, each retained fixup was paid for by an
emitted branch. Address validity alone does not imply this allocation bound. -/
def FixupBudget (frames : List runtime.compiler.Frame) (codeLength : Nat) : Prop :=
  ∀ frame ∈ frames, frame.fixups.val.length ≤ codeLength

theorem FixupBudget.mono {frames before after} (budget : FixupBudget frames before)
    (growth : before ≤ after) : FixupBudget frames after :=
  fun frame member => (budget frame member).trans growth

theorem FixupBudget.empty (codeLength : Nat) : FixupBudget [] codeLength := by
  simp [FixupBudget]

theorem FixupBudget.push {frames codeLength} (budget : FixupBudget frames codeLength)
    (frame : runtime.compiler.Frame) (fresh : frame.fixups.val = []) :
    FixupBudget (frames ++ [frame]) codeLength := by
  intro f member
  rcases List.mem_append.mp member with old | last
  · exact budget f old
  · simp only [List.mem_singleton] at last
    subst f
    simp [fresh]

theorem FixupBudget.set {frames codeLength} (budget : FixupBudget frames codeLength)
    (index : Nat) (replacement : runtime.compiler.Frame)
    (bound : replacement.fixups.val.length ≤ codeLength) :
    FixupBudget (frames.set index replacement) codeLength := by
  induction frames generalizing index with
  | nil => exact .empty _
  | cons frame rest ih =>
    cases index with
    | zero =>
      intro f member
      simp only [List.set_cons_zero, List.mem_cons] at member
      rcases member with rfl | old
      · exact bound
      · exact budget f (List.mem_cons_of_mem _ old)
    | succ index =>
      intro f member
      simp only [List.set_cons_succ, List.mem_cons] at member
      rcases member with rfl | tail
      · exact budget f (by simp)
      · exact ih (fun f member => budget f (List.mem_cons_of_mem _ member)) index f tail

theorem FixupBudget.branch {frames before after} (budget : FixupBudget frames before)
    (index : Nat) (frame : runtime.compiler.Frame) (fixups : alloc.vec.Vec Usize)
    (selected : frames[index]? = some frame)
    (appended : fixups.val.length = frame.fixups.val.length + 1)
    (growth : before + 1 ≤ after) :
    FixupBudget (frames.set index {frame with end_reachable := true, fixups}) after := by
  apply (budget.mono (by omega)).set
  have old := budget frame (List.mem_of_getElem? selected)
  simp only
  omega

theorem FixupBudget.lookup {frames codeLength} (budget : FixupBudget frames codeLength)
    {index : Nat} {frame : runtime.compiler.Frame} (selected : frames[index]? = some frame) (capacity : codeLength < Usize.max) :
    frame.fixups.val.length < Usize.max :=
  (budget frame (List.mem_of_getElem? selected)).trans_lt capacity

end Itasca.Runtime.Compiler
