import Exec.Interp.StructuredMachine.FrameStack
import Exec.Abs.DecodeDepth
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std

@[simp] theorem SavedFrames.length {M : Type} {store : runtime.store.Store M}
    {sourceStore exec raws sources waiting base}
    (saved : SavedFrames store sourceStore exec raws sources waiting base) :
    raws.length = sources.length := by
  induction saved with
  | nil => rfl
  | cons head tail ih => simp only [List.length_cons, ih]

theorem FrameStackRel.length {M : Type} {store : runtime.store.Store M}
    {sourceStore exec sources} (stack : FrameStackRel store sourceStore exec sources) :
    exec.frames.length = sources.length := by
  cases stack with
  | empty frames => simp [alloc.vec.Vec.length, frames]
  | active frames top saved =>
    change exec.frames.val.length = _
    rw [frames, List.length_append, List.length_reverse, saved.length]
    simp

/-- The concrete counter is exactly the decoded configuration's FRAME_ depth. -/
theorem FrameStackRel.depth {M : Type} {store : runtime.store.Store M}
    {sourceStore exec} {source : Abs.AState}
    (stack : FrameStackRel store sourceStore exec source.frames) :
    exec.frames.length = Spec.frameDepth (Abs.decode source) := by
  rw [Abs.decode_depth]
  exact stack.length
end Exec.Interp.StructuredMachine
