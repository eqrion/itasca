import Itasca.Runtime.Code.Local.Relations.Common.FutureFrames
namespace Itasca.Runtime.Code
open Aeneas.Std

/-- A future ELSE plan determines the preceding THEN plan. The completed
normal path ends before the optional skip; its guard resolves to the actual
new ELSE entry. Recorded branches remain live in the shared forward target. -/
theorem FrameFuture.before_else {afterLength beforeLength locals frame label fixups}
    (normal : Bool) (noEntry : U32)
    (future : FrameFuture afterLength locals
      {frame with kind := .Else, if_pc := none, end_reachable := frame.end_reachable || normal, fixups}
      label 0#u32)
    (kind : frame.kind = .Then)
    (order : beforeLength ≤ afterLength) (guardBound : beforeLength ≤ noEntry.val) :
    FrameFuture beforeLength locals frame
      {label with normalExit := beforeLength, cont := [], after := [], normalLive := normal} noEntry := by
  refine ⟨future.height, future.results, ?_, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro entered
    simpa [kind] using future.branchWidth entered
  · intro _
    exact order.trans (future.forwardBound (by simp))
  · simp [kind]
  · simp [kind]
  · intro marked
    exact future.marked (by simp [marked])
  · simp [kind]
  · intro _; exact guardBound

end Itasca.Runtime.Code
