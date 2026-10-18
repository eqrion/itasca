import Exec.Abs.DecodeDepth
import Exec.Interp.Machines.Slice.SliceErrors

namespace Exec.Interp
open Aeneas Aeneas.Std

@[simp] theorem SavedFrames.length {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raws sources waiting base}
    (saved : SavedFrames store exec raws sources waiting base) : raws.length = sources.length := by
  induction saved with
  | nil => rfl
  | cons head tail ih => simp only [List.length_cons, ih]

theorem FrameStackRel.length {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {sources : List Abs.AFrame}
    (stack : FrameStackRel store exec sources) : exec.frames.length = sources.length := by
  cases stack with
  | empty frames => simp [alloc.vec.Vec.length, frames]
  | active frames top saved =>
    change exec.frames.val.length = _
    rw [frames, List.length_append, List.length_reverse, saved.length]
    simp

/-- The runtime frame counter is exactly the FRAME_ nesting of the decoded
configuration, excluding the ambient embedding frame. -/
theorem FrameStackRel.depth {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {source : Abs.AState}
    (stack : FrameStackRel store exec source.frames) :
    exec.frames.length = Spec.frameDepth (Abs.decode source) := by
  rw [Abs.decode_depth]
  exact stack.length

/-- A rejected direct call at the call-stack limit has reached that limit in
source FRAME_ nesting, rather than merely an internal counter. -/
theorem DirectCallCause.frame_depth {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {index : Usize}
    {raw : runtime.interp.Frame} {inst : runtime.store.Instance}
    {compiled : runtime.bytecode.CompiledFunction} {source : Abs.AState}
    (stack : FrameStackRel store exec source.frames)
    (cause : DirectCallCause allocator hooks exec store platform index raw inst compiled (.Exhausted .CallStack)) :
    store.limits.max_frames.val ≤ Spec.frameDepth (Abs.decode source) := by
  obtain ⟨target, offset, pc, address, base, function, instanceIndex, functionIndex,
    callee, code, fetch, resolved, lookup, wasm, instanceLookup, codeLookup, baseEq, pcEq, rejection⟩ := cause
  change store.limits.max_frames.val ≤ (exec.frames.set index { raw with pc := pc }).length at rejection
  simpa only [alloc.vec.Vec.set_length, stack.depth] using rejection

theorem SliceFailure.frame_depth {M P A : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {source : Abs.AState}
    (stack : FrameStackRel store exec source.frames)
    (failure : SliceFailure allocator hooks exec store platform source (.Exhausted .CallStack)) :
    store.limits.max_frames.val ≤ Spec.frameDepth (Abs.decode source) := by
  rcases failure with ⟨⟨trap, kind, _⟩, _⟩ | ⟨kind, _⟩ | rejected
  · cases kind
  · cases kind
  · obtain ⟨index, raw, inst, compiled, _, _, _, _, cause⟩ := rejected
    exact cause.concrete.frame_depth stack

end Exec.Interp
