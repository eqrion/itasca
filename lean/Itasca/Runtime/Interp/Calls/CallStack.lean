import Itasca.Runtime.Interp.Relations.StackRelation

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Updating the active PC retains the frame's metadata and allocated region. -/
theorem FrameBinding.advance {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : Abs.AFrame}
    (binding : FrameBinding store exec raw source) (index : Usize) (pc : U32)
    (lookup : exec.frames.val[index.val]? = some raw) :
    FrameBinding store { exec with frames := exec.frames.set index { raw with pc := pc } }
      { raw with pc := pc } source := by
  obtain ⟨inst, fn, compiled, signature, identity, _, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩ := binding
  refine ⟨inst, fn, compiled, signature, identity, ?_, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩
  have within := (List.getElem?_eq_some_iff.mp lookup).1
  simp only [alloc.vec.Vec.set_val_eq]
  apply List.mem_of_getElem? (i := index.val)
  simp [within]

/-- Fetch changes only the last frame's PC. All older frame bindings survive. -/
theorem FrameBinding.advance_older {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw : runtime.interp.Frame} {source : Abs.AFrame}
    (binding : FrameBinding store exec raw source) (index : Usize) (updated : runtime.interp.Frame)
    (last : index.val + 1 = exec.frames.length)
    (older : raw ∈ exec.frames.val.dropLast) :
    FrameBinding store { exec with frames := exec.frames.set index updated } raw source := by
  obtain ⟨inst, fn, compiled, signature, identity, _, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩ := binding
  refine ⟨inst, fn, compiled, signature, identity, ?_, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩
  simp only [alloc.vec.Vec.set_val_eq]
  have kept : (exec.frames.val.set index.val updated).dropLast = exec.frames.val.dropLast := by
    rw [List.dropLast_eq_take, List.length_set, List.take_set_of_le (by change exec.frames.length - 1 ≤ index.val; omega), ← List.dropLast_eq_take]
  exact List.mem_of_mem_dropLast (kept ▸ older)

end Itasca.Runtime.Interp
