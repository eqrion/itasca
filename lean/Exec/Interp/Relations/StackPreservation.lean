import Exec.Interp.Relations.StackRelation

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Unchanged store identity, retained membership, and nonshrinking storage
preserve all frame metadata and allocation facts. -/
theorem FrameBinding.retain {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {raw source}
    (binding : FrameBinding store before raw source)
    (identity : after.store = before.store)
    (member : raw ∈ after.frames.val)
    (capacity : before.slots.length ≤ after.slots.length) :
    FrameBinding store after raw source := by
  obtain ⟨inst, fn, compiled, signature, oldIdentity, _, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩ := binding
  exact ⟨inst, fn, compiled, signature, identity.trans oldIdentity, member,
    hi, hf, hw, hc, hs, hm, hr, hl, bound.trans capacity⟩

end Exec.Interp
