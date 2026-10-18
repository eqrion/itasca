import Exec.Interp.Relations.StackRelation

namespace Exec.Interp
open Aeneas Aeneas.Std

theorem FrameBinding.member {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raw source}
    (binding : FrameBinding store exec raw source) : raw ∈ exec.frames.val := by
  obtain ⟨_, _, _, _, _, member, _⟩ := binding
  exact member

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

/-- Updating one word in the active frame preserves every suspended region
below that frame's base. -/
theorem SavedFrames.write_slot {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {raws sources waiting base}
    (saved : SavedFrames store exec raws sources waiting base)
    (index : Usize) (word : U64) (above : base ≤ index.val) :
    SavedFrames store { exec with slots := exec.slots.set index word } raws sources waiting base := by
  apply saved.transport
  · intro raw source binding _
    apply binding.retain (after := { exec with slots := exec.slots.set index word }) rfl
      binding.member
    change exec.slots.val.length ≤ (exec.slots.set index word).val.length
    simp only [alloc.vec.Vec.set_val_eq, List.length_set, Nat.le_refl]
  · intro position bits represented below
    simp only [alloc.vec.Vec.set_val_eq]
    exact represented.set_outside index.val word (Or.inr (below.trans above))

/-- An ordinary active-frame iteration preserves the complete stack once its
local effect and unchanged caller prefix have been established. -/
theorem FrameStackRel.step_active {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {source updatedSource : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : FrameStackRel store before (source :: rest))
    (raw updated : runtime.interp.Frame)
    (top : before.frames.val.getLast? = some raw)
    (frames : after.frames.val = before.frames.val.dropLast ++ [updated])
    (sameBase : updated.base = raw.base)
    (sameReturns : updatedSource.resultTypes = source.resultTypes)
    (identity : after.store = before.store)
    (capacity : before.slots.length ≤ after.slots.length)
    (preserve : ∀ position bits, WordsAt before.slots.val position bits →
      position + bits.length ≤ raw.base.val → WordsAt after.slots.val position bits)
    (active : ActiveFrame store after updated updatedSource) :
    FrameStackRel store after (updatedSource :: rest) := by
  cases relation with
  | @active actual _ raws _ oldFrames oldActive saved =>
    have same : actual = raw := by simpa only [oldFrames, List.getLast?_concat, Option.some.injEq] using top
    subst actual
    have remaining : before.frames.val.dropLast = raws.reverse := by rw [oldFrames, List.dropLast_concat]
    apply FrameStackRel.active (raw := updated) (raws := raws)
    · simpa only [remaining] using frames
    · exact active
    · rw [sameReturns, sameBase]
      apply saved.transport
      · intro frame source binding member
        apply binding.retain identity _ capacity
        rw [frames, remaining]
        exact List.mem_append_left _ (List.mem_reverse.mpr member)
      · exact preserve

end Exec.Interp
