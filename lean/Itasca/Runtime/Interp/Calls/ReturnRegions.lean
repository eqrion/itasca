import Itasca.Runtime.Interp.Relations.Regions

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Successful return places exactly the source result words at the callee
base, including the zero-result and overlapping-copy cases. -/
theorem ReturnEffect.results {before after : runtime.interp.Execution}
    {base src count : Nat} {values : List val}
    (effect : ReturnEffect before after base src count)
    (represented : ValuesAt before.slots.val (base + src) values)
    (width : count = Code.slots (values.map Code.valueType))
    (bounds : base + src + count ≤ before.slots.length) :
    ValuesAt after.slots.val base values := by
  rw [ValuesAt, effect.1]
  have size : (Code.encodeValues values).length = count := by rw [Code.encodeValues_length, width]
  have copied := represented.copy base (Or.inl (by omega)) (by rw [size]; exact Nat.le_trans (by omega) bounds)
  simpa only [size] using copied

/-- Return preserves every region below the return destination. -/
theorem ReturnEffect.preserve_prefix {before after : runtime.interp.Execution}
    {base src count position : Nat} {bits : List Nat}
    (effect : ReturnEffect before after base src count)
    (represented : WordsAt before.slots.val position bits)
    (below : position + bits.length ≤ base)
    (bounds : base + src + count ≤ before.slots.length) :
    WordsAt after.slots.val position bits := by
  change base + src + count ≤ before.slots.val.length at bounds
  rw [effect.1]
  apply represented.copy_preserves base (base + src) count (Or.inl (by omega)) bounds (by omega)
  intro j hj
  exact Or.inl (by omega)

/-- The caller's saved values and the copied results form its resumed stack. -/
theorem ReturnEffect.resume {before after : runtime.interp.Execution}
    {base src count : Nat} {raw : runtime.interp.Frame} {caller : Abs.AFrame} {results : List val}
    (effect : ReturnEffect before after base src count)
    (saved : FrameSlots before raw caller)
    (represented : ValuesAt before.slots.val (base + src) results)
    (width : count = Code.slots (results.map Code.valueType))
    (destination : base = raw.base.val + Code.slots ((caller.locals ++ caller.vals).map Code.valueType))
    (bounds : base + src + count ≤ before.slots.length) :
    FrameSlots after raw { caller with vals := caller.vals ++ results } := by
  have kept := effect.preserve_prefix saved (by rw [Code.encodeValues_length, destination]) bounds
  have values := effect.results represented width bounds
  have combined := WordsAt.append kept (by simpa only [ValuesAt, Code.encodeValues_length, ← destination] using values)
  simpa only [FrameSlots, ValuesAt, Code.encodeValues_append, List.append_assoc] using combined

/-- The popped concrete frame is exactly the most recently entered callee. -/
theorem ReturnEffect.frames {before after : runtime.interp.Execution}
    {base src count : Nat} {frames : List runtime.interp.Frame} {top : runtime.interp.Frame}
    (effect : ReturnEffect before after base src count)
    (stack : before.frames.val = frames ++ [top]) : after.frames.val = frames := by
  rw [effect.2.1, stack, List.dropLast_concat]

/-- Surviving frames retain their bindings and allocated capacity. -/
theorem ReturnEffect.preserve_binding {M : Type} {store : runtime.store.Store M}
    {before after : runtime.interp.Execution} {base src count : Nat}
    {raw : runtime.interp.Frame} {source : Abs.AFrame}
    (effect : ReturnEffect before after base src count)
    (binding : FrameBinding store before raw source)
    (member : raw ∈ before.frames.val.dropLast) : FrameBinding store after raw source := by
  obtain ⟨inst, fn, compiled, signature, identity, _, hi, hf, hw, hc, hs, hm, hr, hl, bound⟩ := binding
  refine ⟨inst, fn, compiled, signature, ?_, ?_, hi, hf, hw, hc, hs, hm, hr, hl, ?_⟩
  · exact (congrArg runtime.interp.Execution.store effect.2.2).trans identity
  · simpa only [effect.2.1] using member
  · change raw.base.val + compiled.slot_count.val ≤ after.slots.val.length
    rw [effect.1, copyWords_length]
    exact bound

end Itasca.Runtime.Interp
