import Exec.Store.Initialization.SegmentAccounting

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Instruction execution may drop segment payloads while retaining the number
of issued segment addresses. -/
structure SegmentCounts {M : Type} (before after : runtime.store.Store M) : Prop where
  elements : after.elems.length = before.elems.length
  datas : after.datas.length = before.datas.length

theorem SegmentCounts.refl {M : Type} (store : runtime.store.Store M) : SegmentCounts store store := ⟨rfl,rfl⟩

theorem SegmentCounts.trans {M : Type} {a b c : runtime.store.Store M}
    (first : SegmentCounts a b) (second : SegmentCounts b c) : SegmentCounts a c :=
  ⟨second.elements.trans first.elements,second.datas.trans first.datas⟩

theorem SegmentCounts.accounting {M : Type} {before after : runtime.store.Store M}
    (counts : SegmentCounts before after) (instances : after.instances = before.instances)
    (accounted : SegmentAccounting before) : SegmentAccounting after := by
  constructor
  · simpa only [counts.elements,instances] using accounted.elements
  · simpa only [counts.datas,instances] using accounted.datas

end Exec.Store
