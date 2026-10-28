import Itasca.Runtime.Store.Initialization.SegmentAccounting

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Instruction execution may drop segment payloads while retaining the number
of issued segment addresses. -/
structure SegmentCounts {M : Type} (before after : runtime.store.Store M) : Prop where
  elements : after.elems.length = before.elems.length
  datas : after.datas.length = before.datas.length

theorem SegmentCounts.accounting {M : Type} {before after : runtime.store.Store M}
    (counts : SegmentCounts before after) (instances : after.instances = before.instances)
    (accounted : SegmentAccounting before) : SegmentAccounting after := by
  constructor
  · simpa only [counts.elements,instances] using accounted.elements
  · simpa only [counts.datas,instances] using accounted.datas

end Itasca.Runtime.Store
