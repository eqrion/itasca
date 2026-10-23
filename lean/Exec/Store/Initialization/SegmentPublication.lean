import Exec.Store.Initialization.SegmentCounts
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Old instance maps remain exact. New segment addresses are accounted for by
newly published instance maps; existing payloads may be dropped or modified.
This is an explicit state relation, not a law of arbitrary host callbacks. -/
structure SegmentPublication {M : Type} (before after : runtime.store.Store M) : Prop where
  instances : after.instances.val.take before.instances.length = before.instances.val
  elements : after.elems.length = before.elems.length +
    ((after.instances.val.drop before.instances.length).map fun inst => inst.elems.length).sum
  datas : after.datas.length = before.datas.length +
    ((after.instances.val.drop before.instances.length).map fun inst => inst.datas.length).sum

private theorem sum_retained {T : Type} (measure : T → Nat) {before after : List T}
    (retained : after.take before.length = before) :
    (after.map measure).sum = (before.map measure).sum + ((after.drop before.length).map measure).sum := by
  conv_lhs => rw [←List.take_append_drop before.length after]
  rw [List.map_append,List.sum_append,retained]

/-- Complete accounting on both sides determines the publication ledger.
In particular, retaining old metadata alone does not assume accounting for
newly introduced segment entries. -/
theorem SegmentPublication.of_accounting {M : Type} {before after : runtime.store.Store M}
    (instances : after.instances.val.take before.instances.length = before.instances.val)
    (old : SegmentAccounting before) (fresh : SegmentAccounting after) : SegmentPublication before after := by
  refine ⟨instances,?_,?_⟩
  · rw [fresh.elements,old.elements]
    exact sum_retained _ instances
  · rw [fresh.datas,old.datas]
    exact sum_retained _ instances

end Exec.Store
