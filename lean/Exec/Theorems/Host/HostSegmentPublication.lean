import Exec.Theorems.Api.ExecutableInv
import Exec.Interp.Relations.FrameStorePrefix
import Exec.Store.Initialization.SegmentPublication
namespace Exec.Interp
open Aeneas Aeneas.Std
/-- A generic frame prefix plus explicit accounting at both endpoints allows
publication; no payload preservation is required. -/
theorem FrameStorePrefix.segment_publication {M : Type}
    {before after : runtime.store.Store M} (retained : FrameStorePrefix before after)
    (old : Store.SegmentAccounting before) (fresh : Store.SegmentAccounting after) :
    Store.SegmentPublication before after :=
  .of_accounting retained.instances old fresh
end Exec.Interp

namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- Explicit complete-invariant retention and raw frame-prefix retention give
an exact segment publication ledger, including host-created instances. No
segment-count equality or host semantic law is inferred from source extension. -/
theorem ExecutableInv.segment_publication {M : Type} {view : M → Slice U8}
    {oldCode newCode : Store.CodeInterpretation} {before after : runtime.store.Store M}
    (old : ExecutableInv view oldCode before) (fresh : ExecutableInv view newCode after)
    (retained : Interp.FrameStorePrefix before after) : Store.SegmentPublication before after :=
  .of_accounting retained.instances old.segmentAccounting fresh.segmentAccounting

/-- Existing segment maps stay attached to their exact old instance; both
kinds of issued segment addresses remain in bounds even after publication. -/
theorem retained_instance_segment_maps {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} (published : Store.SegmentPublication before after)
    (shape : Store.Shape view before) {index : Nat} {inst : runtime.store.ModuleInst}
    (found : before.instances.val[index]? = some inst) :
    after.instances.val[index]? = some inst ∧
    (∀ address ∈ inst.elems.val, address.val < after.elems.length) ∧
    (∀ address ∈ inst.datas.val, address.val < after.datas.length) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,elements,datas⟩ := shape.instances inst (List.mem_of_getElem? found)
  exact ⟨published.instance_lookup found,
    fun address member => (elements address member).trans_le published.element_count,
    fun address member => (datas address member).trans_le published.data_count⟩

/-- Initialization followed by a publishing callback composes additively,
without requiring either payload-vector equality or fixed segment counts. -/
theorem initialization_host_segment_accounting {M : Type}
    {before initialized after : runtime.store.Store M}
    (old : Store.SegmentAccounting before)
    (counts : Store.SegmentCounts before initialized)
    (instances : initialized.instances = before.instances)
    (published : Store.SegmentPublication initialized after) :
    Store.SegmentPublication before after ∧ Store.SegmentAccounting after := by
  have all := (counts.publication instances).trans published
  exact ⟨all,all.accounting old⟩
end Exec.Theorems
