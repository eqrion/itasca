import Exec.Representation.StoreInvariant
import Exec.Store.Api.Grow

namespace Exec.Store
open Aeneas Aeneas.Std

theorem check_spec {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (id : Usize) :
    runtime.store.Store.check ops s id = .ok
      (if id = s.id then .Ok () else .Err runtime.ExecError.WrongStore) := by
  by_cases h : id = s.id <;> simp [runtime.store.Store.check, h]

@[step] theorem memory_read {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (s : runtime.store.Store M) (index : Usize) (hindex : index.val < s.memories.length) :
    runtime.store.Store.memory ops s ⟨s.id, index⟩ ⦃ answer =>
      answer = .Ok (view (s.memories.val[index.val]).buf) ⦄ := by
  unfold runtime.store.Store.memory
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  step as ⟨m, hm⟩
  rw [laws.read]
  simp [hm]

/-- The mutable memory accessor exposes exactly the selected bytes. Replacing
its same-length slice changes only that decoded memory's bytes. -/
theorem memory_write_boundary {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view) (code : CodeInterpretation)
    (s : runtime.store.Store M) (index : Usize) (hindex : index.val < s.memories.length) :
    runtime.store.Store.memory_mut ops s ⟨s.id, index⟩ ⦃ answer =>
      answer.1 = .Ok (view (s.memories.val[index.val]).buf) ∧
      ∀ bytes : Slice U8, bytes.length = (view (s.memories.val[index.val]).buf).length →
        decodeStore view code (answer.2 (.Ok bytes)) =
          {decodeStore view code s with MEMS :=
            ((decodeStore view code s).MEMS.set index.val
              {decodeMemory view (s.memories.val[index.val]) with BYTES := decodeBytes bytes.val})} ⦄ := by
  unfold runtime.store.Store.memory_mut
  simp
  step as ⟨m, vecBack, hm, hvecBack⟩
  obtain ⟨back, hread, hwrite⟩ := laws.write m.buf
  rw [hread]
  simp
  constructor
  · simp [hm]
  · intro bytes hlen
    subst vecBack
    have hv : view (back bytes) = bytes := hwrite bytes (by simpa [hm] using hlen)
    rw [decodeStore_memory_update]
    simp [decodeStore, alloc.vec.Vec.set_val_eq, List.map_set, decodeMemory, hv, hm, hlen]

theorem memory_write_preserves_shape {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (s : runtime.store.Store M) (hshape : Shape view s)
    (index : Usize) (hindex : index.val < s.memories.length) :
    runtime.store.Store.memory_mut ops s ⟨s.id, index⟩ ⦃ answer =>
      ∀ bytes : Slice U8, bytes.length = (view (s.memories.val[index.val]).buf).length →
        Shape view (answer.2 (.Ok bytes)) ⦄ := by
  unfold runtime.store.Store.memory_mut
  simp
  step as ⟨m, vecBack, hm, hvecBack⟩
  obtain ⟨back, hread, hwrite⟩ := laws.write m.buf
  rw [hread]
  simp
  intro bytes hlen
  subst vecBack
  have hv : view (back bytes) = bytes := hwrite bytes (by simpa [hm] using hlen)
  apply hshape.memory_replace_same_length index hindex
  · simpa [hv] using hlen
  · simp [hm]

end Exec.Store
