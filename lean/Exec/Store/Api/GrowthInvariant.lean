import Exec.Representation.StoreInvariant
import Exec.Store.Api.Grow

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Memory growth preserves canonical memory shape and all aggregate resource
accounting, on successful growth and on every rejection or allocation failure. -/
theorem memory_grow_preserves_shape {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hs : Shape view s) (index : Usize) (delta : U32)
    (hindex : index.val < s.memories.length) :
    runtime.store.Store.grow_memory_index ops s index delta ⦃ result => Shape view result.2 ⦄ := by
  apply WP.spec_mono (memory_grow_effect ops view laws code s index delta hindex
    (fun m hm => (hs.memories m hm).length_bound) (fun m hm => (hs.memories m hm).1))
  intro result effect
  rcases effect with ⟨_, _, frame⟩ | ⟨old, after, count, hlookup, hbytes, hcount, hlimit, hpages, hmaximum, _, hresult⟩
  · rcases frame with unchanged | ⟨old, after, hlookup, hview, hresult⟩
    · simpa [unchanged] using hs
    · have hold : old = s.memories.val[index.val] := by
        simp only [List.getElem?_eq_getElem hindex, Option.some.injEq] at hlookup
        exact hlookup.symm
      rw [hresult]
      apply hs.memory_replace_same_length index hindex _
      · simp [hview, hold]
      · simp [hold]
  · have hold : old = s.memories.val[index.val] := by
      simp only [List.getElem?_eq_getElem hindex, Option.some.injEq] at hlookup
      exact hlookup.symm
    have hbefore := hs.memories old (List.mem_of_getElem? hlookup)
    have hlength : (view after).length = (view old.buf).length + delta.val * 65536 := by
      simpa using congrArg List.length hbytes
    have hpageEq : (view after).length / 65536 = (view old.buf).length / 65536 + delta.val := by omega
    have hmemory : MemoryShape view {old with buf := after} := by
      refine ⟨?_, ?_, ?_⟩
      · have halign := hbefore.1
        simp only [Slice.length] at *
        omega
      · simpa [hpageEq] using hpages
      · intro maximum hmax
        change old.maximum = some maximum at hmax
        have hmaxBefore := hbefore.2.2 maximum hmax
        constructor
        · simp only [hmax, core.option.Option.unwrap_or] at hmaximum
          simpa [hpageEq] using hmaximum
        · exact hmaxBefore.2
    rw [hresult]
    apply hs.memory_extend index hindex _ hmemory (delta.val * 65536) ?_ count hcount hlimit
    simpa [hold] using hlength


/-- Table growth preserves reference validity, the declared limits, and exact
aggregate accounting. The initial reference must name the same store. -/
theorem table_grow_preserves_shape {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (index : Usize) (delta : U32) (value : U64)
    (hindex : index.val < s.tables.length)
    (hv : ReferenceShape s (s.tables.val[index.val]).ty value) :
    runtime.store.Store.grow_table_index ops allocator s index delta value ⦃ result => Shape view result.2 ⦄ := by
  apply WP.spec_mono (table_grow_effect ops allocator ha s index delta value hindex
    (fun t ht => (hs.tables t ht).1))
  intro result effect
  rcases effect with unchanged | ⟨old, elements, count, hlookup, hvalues, hmax, hcount, hlimit, hmaximum, hresult⟩
  · simpa [unchanged.2] using hs
  · have hold : old = s.tables.val[index.val] := by
      simp only [List.getElem?_eq_getElem hindex, Option.some.injEq] at hlookup
      exact hlookup.symm
    have hbefore := hs.tables old (List.mem_of_getElem? hlookup)
    have hlength : elements.length = old.elements.length + delta.val := by
      simpa using congrArg List.length hvalues
    have htable : TableShape s {old with elements} := by
      refine ⟨?_, ?_, ?_⟩
      · simpa [hlength] using hmax
      · intro maximum hdeclared
        change old.maximum = some maximum at hdeclared
        simp only [hdeclared, core.option.Option.unwrap_or] at hmaximum
        simpa [hlength] using hmaximum
      · intro word hword
        change word ∈ elements.val at hword
        rw [hvalues] at hword
        rcases List.mem_append.mp hword with before | added
        · exact hbefore.2.2 word before
        · have heq := List.eq_of_mem_replicate added
          subst word
          simpa [hold] using hv
    rw [hresult]
    apply hs.table_extend index hindex _ htable delta.val ?_ count hcount hlimit
    simpa [hold] using hlength

end Exec.Store
