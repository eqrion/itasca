import Exec.Store.Api.GrowthInvariant
import Exec.Store.Invariant.ObjectExtension
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Memory growth, including refused growth, preserves source syntax and
extends the decoded store. Failed backing allocation may change the opaque
buffer representation while preserving its exact decoded bytes. -/
theorem memory_grow_extends {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws ops view)
    (code : CodeInterpretation) (s : runtime.store.Store M)
    (shape : Shape view s) (sourceSyntax : StoreSyntax code s)
    (index : Usize) (delta : U32) (inBounds : index.val < s.memories.length) :
    runtime.store.Store.grow_memory_index ops s index delta ⦃ result =>
      Shape view result.2 ∧ StoreSyntax code result.2 ∧
      Extend_store (decodeStore view code s) (decodeStore view code result.2) ⦄ := by
  obtain ⟨result, returned, freshShape⟩ := WP.spec_imp_exists
    (memory_grow_preserves_shape ops view laws code s shape index delta inBounds)
  have effect := memory_grow_effect ops view laws code s index delta inBounds
    (fun m member => (shape.memories m member).length_bound)
    (fun m member => (shape.memories m member).1)
  rw [returned] at effect ⊢
  simp only [WP.spec_ok] at effect ⊢
  have freshSyntax : StoreSyntax code result.2 := by
    rcases effect with ⟨_, _, unchanged | ⟨old, after, lookup, sameView, same⟩⟩ |
      ⟨old, after, count, lookup, bytes, used, limit, pages, maximum, oldPages, same⟩
    · simpa only [unchanged] using sourceSyntax
    · simpa only [same, StoreSyntax] using sourceSyntax
    · simpa only [same, StoreSyntax] using sourceSyntax
  refine ⟨freshShape, freshSyntax, ?_⟩
  have oldWf := decodeStore_wf view code s shape sourceSyntax
  have freshWf := decodeStore_wf view code result.2 freshShape freshSyntax
  rcases effect with ⟨_, unchanged, _⟩ |
    ⟨old, after, count, lookup, bytes, used, limit, pages, maximum, oldPages, same⟩
  · rw [unchanged]
    exact Spec.extend_store_refl _ oldWf
  · have oldShape := shape.memories old (List.mem_of_getElem? lookup)
    have length : (view old.buf).length ≤ (view after).length := by
      have lengths := congrArg List.length bytes
      simp only [List.length_append, List.length_replicate] at lengths
      change (view old.buf).val.length ≤ (view after).val.length
      omega
    have oldMemoryWf : wf_meminst (decodeMemory view old) := by
      apply wf_meminst.meminst_case_
      · apply wf_memtype.memtype_case_0
        apply decodeLimits_wf
        have bound := oldShape.2.1
        scalar_tac
      · exact decodeBytes_wf _
    have newMemoryWf : wf_meminst (decodeMemory view {old with buf := after}) := by
      apply wf_meminst.meminst_case_
      · apply wf_memtype.memtype_case_0
        apply decodeLimits_wf
        have lengths := congrArg List.length bytes
        simp only [List.length_append, List.length_replicate] at lengths
        have aligned := oldShape.1
        change (view after).length / 65536 ≤ U32.max
        scalar_tac
      · exact decodeBytes_wf _
    have objectExtension := decodeMemory_extends view old {old with buf := after} rfl length oldMemoryWf newMemoryWf
    have decoded : decodeStore view code {s with memories := s.memories.set index {old with buf := after}, memory_bytes := count} =
        {decodeStore view code s with MEMS := (s.memories.set index {old with buf := after}).val.map (decodeMemory view)} := by rfl
    rw [same] at freshWf ⊢
    rw [decoded] at freshWf ⊢
    simp only [alloc.vec.Vec.set_val_eq, List.map_set] at freshWf ⊢
    apply Spec.extend_store_set_mem _ _ _ oldWf
    · simpa only [decodeStore] using freshWf
    · intro bound
      have found : old = s.memories.val[index.val] := by
        simpa only [List.getElem?_eq_getElem inBounds, Option.some.injEq] using lookup.symm
      simpa only [decodeStore, found, getElem!_pos (s.memories.val.map (decodeMemory view)) index.val
        (by simpa only [List.length_map] using inBounds), List.getElem_map] using objectExtension
end Exec.Store
