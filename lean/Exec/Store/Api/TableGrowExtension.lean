import Exec.Store.Api.GrowthInvariant
import Exec.Store.Invariant.ObjectExtension
namespace Exec.Store
open Aeneas Aeneas.Std

/-- Table growth and its failure branch preserve structural validity, source
syntax, and generated store extension. The sentinel's successful zero-growth
boundary is included without classifying it as an allocator refusal. -/
theorem table_grow_extends {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (shape : Shape view s) (sourceSyntax : StoreSyntax code s)
    (index : Usize) (delta : U32) (value : U64) (inBounds : index.val < s.tables.length)
    (owned : ReferenceShape s (s.tables.val[index.val]).ty value) :
    runtime.store.Store.grow_table_index ops allocator s index delta value ⦃ result =>
      Shape view result.2 ∧ StoreSyntax code result.2 ∧
      Extend_store (decodeStore view code s) (decodeStore view code result.2) ⦄ := by
  obtain ⟨result, returned, freshShape⟩ := WP.spec_imp_exists
    (table_grow_preserves_shape ops allocator allocation view s shape index delta value inBounds owned)
  have effect := table_grow_effect ops allocator allocation s index delta value inBounds
    (fun table member => (shape.tables table member).1)
  rw [returned] at effect ⊢
  simp only [WP.spec_ok] at effect ⊢
  have freshSyntax : StoreSyntax code result.2 := by
    rcases effect with ⟨_, unchanged⟩ |
      ⟨old, elements, count, lookup, values, capacity, used, limit, maximum, same⟩
    · simpa only [unchanged] using sourceSyntax
    · simpa only [same, StoreSyntax] using sourceSyntax
  refine ⟨freshShape, freshSyntax, ?_⟩
  have oldWf := decodeStore_wf view code s shape sourceSyntax
  have freshWf := decodeStore_wf view code result.2 freshShape freshSyntax
  rcases effect with ⟨_, unchanged⟩ |
    ⟨old, elements, count, lookup, values, capacity, used, limit, maximum, same⟩
  · rw [unchanged]
    exact Spec.extend_store_refl _ oldWf
  · have oldShape := shape.tables old (List.mem_of_getElem? lookup)
    have length : old.elements.length ≤ elements.length := by
      change old.elements.val.length ≤ elements.val.length
      rw [values, List.length_append, List.length_replicate]
      omega
    have oldTableWf : wf_tableinst (decodeTable old) :=
      .tableinst_case_ _ _ (.tabletype_case_0 _ _ (decodeLimits_wf _ _ oldShape.1))
    have newTableWf : wf_tableinst (decodeTable {old with elements}) := by
      apply wf_tableinst.tableinst_case_
      apply wf_tabletype.tabletype_case_0
      apply decodeLimits_wf
      change elements.val.length ≤ U32.max
      rw [values, List.length_append, List.length_replicate]
      exact capacity
    have objectExtension := decodeTable_extends old {old with elements} rfl rfl length oldTableWf newTableWf
    have decoded : decodeStore view code {s with tables := s.tables.set index {old with elements}, table_elements := count} =
        {decodeStore view code s with TABLES := (s.tables.set index {old with elements}).val.map decodeTable} := by rfl
    rw [same] at freshWf ⊢
    rw [decoded] at freshWf ⊢
    simp only [alloc.vec.Vec.set_val_eq, List.map_set] at freshWf ⊢
    apply Spec.extend_store_set_table _ _ _ oldWf
    · simpa only [decodeStore] using freshWf
    · intro bound
      have found : old = s.tables.val[index.val] := by
        simpa only [List.getElem?_eq_getElem inBounds, Option.some.injEq] using lookup.symm
      simpa only [decodeStore, found, getElem!_pos (s.tables.val.map decodeTable) index.val
        (by simpa only [List.length_map] using inBounds), List.getElem_map] using objectExtension
end Exec.Store
