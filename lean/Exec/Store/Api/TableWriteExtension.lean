import Exec.Store.Invariant.SemanticApi
import Exec.Store.Invariant.Typing
import Exec.Spec.Mutation
namespace Exec.Store
open Aeneas Aeneas.Std

/-- A correctly typed public table write extends the decoded store and retains
its structural and source-syntax invariants. -/
theorem table_write_extends {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (shape : Shape view s) (sourceSyntax : StoreSyntax code s)
    (tableIndex : Usize) (index : U32) (value : runtime.Value)
    (htable : tableIndex.val < s.tables.length)
    (hindex : index.val < (s.tables.val[tableIndex.val]).elements.length)
    (htype : elementValueType (s.tables.val[tableIndex.val]).ty = Interp.rawType value)
    (owned : ValueInStore s value) :
    runtime.store.Store.set_table ops s ⟨s.id, tableIndex⟩ index value ⦃ answer =>
      answer.1 = .Ok () ∧ Shape view answer.2 ∧ StoreSyntax code answer.2 ∧
      Extend_store (decodeStore view code s) (decodeStore view code answer.2) ⦄ := by
  obtain ⟨answer, returned, freshShape⟩ := WP.spec_imp_exists
    (table_write_preserves_shape ops view s shape tableIndex index value htable hindex htype owned)
  have effect := table_write ops s tableIndex index value htable hindex htype owned
  rw [returned] at effect ⊢
  simp only [WP.spec_ok] at effect ⊢
  obtain ⟨words, encoded, same⟩ := effect
  rw [same] at freshShape ⊢
  let old := s.tables.val[tableIndex.val]
  let newTable := {old with elements := old.elements.set (UScalar.cast .Usize index) words.1}
  let fresh := {s with tables := s.tables.set tableIndex newTable}
  have freshSyntax : StoreSyntax code fresh := sourceSyntax
  have oldWf := decodeStore_wf view code s shape sourceSyntax
  have freshWf := decodeStore_wf view code fresh freshShape freshSyntax
  have oldBound : old.elements.length ≤ U32.max := (shape.tables old (List.getElem_mem htable)).1
  have oldTableWf : wf_tableinst (decodeTable old) :=
    .tableinst_case_ _ _ (.tabletype_case_0 _ _ (decodeLimits_wf _ _ oldBound))
  have newTableWf : wf_tableinst (decodeTable newTable) := by
    apply wf_tableinst.tableinst_case_
    apply wf_tabletype.tabletype_case_0
    apply decodeLimits_wf
    simpa only [newTable, alloc.vec.Vec.set_length] using oldBound
  have objectExtension : Extend_tableinst (decodeTable old) (decodeTable newTable) := by
    unfold decodeTable at oldTableWf newTableWf ⊢
    simp only [newTable, alloc.vec.Vec.set_length, decodeLimits_option] at oldTableWf newTableWf ⊢
    exact .mk_Extend_tableinst _ _ _ _ _ _ (Nat.le_refl _) (by simp)
      oldTableWf newTableWf
  refine ⟨rfl, freshShape, freshSyntax, ?_⟩
  change Extend_store (decodeStore view code s) (decodeStore view code fresh)
  change wf_store (decodeStore view code {s with tables := s.tables.set tableIndex newTable}) at freshWf
  change Extend_store (decodeStore view code s) (decodeStore view code {s with tables := s.tables.set tableIndex newTable})
  rw [decodeStore_table_update view code s (s.tables.set tableIndex newTable)] at freshWf ⊢
  simp only [alloc.vec.Vec.set_val_eq, List.map_set] at freshWf ⊢
  apply Spec.extend_store_set_table _ _ _ oldWf
  · simpa only [decodeStore] using freshWf
  · intro bound
    simpa only [decodeStore, getElem!_pos (s.tables.val.map decodeTable) tableIndex.val
      (by simpa only [List.length_map] using htable), List.getElem_map, old] using objectExtension
end Exec.Store
