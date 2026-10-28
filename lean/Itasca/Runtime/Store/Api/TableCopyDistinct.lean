import Itasca.Runtime.Store.Api.TableCopyOverlap
import Itasca.Runtime.Store.Initialization.SegmentCopySlice
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem table_copy_distinct (tables : alloc.vec.Vec runtime.store.TableInst)
    (len : U64) (tableIndex sourceIndex : Usize)
    (dst src : core.ops.range.Range Usize) (sourceTable table : runtime.store.TableInst)
    (different : tableIndex.val ≠ sourceIndex.val)
    (resolved : tables.val[sourceIndex.val]? = some sourceTable)
    (target : tables.val[tableIndex.val]? = some table)
    (sourceBound : src.start.val + len.val ≤ sourceTable.elements.length)
    (targetBound : dst.start.val + len.val ≤ table.elements.length) :
    runtime.interp.bulk.execute_loop5 tables len tableIndex dst sourceIndex src 0#usize ⦃ out => ∃ words,
        out = tables.set tableIndex {table with elements := words} ∧
        words.val = copySegment table.elements.val sourceTable.elements.val dst.start.val src.start.val len.val ⦄ := by
  have tableBound : tableIndex.val < tables.length := (List.getElem?_eq_some_iff.mp target).1
  have tableRead : tables.val[tableIndex.val] = table := (List.getElem?_eq_some_iff.mp target).2
  have lengthBound : len.val ≤ Usize.max := by
    have h : sourceTable.elements.length ≤ Usize.max := sourceTable.elements.property
    omega
  have castLength := Interp.cast_usize_exact len lengthBound
  unfold runtime.interp.bulk.execute_loop5
  apply loop.spec_decr_nat (fun state => len.val - state.2.val)
    (fun state => state.2.val ≤ len.val ∧ ∃ words : alloc.vec.Vec U64,
      words.val = copySegment table.elements.val sourceTable.elements.val dst.start.val src.start.val state.2.val ∧
      state.1 = tables.set tableIndex {table with elements := words})
  · rintro ⟨current, index⟩ ⟨indexBound, words, wordValues, currentEq⟩
    dsimp only at indexBound wordValues currentEq ⊢
    have wordLength : words.length = table.elements.length := by
      simpa only [alloc.vec.Vec.length] using congrArg List.length wordValues |>.trans
        (copySegment_length _ _ _ _ _)
    have currentFound : current.val[tableIndex.val]? = some {table with elements := words} := by
      rw [currentEq]
      simp [alloc.vec.Vec.set_val_eq, tableBound]
    unfold runtime.interp.bulk.execute_loop5.body
    simp only [lift, bind_ok]
    split
    · rename_i more
      have less : index.val < len.val := by simpa only [UScalar.lt_equiv, castLength] using more
      have currentSource : current.val[sourceIndex.val]? = some sourceTable := by
        rw [currentEq]
        simpa [alloc.vec.Vec.set_val_eq,List.getElem?_set,different] using resolved
      step with Interp.vec_index_given current sourceIndex sourceTable currentSource as ⟨actual,actualEq⟩
      subst actual
      have sourceInside : src.start.val + index.val < sourceTable.elements.length := by omega
      have targetInside : dst.start.val + index.val < words.length := by omega
      have currentBound : tableIndex.val < current.length := by rw [currentEq]; simpa using tableBound
      step as ⟨sourcePosition, sourcePositionEq⟩
      step with Interp.vec_index_given sourceTable.elements sourcePosition
        sourceTable.elements.val[src.start.val + index.val]!
        (by simp [sourcePositionEq, sourceInside]) as ⟨value, valueEq⟩
      step as ⟨actualTable, tableBack, actualTableEq, tableBackEq⟩
      have actualTableSame : actualTable = {table with elements := words} := by
        have h := List.getElem?_eq_getElem currentBound
        rw [currentFound] at h
        exact actualTableEq.trans (Option.some.inj h).symm
      subst actualTable
      step as ⟨targetPosition, targetPositionEq⟩
      step as ⟨oldValue, wordsBack, oldValueEq, wordsBackEq⟩
      step as ⟨next, nextEq⟩
      refine ⟨?_, ⟨words.set targetPosition value, ?_, ?_⟩, ?_⟩
      · omega
      · simp only [alloc.vec.Vec.set_val_eq, wordValues, targetPositionEq, nextEq, copySegment]
        have sourceInside : src.start.val + index.val < sourceTable.elements.val.length := by omega
        have valueSame : value = sourceTable.elements.val[src.start.val + index.val]! := by
          exact valueEq
        rw [valueSame]
      · simp only [wordsBackEq, tableBackEq, currentEq]
        apply alloc.vec.Vec.ext
        simp [alloc.vec.Vec.set_val_eq, List.set_set]
      · omega
    · rename_i more
      have last : index.val = len.val := by
        have notMore : ¬ index.val < len.val := by simpa only [UScalar.lt_equiv, castLength] using more
        omega
      simp only [WP.spec_ok]
      exact ⟨words, currentEq, by simpa only [last] using wordValues⟩
  · refine ⟨by simp, table.elements, rfl, ?_⟩
    have same : {table with elements := table.elements} = table := by cases table; rfl
    rw [same, ← tableRead, vec_set_current tables tableIndex tableBound]

end Itasca.Runtime.Store
