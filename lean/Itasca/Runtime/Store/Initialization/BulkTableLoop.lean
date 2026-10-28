import Itasca.Runtime.Store.Initialization.BulkDrop
import Itasca.Runtime.Store.Invariant.InvalidWrite
import Itasca.Runtime.Interp.Relations.Range

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Copy from an independent element segment. The recursion records exactly the
left-to-right writes made by table.init. -/
def copySegment (before source : List U64) (dst src : Nat) : Nat → List U64
  | 0 => before
  | n + 1 => (copySegment before source dst src n).set (dst + n) source[src + n]!

theorem copySegment_length (before source : List U64) (dst src count : Nat) :
    (copySegment before source dst src count).length = before.length := by
  induction count with
  | zero => rfl
  | succ n ih => simp only [copySegment, List.length_set, ih]

theorem table_init_loop (tables : alloc.vec.Vec runtime.store.TableInst)
    (instances : alloc.vec.Vec runtime.store.ModuleInst)
    (elements : alloc.vec.Vec runtime.store.ElemInst)
    (instIndex : Usize) (elemIndex : U32) (len : U64) (tableIndex : Usize)
    (dst src : core.ops.range.Range Usize) (inst : runtime.store.ModuleInst)
    (address : Usize) (segment : runtime.store.ElemInst) (table : runtime.store.TableInst)
    (found : instances.val[instIndex.val]? = some inst)
    (mapped : inst.elems.val[elemIndex.val]? = some address)
    (resolved : elements.val[address.val]? = some segment)
    (target : tables.val[tableIndex.val]? = some table)
    (sourceBound : src.start.val + len.val ≤ segment.refs.length)
    (targetBound : dst.start.val + len.val ≤ table.elements.length) :
    runtime.interp.bulk.execute_loop6 tables instances elements instIndex elemIndex len
      tableIndex dst src 0#usize ⦃ out => ∃ words,
        out = tables.set tableIndex {table with elements := words} ∧
        words.val = copySegment table.elements.val segment.refs.val dst.start.val src.start.val len.val ⦄ := by
  have tableBound : tableIndex.val < tables.length := (List.getElem?_eq_some_iff.mp target).1
  have tableRead : tables.val[tableIndex.val] = table := (List.getElem?_eq_some_iff.mp target).2
  have lengthBound : len.val ≤ Usize.max := by
    have h : segment.refs.length ≤ Usize.max := segment.refs.property
    omega
  have castLength := Interp.cast_usize_exact len lengthBound
  unfold runtime.interp.bulk.execute_loop6
  apply loop.spec_decr_nat (fun state => len.val - state.2.val)
    (fun state => state.2.val ≤ len.val ∧ ∃ words : alloc.vec.Vec U64,
      words.val = copySegment table.elements.val segment.refs.val dst.start.val src.start.val state.2.val ∧
      state.1 = tables.set tableIndex {table with elements := words})
  · rintro ⟨current, index⟩ ⟨indexBound, words, wordValues, currentEq⟩
    dsimp only at indexBound wordValues currentEq ⊢
    have wordLength : words.length = table.elements.length := by
      simpa only [alloc.vec.Vec.length] using congrArg List.length wordValues |>.trans
        (copySegment_length _ _ _ _ _)
    have currentFound : current.val[tableIndex.val]? = some {table with elements := words} := by
      rw [currentEq]
      simp [alloc.vec.Vec.set_val_eq, tableBound]
    unfold runtime.interp.bulk.execute_loop6.body
    simp only [lift, bind_ok]
    split
    · rename_i more
      have less : index.val < len.val := by simpa only [UScalar.lt_equiv, castLength] using more
      step with Interp.vec_index_given instances instIndex inst found as ⟨actual, actualEq⟩
      subst actual
      step with Interp.vec_index_given inst.elems (UScalar.cast .Usize elemIndex) address
        (by simpa using mapped) as ⟨actual, actualEq⟩
      subst actual
      step with Interp.vec_index_given elements address segment resolved as ⟨actual, actualEq⟩
      subst actual
      have sourceInside : src.start.val + index.val < segment.refs.length := by omega
      have targetInside : dst.start.val + index.val < words.length := by omega
      have currentBound : tableIndex.val < current.length := by rw [currentEq]; simpa using tableBound
      step as ⟨sourcePosition, sourcePositionEq⟩
      step with Interp.vec_index_given segment.refs sourcePosition
        segment.refs.val[src.start.val + index.val]!
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
        have sourceInside : src.start.val + index.val < segment.refs.val.length := by omega
        have valueSame : value = segment.refs.val[src.start.val + index.val]! := by
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
