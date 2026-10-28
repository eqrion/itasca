import Exec.Store.Api.TableFillLoop
import Exec.Spec.CopyInterval
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem table_copy_forward_same (tables : alloc.vec.Vec runtime.store.TableInst)
    (tableIndex destination source : Usize) (count : U64) (table : runtime.store.TableInst)
    (target : tables.val[tableIndex.val]? = some table)
    (direction : destination.val ≤ source.val)
    (sourceBound : source.val+count.val ≤ table.elements.length)
    (targetBound : destination.val+count.val ≤ table.elements.length) :
    runtime.interp.bulk.execute_loop4 tables count tableIndex destination tableIndex source 0#usize ⦃ out =>
      ∃ words, out = tables.set tableIndex {table with elements := words} ∧
        words.val = table.elements.val.setSlice! destination.val (table.elements.val.slice source.val (source.val+count.val)) ⦄ := by
  have tableBound := (List.getElem?_eq_some_iff.mp target).1
  have tableRead := (List.getElem?_eq_some_iff.mp target).2
  have countBound : count.val ≤ Usize.max := by have := table.elements.property; scalar_tac
  have castCount := Interp.cast_usize_exact count countBound
  unfold runtime.interp.bulk.execute_loop4
  apply loop.spec_decr_nat (fun state => count.val-state.2.val)
    (fun state => state.2.val ≤ count.val ∧ ∃ words : alloc.vec.Vec U64,
      Spec.Segment.CopyPrefix table.elements.val words.val destination.val source.val state.2.val ∧
      state.1 = tables.set tableIndex {table with elements := words})
  · rintro ⟨current,index⟩ ⟨upper,words,copyState,currentEq⟩
    dsimp only at upper copyState currentEq ⊢
    have wordLength : words.length = table.elements.length := copyState.length
    have currentFound : current.val[tableIndex.val]? = some {table with elements := words} := by
      rw [currentEq]
      simp [alloc.vec.Vec.set_val_eq,tableBound]
    have currentBound : tableIndex.val < current.length := by rw [currentEq]; simpa using tableBound
    unfold runtime.interp.bulk.execute_loop4.body
    simp only [lift,bind_ok]
    split
    · rename_i more
      have less : index.val < count.val := by simpa only [UScalar.lt_equiv,castCount] using more
      have sourceInside : source.val+index.val < words.length := by omega
      have targetInside : destination.val+index.val < words.length := by omega
      step with Interp.vec_index_given current tableIndex {table with elements := words} currentFound as ⟨actual,actualEq⟩
      subst actual
      step as ⟨src,srcEq⟩
      step with Interp.vec_index_given words src words.val[source.val+index.val]!
        (by simp [srcEq,sourceInside]) as ⟨value,valueEq⟩
      step as ⟨actualTable,tableBack,actualEq,tableBackEq⟩
      have actualSame : actualTable = {table with elements := words} := by
        have h := List.getElem?_eq_getElem currentBound
        rw [currentFound] at h
        exact actualEq.trans (Option.some.inj h).symm
      subst actualTable
      step as ⟨dst,dstEq⟩
      step as ⟨old,wordsBack,oldEq,wordsBackEq⟩
      step as ⟨next,nextEq⟩
      refine ⟨by omega,⟨words.set dst value,?_,?_⟩,by omega⟩
      · have valueRead : value = words.val[source.val+index.val]! := by
          exact valueEq
        have relation := copyState.write direction (by change _ < table.elements.length; omega) (by change _ < table.elements.length; omega)
        simpa only [alloc.vec.Vec.set_val_eq,dstEq,valueRead,nextEq] using relation
      · simp only [wordsBackEq,tableBackEq,currentEq]
        apply alloc.vec.Vec.ext
        simp [alloc.vec.Vec.set_val_eq,List.set_set]
    · rename_i finished
      have last : index.val=count.val := by
        have notMore : ¬ index.val < count.val := by simpa only [UScalar.lt_equiv,castCount] using finished
        omega
      simp only [WP.spec_ok]
      exact ⟨words,currentEq,(last ▸ copyState).complete sourceBound targetBound⟩
  · refine ⟨by simp,table.elements,?_,?_⟩
    · simpa using Spec.Segment.CopyPrefix.initial table.elements.val destination.val source.val
    · have same : {table with elements := table.elements} = table := by cases table; rfl
      rw [same,←tableRead,vec_set_current tables tableIndex tableBound]
theorem table_copy_backward_same (tables : alloc.vec.Vec runtime.store.TableInst)
    (tableIndex destination source count : Usize) (table : runtime.store.TableInst)
    (target : tables.val[tableIndex.val]? = some table)
    (direction : source.val ≤ destination.val)
    (sourceBound : source.val+count.val ≤ table.elements.length)
    (targetBound : destination.val+count.val ≤ table.elements.length) :
    runtime.interp.bulk.execute_loop3 tables tableIndex destination tableIndex source count ⦃ out =>
      ∃ words, out = tables.set tableIndex {table with elements := words} ∧
        words.val = table.elements.val.setSlice! destination.val (table.elements.val.slice source.val (source.val+count.val)) ⦄ := by
  have tableBound := (List.getElem?_eq_some_iff.mp target).1
  have tableRead := (List.getElem?_eq_some_iff.mp target).2
  unfold runtime.interp.bulk.execute_loop3
  apply loop.spec_decr_nat (fun state => state.2.val)
    (fun state => state.2.val ≤ count.val ∧ ∃ words : alloc.vec.Vec U64,
      Spec.Segment.CopySuffix table.elements.val words.val destination.val source.val state.2.val count.val ∧
      state.1 = tables.set tableIndex {table with elements := words})
  · rintro ⟨current,index⟩ ⟨upper,words,copyState,currentEq⟩
    dsimp only at upper copyState currentEq ⊢
    have wordLength : words.length = table.elements.length := copyState.length
    have currentFound : current.val[tableIndex.val]? = some {table with elements := words} := by
      rw [currentEq]
      simp [alloc.vec.Vec.set_val_eq,tableBound]
    have currentBound : tableIndex.val < current.length := by rw [currentEq]; simpa using tableBound
    unfold runtime.interp.bulk.execute_loop3.body
    split
    · rename_i more
      have positive : 0 < index.val := by simpa [UScalar.lt_equiv] using more
      have sourceInside : source.val+(index.val-1) < words.length := by omega
      have targetInside : destination.val+(index.val-1) < words.length := by omega
      step as ⟨next,nextEq⟩
      step with Interp.vec_index_given current tableIndex {table with elements := words} currentFound as ⟨actual,actualEq⟩
      subst actual
      step as ⟨src,srcEq⟩
      step with Interp.vec_index_given words src words.val[source.val+(index.val-1)]!
        (by simp [srcEq,nextEq,sourceInside]) as ⟨value,valueEq⟩
      step as ⟨actualTable,tableBack,actualEq,tableBackEq⟩
      have actualSame : actualTable = {table with elements := words} := by
        have h := List.getElem?_eq_getElem currentBound
        rw [currentFound] at h
        exact actualEq.trans (Option.some.inj h).symm
      subst actualTable
      step as ⟨dst,dstEq⟩
      step as ⟨old,wordsBack,oldEq,wordsBackEq⟩
      refine ⟨by omega,⟨words.set dst value,?_,?_⟩,by omega⟩
      · have valueRead : value = words.val[source.val+(index.val-1)]! := by
          exact valueEq
        have relation := copyState.write direction positive upper (by change _ ≤ table.elements.length; omega) (by change _ ≤ table.elements.length; omega)
        simpa only [alloc.vec.Vec.set_val_eq,dstEq,valueRead,nextEq] using relation
      · simp only [wordsBackEq,tableBackEq,currentEq]
        apply alloc.vec.Vec.ext
        simp [alloc.vec.Vec.set_val_eq,List.set_set]
    · rename_i finished
      have last : index.val=0 := by
        have notMore : ¬ 0 < index.val := by simpa [UScalar.lt_equiv] using finished
        omega
      simp only [WP.spec_ok]
      exact ⟨words,currentEq,(last ▸ copyState).complete sourceBound targetBound⟩
  · refine ⟨Nat.le_refl _,table.elements,?_,?_⟩
    · simpa using Spec.Segment.CopySuffix.initial table.elements.val destination.val source.val count.val
    · have same : {table with elements := table.elements} = table := by cases table; rfl
      rw [same,←tableRead,vec_set_current tables tableIndex tableBound]
end Itasca.Runtime.Store
