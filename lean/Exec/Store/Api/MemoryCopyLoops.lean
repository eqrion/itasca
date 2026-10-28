import Exec.Store.Initialization.BulkMemory
import Exec.Spec.CopyInterval
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Forward overlap copying retains unread source bytes, so its result uses
the source bytes as they were before the loop. -/
theorem memory_copy_forward (before : Slice U8) (destination source : Usize) (count : U64)
    (direction : destination.val ≤ source.val)
    (sourceBound : source.val+count.val ≤ before.length)
    (targetBound : destination.val+count.val ≤ before.length) :
    runtime.interp.bulk.execute_loop0 count destination source before 0#usize ⦃ after =>
      after.val = before.val.setSlice! destination.val (before.val.slice source.val (source.val+count.val)) ⦄ := by
  have countBound : count.val ≤ Usize.max := by have := before.property; scalar_tac
  have castCount := Interp.cast_usize_exact count countBound
  unfold runtime.interp.bulk.execute_loop0
  apply loop.spec_decr_nat (fun state => count.val-state.2.val)
    (fun state => state.2.val ≤ count.val ∧ Spec.Segment.CopyPrefix before.val state.1.val destination.val source.val state.2.val)
  · rintro ⟨current,index⟩ ⟨upper,copyState⟩
    dsimp only at upper copyState ⊢
    unfold runtime.interp.bulk.execute_loop0.body
    simp only [lift,bind_ok]
    split
    · rename_i more
      have less : index.val<count.val := by simpa only [UScalar.lt_equiv,castCount] using more
      have sourceInside : source.val+index.val < current.length := by
        change _ < current.val.length
        rw [copyState.length]
        change _ < before.length
        omega
      have targetInside : destination.val+index.val < current.length := by
        change _ < current.val.length
        rw [copyState.length]
        change _ < before.length
        omega
      step as ⟨src,srcEq⟩
      step as ⟨value,valueEq⟩
      step as ⟨dst,dstEq⟩
      step as ⟨updated,updatedEq⟩
      step as ⟨next,nextEq⟩
      refine ⟨by omega,?_,by omega⟩
      have updatedValues : updated.val = current.val.set (destination.val+index.val) current.val[source.val+index.val]! := by
        rw [updatedEq]
        simp only [Slice.set_val_eq,srcEq,dstEq,valueEq]
        congr 1
        exact (getElem!_pos current.val (source.val+index.val) sourceInside).symm
      have relation := copyState.write direction (by change _ < before.length; omega) (by change _ < before.length; omega)
      simpa only [updatedValues,nextEq] using relation
    · rename_i finished
      have last : index.val=count.val := by
        have notMore : ¬ index.val<count.val := by simpa only [UScalar.lt_equiv,castCount] using finished
        omega
      simp only [WP.spec_ok]
      exact (last ▸ copyState).complete sourceBound targetBound
  · exact ⟨by simp,by simpa using Spec.Segment.CopyPrefix.initial before.val destination.val source.val⟩

/-- Backward overlap copying preserves the unread source prefix. -/
theorem memory_copy_backward (before : Slice U8) (destination source count : Usize)
    (direction : source.val ≤ destination.val)
    (sourceBound : source.val+count.val ≤ before.length)
    (targetBound : destination.val+count.val ≤ before.length) :
    runtime.interp.bulk.execute_loop1 destination source before count ⦃ after =>
      after.val = before.val.setSlice! destination.val (before.val.slice source.val (source.val+count.val)) ⦄ := by
  unfold runtime.interp.bulk.execute_loop1
  apply loop.spec_decr_nat (fun state => state.2.val)
    (fun state => state.2.val ≤ count.val ∧ Spec.Segment.CopySuffix before.val state.1.val destination.val source.val state.2.val count.val)
  · rintro ⟨current,index⟩ ⟨upper,copyState⟩
    dsimp only at upper copyState ⊢
    unfold runtime.interp.bulk.execute_loop1.body
    split
    · rename_i more
      have positive : 0 < index.val := by simpa [UScalar.lt_equiv] using more
      have sourceInside : source.val+(index.val-1) < current.length := by
        change _ < current.val.length
        rw [copyState.length]
        change _ < before.length
        omega
      have targetInside : destination.val+(index.val-1) < current.length := by
        change _ < current.val.length
        rw [copyState.length]
        change _ < before.length
        omega
      step as ⟨next,nextEq⟩
      step as ⟨src,srcEq⟩
      step as ⟨value,valueEq⟩
      step as ⟨dst,dstEq⟩
      step as ⟨updated,updatedEq⟩
      refine ⟨by omega,?_,by omega⟩
      have updatedValues : updated.val = current.val.set (destination.val+(index.val-1)) current.val[source.val+(index.val-1)]! := by
        rw [updatedEq]
        simp only [Slice.set_val_eq,srcEq,dstEq,valueEq,nextEq]
        congr 1
        exact (getElem!_pos current.val (source.val+(index.val-1)) sourceInside).symm
      have relation := copyState.write direction positive upper (by change _ ≤ before.length; omega) (by change _ ≤ before.length; omega)
      simpa only [updatedValues,nextEq] using relation
    · rename_i finished
      have last : index.val=0 := by
        have notMore : ¬ 0 < index.val := by simpa [UScalar.lt_equiv] using finished
        omega
      simp only [WP.spec_ok]
      exact (last ▸ copyState).complete sourceBound targetBound
  · exact ⟨Nat.le_refl _,Spec.Segment.CopySuffix.initial before.val destination.val source.val count.val⟩
end Itasca.Runtime.Store
