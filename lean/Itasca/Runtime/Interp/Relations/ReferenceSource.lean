import Itasca.Runtime.Interp.Relations.InitializerExecute
import Itasca.Runtime.Interp.Relations.WordEncoding
import Itasca.Runtime.Spec.References

/-!
Reference-null execution and source encoding. The null-test result and encode/decode facts connect concrete reference words to source reference values.
-/

/-! ## Reference Null -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- The reference test compares the complete encoded word with the null
sentinel and writes exactly the canonical i32 Boolean. -/
@[step] theorem ref_is_null_effect
    (exec : runtime.interp.Execution) (base : Usize) (dst src : U32)
    (sourceBound : base.val+src.val < exec.slots.length)
    (destinationBound : base.val+dst.val < exec.slots.length) :
    runtime.interp.execute_ref_is_null exec base dst src ⦃ out =>
      out.1 = .Ok () ∧ SlotsEffect exec out.2
        (exec.slots.val.set (base.val+dst.val)
          (if exec.slots.val[base.val+src.val]! = 0#u64 then 1#u64 else 0#u64)) ⦄ := by
  unfold runtime.interp.execute_ref_is_null
  simp only [lift,bind_ok]
  step as ⟨position,positionEq⟩
  have positionVal : position.val = base.val+src.val := by simpa only [U32.cast_Usize_val_eq] using positionEq
  have found : exec.slots.val[position.val]? = some exec.slots.val[base.val+src.val]! := by
    rw [positionVal,getElem!_pos exec.slots.val _ sourceBound]
    exact List.getElem?_eq_getElem sourceBound
  step with vec_index_given exec.slots position exec.slots.val[base.val+src.val]! found as ⟨word,wordEq⟩
  simp only [wordEq]
  split <;> step* <;> simp_all [SlotsEffect,_root_.getElem!_pos]

end Itasca.Runtime.Interp

end

/-! ## Reference Source -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store

/-- The complete raw reference word uses exactly zero for either null type. -/
theorem decode_ref_is_null (ty : Itasca.types.ElemType) (word : U64) :
    Spec.referenceIsNull (decodeRef ty word) = if word = 0#u64 then 1 else 0 := by
  have zero : word = 0#u64 ↔ word.val = 0 := by scalar_tac
  by_cases null : word.val = 0 <;> cases ty <;> simp [decodeRef,decodeElemType,Spec.referenceIsNull,zero,null]

/-- Every raw reference, including the largest encoded address, re-encodes
without loss. Address validity is a separate store invariant. -/
theorem encode_decoded_ref (ty : Itasca.types.ElemType) (word : U64) :
    Code.encodeValue (refVal (decodeRef ty word)) = [word.val] := by
  cases ty
  · simpa only [decodeWords,pairWords,sourceType,reduceCtorEq,ite_false] using encode_decode_words .FuncRef word 0#u64 (by simp)
  · simpa only [decodeWords,pairWords,sourceType,reduceCtorEq,ite_false] using encode_decode_words .ExternRef word 0#u64 (by simp)

end Itasca.Runtime.Interp

end
