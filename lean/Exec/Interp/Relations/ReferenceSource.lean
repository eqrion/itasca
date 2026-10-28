import Exec.Interp.Relations.ReferenceNull
import Exec.Interp.Relations.WordEncoding
import Exec.Spec.References
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
