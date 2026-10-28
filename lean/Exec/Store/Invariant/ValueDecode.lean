import Exec.Store.Invariant.ValueShape
import Exec.Interp.Relations.DecodeValue

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem decode_words_code (ty : Itasca.types.ValueType) (lo hi : U64)
    (hfloat : ty = .F32 → lo.val < 2^32) :
    Code.decodeOne (Interp.sourceType ty) (Interp.pairWords ty (lo, hi)) =
      some (decodeWords ty lo hi, []) := by
  exact Interp.decode_words_code ty lo hi hfloat

/-- The concrete store decoder recovers the exact specification value from
words emitted by the actual extracted encoder, including all NaN payloads. -/
theorem decode_encoded_value {M : Type} (s : runtime.store.Store M)
    (value : runtime.Value) (hv : ValueInStore s value) (words : U64 × U64)
    (hencode : runtime.value.encode value = .ok words) :
    decodeWords (Interp.rawType value) words.1 words.2 = Interp.sourceValue value := by
  have hwords := Interp.encode_value_spec value s.id hv.1
  rw [hencode] at hwords
  simp only [WP.spec_ok] at hwords
  have hcanonical := encode_global_shape s value
    {mutability := .Const, valtype := Interp.rawType value} rfl hv
  rw [hencode] at hcanonical
  simp only [WP.spec_ok] at hcanonical
  have hfloat : Interp.rawType value = .F32 → words.1.val < 2^32 := by
    intro ht
    simp only [GlobalShape, ht] at hcanonical
    exact hcanonical.1
  have hround := Code.decode_encode (Interp.sourceValue value) (Interp.sourceValue_wf value) []
  simp only [List.append_nil, Interp.sourceValue_type] at hround
  rw [← hwords, decode_words_code _ _ _ hfloat] at hround
  exact congrArg Prod.fst (Option.some.inj hround)

end Itasca.Runtime.Store
