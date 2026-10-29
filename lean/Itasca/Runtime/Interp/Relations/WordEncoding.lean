import Itasca.Runtime.Interp.Relations.DecodeValue
import Itasca.Runtime.Interp.Relations.Regions

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

/-- Canonical raw global words re-encode exactly, including reference zero and
both vector words. Only 32-bit numerical payloads need their canonical bound. -/
theorem encode_decode_words (ty : Itasca.types.ValueType) (lo hi : U64)
    (small : ty = .I32 ∨ ty = .F32 → lo.val < 2^32) :
    Compiler.encodeValue (Store.decodeWords ty lo hi) = pairWords ty (lo,hi) := by
  cases ty
  · change [lo.val % 2^32] = [lo.val]
    rw [Nat.mod_eq_of_lt (small (Or.inl rfl))]
  · rfl
  · change [Builtins.floatBits 32 (Builtins.floatOfBits 32 (lo.val % 2^32))] = [lo.val]
    have bound := small (Or.inr rfl)
    rw [Nat.mod_eq_of_lt bound,Builtins.Float.float_bits_roundtrip_32 lo.val bound]
  · change [Builtins.floatBits 64 (Builtins.floatOfBits 64 lo.val)] = [lo.val]
    rw [Builtins.Float.float_bits_roundtrip_64 lo.val (by scalar_tac)]
  · change [(lo.val+hi.val*2^64)%2^64,(lo.val+hi.val*2^64)/2^64] = [lo.val,hi.val]
    have bound : lo.val < 2^64 := by scalar_tac
    simp [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt bound,Nat.add_mul_div_right,Nat.div_eq_of_lt bound]
    exact bound
  · by_cases zero : lo.val = 0
    · simp [Store.decodeWords,Store.decodeRef,zero,Store.refVal,Store.decodeElemType,Compiler.encodeValue,pairWords,sourceType]
    · have restore : lo.val - 1 + 1 = lo.val := by omega
      simp [Store.decodeWords,Store.decodeRef,zero,Store.refVal,Compiler.encodeValue,pairWords,sourceType,restore]
  · by_cases zero : lo.val = 0
    · simp [Store.decodeWords,Store.decodeRef,zero,Store.refVal,Store.decodeElemType,Compiler.encodeValue,pairWords,sourceType]
    · have restore : lo.val - 1 + 1 = lo.val := by omega
      simp [Store.decodeWords,Store.decodeRef,zero,Store.refVal,Compiler.encodeValue,pairWords,sourceType,restore]

theorem ValuesAt.append_scalar {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (ty : Itasca.types.ValueType) (lo hi : U64)
    (scalar : ty ≠ .V128) (small : ty = .I32 ∨ ty = .F32 → lo.val < 2^32)
    (capacity : base + Compiler.slots (front.map Compiler.valueType) < words.length) :
    ValuesAt (words.set (base + Compiler.slots (front.map Compiler.valueType)) lo) base
      (front ++ [Store.decodeWords ty lo hi]) := by
  have same : pairWords ty (lo,hi) = [lo.val] := by cases ty <;> simp_all [pairWords,sourceType]
  have written := WordsAt.set_append represented lo (by simpa only [Compiler.encode_values_length] using capacity)
  change WordsAt _ _ (Compiler.encodeValues (front ++ [Store.decodeWords ty lo hi]))
  rw [Compiler.encode_values_append]
  rw [show Compiler.encodeValues [Store.decodeWords ty lo hi] = Compiler.encodeValue (Store.decodeWords ty lo hi) by simp [Compiler.encodeValues]]
  rw [encode_decode_words ty lo hi small,same]
  simpa only [Compiler.encode_values_length] using written

theorem ValuesAt.append_vector {words : List U64} {base : Nat} {front : List val}
    (represented : ValuesAt words base front) (lo hi : U64)
    (capacity : base + Compiler.slots (front.map Compiler.valueType) + 2 ≤ words.length) :
    ValuesAt ((words.set (base + Compiler.slots (front.map Compiler.valueType)) lo).set
      (base + Compiler.slots (front.map Compiler.valueType)+1) hi) base
      (front ++ [Store.decodeWords .V128 lo hi]) := by
  have first := WordsAt.set_append represented lo (by rw [Compiler.encode_values_length]; omega)
  have second := first.set_append hi (by simp only [List.length_append,List.length_cons,List.length_nil,
    List.length_set,Compiler.encode_values_length]; omega)
  change WordsAt _ _ (Compiler.encodeValues (front ++ [Store.decodeWords .V128 lo hi]))
  rw [Compiler.encode_values_append]
  rw [show Compiler.encodeValues [Store.decodeWords .V128 lo hi] = Compiler.encodeValue (Store.decodeWords .V128 lo hi) by simp [Compiler.encodeValues]]
  rw [encode_decode_words .V128 lo hi (by simp)]
  change WordsAt _ _ (Compiler.encodeValues front ++ [lo.val,hi.val])
  simpa only [Compiler.encode_values_length,List.length_append,List.length_cons,List.length_nil,
    List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.zero_add] using second

end Itasca.Runtime.Interp
