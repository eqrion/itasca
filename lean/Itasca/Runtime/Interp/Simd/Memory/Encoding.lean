import Itasca.Runtime.Interp.Simd.Memory.Bytes
import SpecExt.Builtins.EncodingLemmas

/-!
Byte decoding and source values of vector loads.

Main declarations: `vector_load_byte_value` and `vector_load_bytes_source`. A direct consumer is `Interp.Simd.Memory.LoadSource`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

private theorem power_byte (index : Nat) : 2^(index * 8) = 256^index := by
  rw [Nat.mul_comm, Nat.pow_mul]

theorem vector_load_byte_value (value : U128) (byte : U8) (index : Nat)
    (small : index < 16) (lowerBound : value.val < 256^index) :
    (vectorLoadByte value byte index).val = value.val + byte.val * 256^index := by
  have byteBound : byte.val < 256 := by scalar_tac
  have shiftedBound : byte.val * 256^index < 2^128 := by
    interval_cases index <;> norm_num at * <;> omega
  change (value.bv ||| ((UScalar.cast .U128 byte).bv <<< (index * 8))).toNat = _
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, UScalar.bv_toNat, U8.cast_U128_val_eq]
  rw [Nat.shiftLeft_eq, power_byte, Nat.mod_eq_of_lt shiftedBound]
  have separated := Nat.two_pow_add_eq_or_of_lt (i := index * 8) (by simpa only [power_byte] using lowerBound) byte.val
  simpa only [power_byte, Nat.mul_comm, Nat.add_comm, Nat.or_comm] using separated.symm
/-- The byte loop is the specification's little-endian natural-number decoder,
with an explicit already-filled low prefix. -/
theorem vector_load_bytes_value (bytes : List U8) (start : Nat) (value : U128) (index count : Nat)
    (small : index + count ≤ 16) (inside : start + index + count ≤ bytes.length)
    (lowerBound : value.val < 256^index) :
    (vectorLoadBytes bytes start value index count).val = value.val + 256^index *
      SpecExt.Builtins.integerOfBytes (Store.decodeBytes ((bytes.drop (start + index)).take count)) := by
  induction count generalizing value index with
  | zero => simp [vectorLoadBytes, Store.decodeBytes, SpecExt.Builtins.integerOfBytes]
  | succ count ih =>
    have atIndex : start + index < bytes.length := by omega
    have byteBound : bytes[start + index]!.val < 256 := by scalar_tac
    have nextValue := vector_load_byte_value value bytes[start + index]! index (by omega) lowerBound
    have nextBound : (vectorLoadByte value bytes[start + index]! index).val < 256^(index+1) := by
      rw [nextValue,Nat.pow_succ]
      have positive : 0 < 256^index := by positivity
      nlinarith
    rw [vectorLoadBytes, ih _ (index+1) (by omega) (by omega) nextBound, nextValue]
    rw [List.drop_eq_getElem_cons atIndex]
    simp only [List.take_succ_cons, Store.decodeBytes, List.map_cons, SpecExt.Builtins.integerOfBytes]
    rw [getElem!_pos bytes _ atIndex, Nat.pow_succ]
    have positions : start + (index+1) = start + index + 1 := by omega
    rw [positions]
    ring

theorem vector_load_bytes_source (bytes : List U8) (start count : Nat)
    (small : count ≤ 16) (inside : start + count ≤ bytes.length) :
    (vectorLoadBytes bytes start 0#u128 0 count).val =
      SpecExt.Builtins.integerOfBytes (Store.decodeBytes ((bytes.drop start).take count)) := by
  simpa using vector_load_bytes_value bytes start 0#u128 0 count (by simpa using small)
    (by simpa using inside) (by simp)
end Itasca.Runtime.Interp.Simd
