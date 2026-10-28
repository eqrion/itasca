import Itasca.Runtime.Interp.Simd.Integer.SimdIntegerBinaryLoop
import Itasca.Runtime.Spec.SimdAverage
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

theorem average_word (width : U32) (a b : U64) (sa sb : I64)
    (widthBound : width.val ≤ 32)
    (aBound : a.val < 2^width.val) (bBound : b.val < 2^width.val) :
    integerBinaryWord 27#u32 width a b sa sb ⦃ result =>
      result.bv.setWidth width.val = averageBits (a.bv.setWidth width.val) (b.bv.setWidth width.val) ⦄ := by
  have power : 2^width.val ≤ 2^32 := Nat.pow_le_pow_right (by decide) widthBound
  have aValue : (a.bv.setWidth width.val).toNat = a.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt aBound
  have bValue : (b.bv.setWidth width.val).toNat = b.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt bBound
  unfold integerBinaryWord
  with_unfolding_all change (Aeneas.Std.bind _ _) ⦃ _ ⦄
  step as ⟨sum,sumEq⟩
  step as ⟨rounded,roundedEq⟩
  step as ⟨result,resultEq⟩
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth,average_bits_value,aValue,bValue]
  change result.val % 2^width.val = _
  rw [resultEq,roundedEq,sumEq]
  exact Nat.mod_eq_of_lt (by omega)

end Itasca.Runtime.Interp.Simd
