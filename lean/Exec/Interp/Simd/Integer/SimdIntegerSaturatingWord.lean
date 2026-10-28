import Exec.Interp.Simd.Integer.SimdSaturation
import Exec.Spec.SimdIntegerSaturating
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def integerSaturatingIndex (kind : IntegerSaturating) : U32 :=
  match kind with | .addS => 15#u32 | .addU => 16#u32 | .subS => 18#u32 | .subU => 19#u32

theorem integer_saturating_word (kind : IntegerSaturating) (width : U32)
    (a b : U64) (sa sb : I64) (supported : width.val ∈ [8,16,32])
    (aBound : a.val < 2^width.val) (bBound : b.val < 2^width.val)
    (saEq : sa.val = (a.bv.setWidth width.val).toInt)
    (sbEq : sb.val = (b.bv.setWidth width.val).toInt) :
    integerBinaryWord (integerSaturatingIndex kind) width a b sa sb ⦃ result =>
      result.bv.setWidth width.val = integerSaturatingBits kind (a.bv.setWidth width.val) (b.bv.setWidth width.val) ⦄ := by
  have aValue : (a.bv.setWidth width.val).toNat = a.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt aBound
  have bValue : (b.bv.setWidth width.val).toNat = b.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt bBound
  have aCast : (a.val:Int).bmod (2^128) = a.val := Int.bmod_eq_of_le (by scalar_tac) (by scalar_tac)
  have bCast : (b.val:Int).bmod (2^128) = b.val := Int.bmod_eq_of_le (by scalar_tac) (by scalar_tac)
  cases kind
  all_goals unfold integerBinaryWord integerSaturatingIndex
  all_goals with_unfolding_all change (Aeneas.Std.bind _ _) ⦃ _ ⦄
  all_goals step* <;> simp_all [integerSaturatingBits,aCast,bCast,I128.min,I128.max] <;> scalar_tac

end Itasca.Runtime.Interp.Simd
