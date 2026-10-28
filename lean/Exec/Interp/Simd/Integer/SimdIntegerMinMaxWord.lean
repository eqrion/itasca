import Exec.Interp.Simd.Integer.SimdIntegerBinaryLoop
import Exec.Spec.SimdIntegerMinMax
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def integerMinMaxIndex (kind : IntegerMinMax) : U32 :=
  match kind with | .minS => 22#u32 | .minU => 23#u32 | .maxS => 24#u32 | .maxU => 25#u32

theorem integer_minmax_word (kind : IntegerMinMax) (width : U32)
    (a b : U64) (sa sb : I64)
    (aBound : a.val < 2^width.val) (bBound : b.val < 2^width.val)
    (saEq : sa.val = (a.bv.setWidth width.val).toInt)
    (sbEq : sb.val = (b.bv.setWidth width.val).toInt) :
    integerBinaryWord (integerMinMaxIndex kind) width a b sa sb ⦃ result =>
      result.bv.setWidth width.val = integerMinMaxBits kind (a.bv.setWidth width.val) (b.bv.setWidth width.val) ⦄ := by
  have aValue : (a.bv.setWidth width.val).toNat = a.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt aBound
  have bValue : (b.bv.setWidth width.val).toNat = b.val := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt bBound
  cases kind
  all_goals unfold integerBinaryWord integerMinMaxIndex
  all_goals with_unfolding_all change (if _ then Result.ok a else Result.ok b) ⦃ _ ⦄
  all_goals simp only [IScalar.lt_equiv,UScalar.lt_equiv,saEq,sbEq,integerMinMaxBits,aValue,bValue]
  all_goals split <;> simp_all only [WP.spec_ok]

end Itasca.Runtime.Interp.Simd
