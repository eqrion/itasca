import Itasca.Runtime.Interp.Simd.Integer.SimdIntegerBinaryLoop
import Itasca.Runtime.Spec.SimdIntegerArithmetic
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

def integerArithmeticIndex (kind : IntegerArithmetic) : U32 :=
  match kind with | .add => 14#u32 | .sub => 17#u32 | .mul => 21#u32

theorem integer_arithmetic_word (kind : IntegerArithmetic) (width : U32)
    (a b : U64) (sa sb : I64) (widthBound : width.val ≤ 64) :
    integerBinaryWord (integerArithmeticIndex kind) width a b sa sb ⦃ result =>
      result.bv.setWidth width.val = integerArithmeticBits kind (a.bv.setWidth width.val) (b.bv.setWidth width.val) ⦄ := by
  cases kind
  all_goals unfold integerBinaryWord integerArithmeticIndex
  all_goals with_unfolding_all change (Result.ok _) ⦃ _ ⦄
  all_goals rw [WP.spec_ok]
  · with_unfolding_all change (a.bv+b.bv).setWidth width.val = _
    exact BitVec.setWidth_add _ _ widthBound
  · with_unfolding_all change (a.bv-b.bv).setWidth width.val = _
    rw [BitVec.sub_eq_add_neg,BitVec.setWidth_add _ _ widthBound,BitVec.setWidth_neg_of_le widthBound]
    exact (BitVec.sub_eq_add_neg _ _).symm
  · with_unfolding_all change (a.bv*b.bv).setWidth width.val = _
    exact BitVec.setWidth_mul _ _ widthBound

end Itasca.Runtime.Interp.Simd
