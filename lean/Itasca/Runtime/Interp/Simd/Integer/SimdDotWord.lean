import Itasca.Runtime.Interp.Simd.Integer.SimdQ15Word
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

@[step] theorem dot_mul (a b : I64)
    (aBound : -32768 ≤ a.val ∧ a.val < 32768)
    (bBound : -32768 ≤ b.val ∧ b.val < 32768) :
    a * b ⦃ result => result.val = a.val*b.val ∧
      -1073741824 ≤ result.val ∧ result.val ≤ 1073741824 ⦄ := by
  have p1 := mul_nonneg (by omega : 0 ≤ a.val+32768) (by omega : 0 ≤ b.val+32768)
  have p2 := mul_nonneg (by omega : 0 ≤ 32768-a.val) (by omega : 0 ≤ 32768-b.val)
  have p3 := mul_nonneg (by omega : 0 ≤ a.val+32768) (by omega : 0 ≤ 32768-b.val)
  have p4 := mul_nonneg (by omega : 0 ≤ 32768-a.val) (by omega : 0 ≤ b.val+32768)
  have productBound : -1073741824 ≤ a.val*b.val ∧ a.val*b.val ≤ 1073741824 := by constructor <;> nlinarith
  step* <;> scalar_tac

theorem dot_cast (x : I64) :
    (IScalar.hcast .U64 x).bv.setWidth 32 = BitVec.ofInt 32 x.val := by
  rw [IScalar.hcast_bv_eq]
  change (x.bv.signExtend 64).setWidth 32 = BitVec.ofInt 32 x.val
  rw [BitVec.signExtend_eq_setWidth_of_le _ (by decide : 64 ≤ 64)]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
  rw [← BitVec.signExtend_eq_setWidth_of_le _ (by decide : 32 ≤ 64)]
  rfl

end Itasca.Runtime.Interp.Simd
