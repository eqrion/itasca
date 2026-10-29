import Itasca.Runtime.Interp.Simd.Integer.CompareLanes
import Itasca.Runtime.Spec.Simd.CompareInteger

/-!
Sign extension of packed comparison masks.

Main declarations: `comparison_bits_sign_extend`. A direct consumer is `Interp.Simd.Float.Compare`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem comparison_bits_sign_extend (width : Nat) (bound : width ≤ 64) (answer : Bool) :
    comparisonBits width answer = (BitVec.ofNat 1 (nat_of_bool answer)).signExtend width := by
  cases answer
  · simp [comparisonBits,nat_of_bool,BitVec.signExtend]
  · apply BitVec.eq_of_getLsbD_eq
    intro i valid
    simp only [comparisonBits,nat_of_bool,ite_true]
    change ((BitVec.allOnes 64).setWidth width).getLsbD i = _
    rw [BitVec.getLsbD_setWidth,BitVec.getLsbD_allOnes]
    have small : i < 64 := by omega
    simp [valid,small,BitVec.getLsbD_signExtend]

end Itasca.Runtime.Interp.Simd
