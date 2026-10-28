import Exec.Interp.Simd.Common.SimdUnary
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem unary_sign_lane (width : Nat) (bits : BitVec width) (positive : 0 < width) (bound : width ≤ 64) :
    ((bits.setWidth 64 >>> (width-1)).setWidth 32) = (BitVec.ofBool bits.msb).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i valid
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight]
  by_cases zero : i=0
  · subst i
    simp [BitVec.msb,BitVec.getMsbD_eq_getLsbD,positive,show width-1<64 by omega]
  · have past : width ≤ i+(width-1) := by omega
    simp [BitVec.getLsbD_ofBool,zero,BitVec.getLsbD_of_ge bits (width-1+i) (by omega)]

theorem unary_signs_get (width : Nat) (x : BitVec 128) (count : Nat)
    (positive : 0 < width) (bound : width ≤ 64) (countBound : count ≤ 32) :
    ∀ i, i < 32 → (unarySigns width x count).getLsbD i =
      if i < count then (laneBits width i x).msb else false := by
  induction count with
  | zero => simp [unarySigns]
  | succ count ih =>
    intro i valid
    rw [unarySigns,BitVec.getLsbD_or,ih (by omega) i valid,unary_sign_lane width _ positive bound]
    simp only [BitVec.getLsbD_shiftLeft,BitVec.getLsbD_setWidth,BitVec.getLsbD_ofBool]
    by_cases before : i<count
    · simp [before,show i<count+1 from by omega]
    · by_cases same : i=count
      · subst i
        simp [valid]
      · have after : ¬ (i < count+1) := by omega
        have difference : i-count≠0 := by omega
        simp [before,after,difference]
end Itasca.Runtime.Interp.Simd
