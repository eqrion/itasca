import Exec.Interp.Simd.Integer.SimdWidenLoop
import Exec.Interp.Simd.Common.SimdShiftBits
import Exec.Spec.SimdWiden
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std Exec.Spec.Simd

theorem signExtend_restrict {width : Nat} (bits : BitVec width) (output : Nat) (le : output ≤ 64) :
    (bits.signExtend 64).setWidth output = bits.signExtend output := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_signExtend]
  by_cases inside : i < output
  · simp [inside,show i < 64 by omega]
  · simp [inside]

@[step] theorem widen_input (width : U32) (signed : Bool) (a : U64) (bits : BitVec width.val)
    (positive : 0 < width.val) (bound : width.val ≤ 32)
    (input : a.val = bits.toNat) :
    (if signed then do
      let value ← runtime.interp.simd.signed a width
      Result.ok (IScalar.hcast .U64 value)
      else Result.ok a) ⦃ result => result.bv.setWidth (width.val*2) = extendBits signed (width.val*2) bits ⦄ := by
  have aBits : a.bv = bits.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth_of_le (by omega)]
    exact input
  cases signed
  · simp only [Bool.false_eq_true,↓reduceIte,WP.spec_ok,extendBits]
    exact (congrArg (BitVec.setWidth (width.val*2)) aBits).trans
      (BitVec.setWidth_setWidth_of_le _ (by omega))
  · simp only [Bool.true_eq,↓reduceIte]
    step with signed_bits a width positive (by omega) as ⟨value,valueEq⟩
    simp only [IScalar.hcast_bv_eq,UScalarTy.U64_numBits_eq,IScalarTy.I64_numBits_eq,BitVec.signExtend_eq]
    have narrow : a.bv.setWidth width.val = bits := by
      rw [aBits,BitVec.setWidth_setWidth_of_le _ (by omega),BitVec.setWidth_eq]
    have exactValue : value.bv = bits.signExtend 64 := by rw [valueEq,narrow]
    exact (congrArg (BitVec.setWidth (width.val*2)) exactValue).trans
      (signExtend_restrict bits _ (by omega))

@[step] theorem widen_word (width : U32) (multiply signed : Bool) (a b : U64)
    (x y : BitVec width.val) (positive : 0 < width.val) (bound : width.val ≤ 32)
    (aBits : a.val = x.toNat) (bBits : b.val = y.toNat) :
    widenWord width multiply signed a b ⦃ result =>
      result.bv.setWidth (width.val*2) = widenBits multiply signed x y ⦄ := by
  unfold widenWord
  step with widen_input width signed a x positive bound aBits as ⟨first,firstEq⟩
  step with widen_input width signed b y positive bound bBits as ⟨second,secondEq⟩
  cases multiply
  · exact WP.spec.ret firstEq
  · apply WP.spec.ret
    with_unfolding_all change (first.bv*second.bv).setWidth (width.val*2) = _
    rw [BitVec.setWidth_mul _ _ (by omega),firstEq,secondEq]
    rfl
end Exec.Interp.Simd
