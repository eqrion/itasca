import Itasca.Runtime.Interp.Simd.Integer.SimdPairwiseLoop
import Itasca.Runtime.Interp.Simd.Integer.SimdWidenWord
namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std Itasca.Runtime.Spec.Simd

@[step] theorem pairwise_word (width : U32) (signed : Bool) (a b : U64)
    (x y : BitVec width.val) (supported : width.val ∈ [8,16])
    (aBits : a.val = x.toNat) (bBits : b.val = y.toNat) :
    pairwiseWord width signed a b ⦃ result =>
      result.bv.setWidth (width.val*2) = pairwiseBits signed x y ⦄ := by
  have positive : 0 < width.val := by simp only [List.mem_cons,List.not_mem_nil,or_false] at supported;omega
  have bound : width.val ≤ 16 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at supported;omega
  have aNat : a.val < 65536 := by
    rw [aBits]
    exact lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) bound)
  have bNat : b.val < 65536 := by
    rw [bBits]
    exact lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by decide) bound)
  have aExact : a.bv = x.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq;rw [BitVec.toNat_setWidth_of_le (by omega)];exact aBits
  have bExact : b.bv = y.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq;rw [BitVec.toNat_setWidth_of_le (by omega)];exact bBits
  unfold pairwiseWord
  cases signed
  · simp only [Bool.false_eq_true,↓reduceIte]
    step as ⟨value,valueEq⟩
    have valueBits : value.bv = a.bv+b.bv := by
      apply BitVec.eq_of_toNat_eq
      change value.val = (a.val+b.val)%2^64
      rw [←valueEq]
      exact (Nat.mod_eq_of_lt (by scalar_tac)).symm
    refine (congrArg (BitVec.setWidth (width.val*2)) valueBits).trans ?_
    rw [BitVec.setWidth_add _ _ (by omega),aExact,bExact,
      BitVec.setWidth_setWidth_of_le _ (by omega),BitVec.setWidth_setWidth_of_le _ (by omega)]
    rfl
  · simp only [↓reduceIte]
    step with signed_bits a width positive (by omega) as ⟨sa,saBits⟩
    step with signed_bits b width positive (by omega) as ⟨sb,sbBits⟩
    have saExact : sa.bv = x.signExtend 64 := by
      rw [saBits,aExact,BitVec.setWidth_setWidth_of_le _ (by omega),BitVec.setWidth_eq]
    have sbExact : sb.bv = y.signExtend 64 := by
      rw [sbBits,bExact,BitVec.setWidth_setWidth_of_le _ (by omega),BitVec.setWidth_eq]
    have signedBounds (bits : BitVec width.val) : -32768 ≤ bits.toInt ∧ bits.toInt < 32768 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at supported
      rcases supported with h | h
      all_goals have lo := BitVec.le_toInt bits
      all_goals have hi := BitVec.toInt_lt (x:=bits)
      all_goals simp only [h] at lo hi
      all_goals omega
    have saBound : -32768 ≤ sa.val ∧ sa.val < 32768 := by
      change -32768 ≤ sa.bv.toInt ∧ sa.bv.toInt < 32768
      rw [saExact,BitVec.toInt_signExtend_of_le (by omega)]
      exact signedBounds x
    have sbBound : -32768 ≤ sb.val ∧ sb.val < 32768 := by
      change -32768 ≤ sb.bv.toInt ∧ sb.bv.toInt < 32768
      rw [sbExact,BitVec.toInt_signExtend_of_le (by omega)]
      exact signedBounds y
    step as ⟨value,valueEq⟩
    have valueBits : value.bv = sa.bv+sb.bv := by
      rw [←BitVec.ofInt_toInt (x:=value.bv)]
      change BitVec.ofInt 64 value.val = _
      rw [valueEq,BitVec.ofInt_add]
      simp
    simp only [IScalar.hcast_bv_eq,UScalarTy.U64_numBits_eq,IScalarTy.I64_numBits_eq,BitVec.signExtend_eq]
    refine (congrArg (BitVec.setWidth (width.val*2)) valueBits).trans ?_
    rw [BitVec.setWidth_add _ _ (by omega),saExact,sbExact,
      signExtend_restrict _ _ (by omega),signExtend_restrict _ _ (by omega)]
    rfl
end Itasca.Runtime.Interp.Simd
