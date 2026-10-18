import Exec.Interp.Simd.Common.SimdUnaryWord
import Exec.Interp.Simd.Common.SimdPopulation
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std

theorem signExtend_low (width : Nat) (bits : BitVec width) (bound : width ≤ 64) :
    (bits.signExtend 64).setWidth width = bits := by
  apply BitVec.eq_of_getLsbD_eq
  intro i valid
  have fits : i < 64 := by omega
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_signExtend]
  simp only [valid,fits,ite_true,decide_true,Bool.true_and]

theorem unaryLane_neg (width : Nat) (bits : BitVec width) (bound : width ≤ 64) :
    unaryLane 1#u32 width bits = -bits := by
  have same := (congrArg (BitVec.setWidth width) (BitVec.zero_sub (bits.setWidth 64))).trans
    ((BitVec.setWidth_neg_of_le bound).trans
      (congrArg Neg.neg ((BitVec.setWidth_setWidth_of_le bits bound).trans (BitVec.setWidth_eq bits))))
  with_unfolding_all exact same

theorem unaryLane_abs (width : Nat) (bits : BitVec width) (bound : width ≤ 64) :
    unaryLane 0#u32 width bits = if bits.toInt < 0 then -bits else bits := by
  have sign : ((⟨bits.signExtend 64⟩ : I64) < 0#i64) ↔ bits.toInt < 0 := by
    change (bits.signExtend 64).toInt < 0 ↔ _
    rw [BitVec.toInt_signExtend_of_le bound]
  with_unfolding_all change
    ((if (⟨bits.signExtend 64⟩ : I64) < 0#i64
      then core.num.U64.wrapping_sub 0#u64 (IScalar.hcast .U64 (⟨bits.signExtend 64⟩ : I64))
      else IScalar.hcast .U64 (⟨bits.signExtend 64⟩ : I64)).bv).setWidth width = _
  simp only [sign]
  by_cases negative : bits.toInt < 0
  · rw [if_pos negative,if_pos negative]
    simp only [core.num.U64.wrapping_sub,UScalar.wrapping_sub,IScalar.hcast_bv_eq,
      UScalarTy.U64_numBits_eq,IScalarTy.I64_numBits_eq,BitVec.signExtend_eq]
    with_unfolding_all change (0 - bits.signExtend 64).setWidth width = -bits
    exact (congrArg (BitVec.setWidth width) (BitVec.zero_sub (bits.signExtend 64))).trans
      ((BitVec.setWidth_neg_of_le bound).trans (congrArg Neg.neg (signExtend_low width bits bound)))
  · rw [if_neg negative,if_neg negative]
    simp only [IScalar.hcast_bv_eq,UScalarTy.U64_numBits_eq,IScalarTy.I64_numBits_eq,
      BitVec.signExtend_eq]
    exact signExtend_low width bits bound
theorem unaryLane_population (bits : BitVec 8) :
    unaryLane 2#u32 8 bits = BitVec.ofNat 8 (SpecExt.Builtins.population (SpecExt.Builtins.integerBits 8 bits.toNat)) := by
  have widened : (bits.setWidth 64).toNat = bits.toNat := by
    rw [BitVec.toNat_setWidth,Nat.mod_eq_of_lt (lt_trans bits.isLt (by decide : 2^8 < 2^64))]
  have same := countBits_width 8 bits.toNat (by decide) bits.isLt
  rw [Exec.Interp.countBits_population 8] at same
  with_unfolding_all change
    ((BitVec.ofNat 32 (Primitive.countBits 64 (bits.setWidth 64).toNat)).setWidth 64).setWidth 8 = _
  rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
    BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 32),widened,same]

end Exec.Interp.Simd
