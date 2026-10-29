import Itasca.Runtime.Interp.Simd.Integer.Signed
import Itasca.Runtime.Interp.Simd.Lanes.Packing

/-!
Bit-width and signed-value facts for lane shifts.

Main declarations: `shift_right_widen` and `signed_bits`. A direct consumer is `Interp.Simd.Integer.Shift`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem shift_right_widen (width : Nat) (bits : BitVec width) (shift : Nat) (bound : width ≤ 64) :
    ((bits.setWidth 64) >>> shift).setWidth width = bits >>> shift := by
  rw [←BitVec.setWidth_ushiftRight bound,BitVec.setWidth_setWidth_of_le _ bound,BitVec.setWidth_eq]

theorem shift_right_signed_widen (width : Nat) (bits : BitVec width) (shift : Nat)
    (positive : 0 < width) (bound : width ≤ 64) :
    ((bits.signExtend 64).sshiftRight shift).setWidth width = bits.sshiftRight shift := by
  by_cases full : width=64
  · subst width
    simp
  have lastFalse : ¬63 < width := by omega
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_setWidth,BitVec.getLsbD_sshiftRight,BitVec.getLsbD_signExtend,
    BitVec.msb_eq_getLsbD_last]
  by_cases inside : i < width
  · have valid : i < 64 := by omega
    by_cases shifted : shift+i < width
    · have fits : shift+i < 64 := by omega
      simp [inside,Nat.not_le.mpr inside,Nat.not_le.mpr valid,shifted,fits,lastFalse]
    · by_cases fits : shift+i < 64
      · simp [inside,Nat.not_le.mpr inside,Nat.not_le.mpr valid,shifted,fits,lastFalse]
      · simp [inside,Nat.not_le.mpr inside,Nat.not_le.mpr valid,shifted,fits,lastFalse]
  · simp [inside]

@[step] theorem lane_bits (v : U128) (width index : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64)
    (positionBound : width.val*index.val < 128) :
    runtime.interp.simd.lane v width index ⦃ result =>
      result.bv = (laneBits width.val index.val v.bv).setWidth 64 ⦄ := by
  apply WP.spec_mono (lane v width index positive widthBound positionBound)
  intro result value
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth,lane_bits_to_nat]
  change result.val = _
  rw [value]
  exact (Nat.mod_eq_of_lt (by
    apply lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
    exact Nat.pow_le_pow_right (by decide) widthBound)).symm

@[step] theorem signed_bits (v : U64) (width : U32)
    (positive : 0 < width.val) (widthBound : width.val ≤ 64) :
    runtime.interp.simd.signed v width ⦃ result =>
      result.bv = (v.bv.setWidth width.val).signExtend 64 ⦄ := by
  apply WP.spec_mono (signed v width positive widthBound)
  intro result value
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le widthBound]
  exact value
end Itasca.Runtime.Interp.Simd
