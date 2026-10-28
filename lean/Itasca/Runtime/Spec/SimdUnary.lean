import Itasca.Runtime.Spec.SimdShape
import Itasca.Runtime.Spec.IntegerSigned
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem negate_lane_relation (width : Nat) (bits : BitVec width) :
    fun_ineg_ width (.mk_uN bits.toNat) (.mk_uN (-bits).toNat) := by
  have bitsEq : BitVec.ofInt width ((2^width : Int)-bits.toNat) = -bits := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt,BitVec.toNat_neg]
    have bound := bits.isLt
    have power : (2^width : Int) = ((2^width : Nat) : Int) := by norm_cast
    rw [power,←Int.natCast_sub (by omega : bits.toNat ≤ 2^width),←Int.natCast_emod,Int.toNat_natCast]
  have valueEq := congrArg BitVec.toNat bitsEq
  simp only [BitVec.toNat_ofInt] at valueEq
  rw [←valueEq]
  exact .fun_ineg__case_0 _ _ (unsigned_wf_of_lt width _ (by simp only [proj_uN_0]; convert (-bits).isLt using 1; exact valueEq))

theorem absolute_lane_relation (width : Nat) (bits : BitVec width) (positive : 0 < width) :
    fun_iabs_ width (.mk_uN bits.toNat)
      (.mk_uN (if bits.toInt < 0 then (-bits).toNat else bits.toNat)) := by
  have signed := bitvec_signed width bits
  have relation := fun_iabs_.fun_iabs__case_0 width (.mk_uN bits.toNat) (.mk_uN (-bits).toNat)
    bits.toInt (negate_lane_relation width bits) signed
  split
  · rename_i negative
    simpa [show ¬bits.toInt ≥ 0 by omega] using relation
  · rename_i nonnegative
    simpa [show bits.toInt ≥ 0 by omega] using relation
end Itasca.Runtime.Spec.Simd
