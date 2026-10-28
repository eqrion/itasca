import Itasca.Runtime.Spec.SimdSaturation
import Itasca.Runtime.Spec.IntegerShift
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem clamp_signed_minmax (width : Nat) (x : Int) :
    clampLane width true x = max (-(2^(width-1):Int)) (min x ((2^(width-1):Int)-1)) := by
  have power : 0 < (2^(width-1):Int) := pow_pos (by decide) _
  simp only [clampLane,Bool.true_eq,↓reduceIte,max_def,min_def]
  split_ifs <;> omega

theorem signed_saturate_bits (width : Nat) (x : Int) :
    uN.mk_uN (BitVec.ofInt width (clampLane width true x)).toNat = saturate width .S x := by
  simp only [saturate,encodeSigned,BitVec.toNat_ofInt,Nat.cast_pow,Nat.cast_ofNat,clamp_signed_minmax]

def q15Bits (a b : BitVec 16) : BitVec 16 :=
  BitVec.ofInt 16 (clampLane 16 true ((a.toInt*b.toInt+16384)/32768))

theorem q15_bits_source (a b : BitVec 16) :
    uN.mk_uN (q15Bits a b).toNat = iq15mulr_sat_ 16 .S (.mk_uN a.toNat) (.mk_uN b.toNat) := by
  simp only [q15Bits,iq15mulr_sat_,proj_uN_0,Itasca.Runtime.Spec.signedValue_bitvec]
  exact signed_saturate_bits _ _

end Itasca.Runtime.Spec.Simd
