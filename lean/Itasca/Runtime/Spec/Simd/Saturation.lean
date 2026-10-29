import Itasca.Runtime.Spec.Simd.CompareInteger
import Itasca.Runtime.Spec.IntegerSigned

/-!
The source lane-clamping operation.

Main declarations: `clampLane`. A direct consumer is `Spec.Simd.IntegerSaturating`.
-/

namespace Itasca.Runtime.Spec.Simd

def clampLane (width : Nat) (signed : Bool) (x : Int) : Int :=
  let lo := if signed then -(2^(width-1):Int) else 0
  let hi := if signed then (2^(width-1):Int)-1 else (2^width:Int)-1
  if x < lo then lo else if x > hi then hi else x

theorem clamp_signed (width : Nat) (x : Int) : clampLane width true x = sat_s_ width x := by
  have exponent : ((width:Int)-1).toNat = width-1 := by omega
  simp only [clampLane,Bool.true_eq,↓reduceIte,sat_s_,exponent]

theorem clamp_signed_to_int (width : Nat) (x : Int) (positive : 0 < width) :
    (BitVec.ofInt width (clampLane width true x)).toInt = sat_s_ width x := by
  have exponent : ((width:Int)-1).toNat = width-1 := by omega
  have power : 0 < (2^(width-1):Int) := pow_pos (by decide) _
  rw [clamp_signed]
  apply BitVec.toInt_ofInt_eq_self positive
  all_goals simp only [sat_s_,exponent]
  all_goals split <;> (try split) <;> omega

theorem clamp_unsigned_to_nat (width : Nat) (x : Int) :
    (BitVec.ofInt width (clampLane width false x)).toNat = sat_u_ width x := by
  have power : 0 < (2^width:Int) := pow_pos (by decide) _
  simp only [clampLane,Bool.false_eq_true,↓reduceIte,sat_u_]
  split
  · simp
  · split
    · rw [BitVec.toNat_ofInt,Int.emod_eq_of_lt] <;> (try simp only [Nat.cast_pow,Nat.cast_ofNat]) <;> omega
    · rw [BitVec.toNat_ofInt,Int.emod_eq_of_lt] <;> (try simp only [Nat.cast_pow,Nat.cast_ofNat]) <;> omega

end Itasca.Runtime.Spec.Simd
