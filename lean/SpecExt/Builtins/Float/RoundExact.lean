import SpecExt.Builtins.Float.Classify
import SpecExt.Builtins.Float.RoundingLemmas
namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem floorEncoding_exact (width : Nat) (square : Bool) (q : Rat)
    (fuel lo hi target : Nat) (lower : lo ≤ target) (upper : target ≤ hi)
    (size : hi - lo < 2 ^ fuel)
    (test : ∀ k, lo ≤ k → k ≤ hi →
      ((if square then roundingValue width k * roundingValue width k else roundingValue width k) ≤ q ↔ k ≤ target)) :
    floorEncoding width square q fuel lo hi = target := by
  induction fuel generalizing lo hi with
  | zero =>
    simp only [floorEncoding]
    simp only [pow_zero] at size
    omega
  | succ fuel ih =>
    have power : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by omega
    rw [power] at size
    have lowMid : lo ≤ (lo + hi + 1) / 2 := by omega
    have midHigh : (lo + hi + 1) / 2 ≤ hi := by omega
    simp only [floorEncoding, test _ lowMid midHigh]
    split_ifs with mid
    · apply ih _ hi mid upper (by omega)
      intro k hk kh
      exact test k (by omega) kh
    · apply ih lo _ lower (by omega) (by omega)
      intro k hk kh
      exact test k hk (by omega)

theorem roundingValue_finite32 (bits : Nat) (finite : bits < 2139095040) :
    roundingValue 32 bits = finiteValue 32 (floatOfBits 32 bits) := by
  unfold roundingValue
  rw [if_neg (show bits ≠ infinityBits 32 by change bits ≠ 2139095040; omega)]
  unfold finiteValue
  rw [negative_floatOfBits_32 bits (by omega)]
  simp [show ¬2147483648 ≤ bits by omega]

theorem roundMagnitude_exact32 (bits : Nat) (finite : bits + 1 < 2139095040) :
    roundMagnitude 32 false (finiteValue 32 (floatOfBits 32 bits)) = magnitude (floatOfBits 32 bits) := by
  have floor : floorEncoding 32 false (finiteValue 32 (floatOfBits 32 bits)) 32 0
      (infinityBits 32 - 1) = bits := by
    apply floorEncoding_exact
    · omega
    · change bits ≤ 2139095040 - 1; omega
    · decide
    · intro k lower upper
      have kfinite : k < 2139095040 := by change k ≤ 2139095040 - 1 at upper; omega
      simp only [Bool.false_eq_true, ↓reduceIte, roundingValue_finite32 k kfinite]
      have lt := positive_finite_lt_32 bits k (by omega) kfinite
      simpa only [not_lt] using not_congr lt
  unfold roundMagnitude
  rw [floor]
  dsimp only
  rw [roundingValue_finite32 bits (by omega), roundingValue_finite32 (bits+1) finite]
  have rise := (positive_finite_lt_32 bits (bits+1) (by omega) finite).mpr (by omega)
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [if_pos (by linarith)]

theorem round_exact_positive32 (bits : Nat) (positive : 0 < bits) (finite : bits + 1 < 2139095040) :
    round 32 (finiteValue 32 (floatOfBits 32 bits)) = floatOfBits 32 bits := by
  have zero : finiteValue 32 (floatOfBits 32 0) = 0 := by decide +kernel
  have pos : 0 < finiteValue 32 (floatOfBits 32 bits) := by
    have h := (positive_finite_lt_32 0 bits (by omega) (by omega)).mpr positive
    simpa only [zero] using h
  unfold round
  rw [if_neg (ne_of_gt pos), if_neg (not_lt.mpr (le_of_lt pos)), roundMagnitude_exact32 bits finite]
  rw [← floatOfBits_abs32, Nat.mod_eq_of_lt (show bits < 2147483648 by omega)]

theorem roundingValue_finite64 (bits : Nat) (finite : bits < 9218868437227405312) :
    roundingValue 64 bits = finiteValue 64 (floatOfBits 64 bits) := by
  unfold roundingValue
  rw [if_neg (show bits ≠ infinityBits 64 by change bits ≠ 9218868437227405312; omega)]
  unfold finiteValue
  rw [negative_floatOfBits_64 bits (by omega)]
  simp [show ¬9223372036854775808 ≤ bits by omega]

theorem roundMagnitude_exact64 (bits : Nat) (finite : bits + 1 < 9218868437227405312) :
    roundMagnitude 64 false (finiteValue 64 (floatOfBits 64 bits)) = magnitude (floatOfBits 64 bits) := by
  have floor : floorEncoding 64 false (finiteValue 64 (floatOfBits 64 bits)) 64 0
      (infinityBits 64 - 1) = bits := by
    apply floorEncoding_exact
    · omega
    · change bits ≤ 9218868437227405312 - 1; omega
    · decide
    · intro k lower upper
      have kfinite : k < 9218868437227405312 := by change k ≤ 9218868437227405312 - 1 at upper; omega
      simp only [Bool.false_eq_true, ↓reduceIte, roundingValue_finite64 k kfinite]
      have lt := positive_finite_lt_64 bits k (by omega) kfinite
      simpa only [not_lt] using not_congr lt
  unfold roundMagnitude
  rw [floor]
  dsimp only
  rw [roundingValue_finite64 bits (by omega), roundingValue_finite64 (bits+1) finite]
  have rise := (positive_finite_lt_64 bits (bits+1) (by omega) finite).mpr (by omega)
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [if_pos (by linarith)]

theorem round_exact_positive64 (bits : Nat) (positive : 0 < bits) (finite : bits + 1 < 9218868437227405312) :
    round 64 (finiteValue 64 (floatOfBits 64 bits)) = floatOfBits 64 bits := by
  have zero : finiteValue 64 (floatOfBits 64 0) = 0 := by decide +kernel
  have pos : 0 < finiteValue 64 (floatOfBits 64 bits) := by
    have h := (positive_finite_lt_64 0 bits (by omega) (by omega)).mpr positive
    simpa only [zero] using h
  unfold round
  rw [if_neg (ne_of_gt pos), if_neg (not_lt.mpr (le_of_lt pos)), roundMagnitude_exact64 bits finite]
  rw [← floatOfBits_abs64, Nat.mod_eq_of_lt (show bits < 9223372036854775808 by omega)]

theorem round_exact_negative32 (bits : Nat) (positive : 0 < bits) (finite : bits + 1 < 2139095040) :
    round 32 (-finiteValue 32 (floatOfBits 32 bits)) = .NEG (magnitude (floatOfBits 32 bits)) := by
  have zero : finiteValue 32 (floatOfBits 32 0) = 0 := by decide +kernel
  have pos : 0 < finiteValue 32 (floatOfBits 32 bits) := by
    have h := (positive_finite_lt_32 0 bits (by omega) (by omega)).mpr positive
    simpa only [zero] using h
  unfold round
  rw [if_neg (ne_of_lt (neg_lt_zero.mpr pos)), if_pos (neg_lt_zero.mpr pos), neg_neg,
    roundMagnitude_exact32 bits finite]

theorem round_exact_negative64 (bits : Nat) (positive : 0 < bits) (finite : bits + 1 < 9218868437227405312) :
    round 64 (-finiteValue 64 (floatOfBits 64 bits)) = .NEG (magnitude (floatOfBits 64 bits)) := by
  have zero : finiteValue 64 (floatOfBits 64 0) = 0 := by decide +kernel
  have pos : 0 < finiteValue 64 (floatOfBits 64 bits) := by
    have h := (positive_finite_lt_64 0 bits (by omega) (by omega)).mpr positive
    simpa only [zero] using h
  unfold round
  rw [if_neg (ne_of_lt (neg_lt_zero.mpr pos)), if_pos (neg_lt_zero.mpr pos), neg_neg,
    roundMagnitude_exact64 bits finite]

end SpecExt.Builtins.Float
