import SpecExt.Builtins.Float.Decoding
import SpecExt.Builtins.Float.Round

/-! Range facts for rational rounding. The binary search and final adjacent
choice never construct a NaN encoding, independently of rounding accuracy. -/

namespace SpecExt.Builtins.Float
open SpecExt.Builtins

theorem floorEncoding_bound (width : Nat) (square : Bool) (q : Rat)
    (fuel lo hi bound : Nat) (hlo : lo ≤ bound) (hhi : hi ≤ bound) :
    floorEncoding width square q fuel lo hi ≤ bound := by
  induction fuel generalizing lo hi with
  | zero => exact hlo
  | succ fuel ih =>
    simp only [floorEncoding]
    have hm : (lo + hi + 1) / 2 ≤ bound := by omega
    split_ifs <;> first
    | exact ih _ _ hm hhi
    | exact ih _ _ hlo (by omega)

theorem roundMagnitude_noNaN_32 (square : Bool) (q : Rat) :
    isNaN (.POS (roundMagnitude 32 square q)) = false := by
  have hb := floorEncoding_bound 32 square q 32 0 (infinityBits 32 - 1)
    (infinityBits 32 - 1) (Nat.zero_le _) (Nat.le_refl _)
  norm_num [infinityBits, E, fun_M, signif, expon] at hb
  unfold roundMagnitude
  simp only [show infinityBits 32 = 2139095040 from rfl, Nat.reduceSub]
  change isNaN (floatOfBits 32 _) = false
  rw [isNaN_floatOfBits_32]
  split_ifs <;> simp only [decide_eq_false_iff_not, not_lt] <;>
    exact le_trans (Nat.mod_le _ _) (by omega)

theorem roundMagnitude_noNaN_64 (square : Bool) (q : Rat) :
    isNaN (.POS (roundMagnitude 64 square q)) = false := by
  have hb := floorEncoding_bound 64 square q 64 0 (infinityBits 64 - 1)
    (infinityBits 64 - 1) (Nat.zero_le _) (Nat.le_refl _)
  norm_num [infinityBits, E, fun_M, signif, expon] at hb
  unfold roundMagnitude
  simp only [show infinityBits 64 = 9218868437227405312 from rfl, Nat.reduceSub]
  change isNaN (floatOfBits 64 _) = false
  rw [isNaN_floatOfBits_64]
  split_ifs <;> simp only [decide_eq_false_iff_not, not_lt] <;>
    exact le_trans (Nat.mod_le _ _) (by omega)

theorem roundMagnitude_noNaN (width : Nat) (hw : width = 32 ∨ width = 64)
    (square : Bool) (q : Rat) : isNaN (.POS (roundMagnitude width square q)) = false := by
  rcases hw with rfl | rfl
  · exact roundMagnitude_noNaN_32 square q
  · exact roundMagnitude_noNaN_64 square q

theorem round_noNaN (width : Nat) (hw : width = 32 ∨ width = 64)
    (q : Rat) (negativeZero : Bool) : isNaN (round width q negativeZero) = false := by
  unfold round
  split_ifs
  · cases negativeZero <;> rfl
  · change isNaN (.POS (roundMagnitude width false (-q))) = false
    exact roundMagnitude_noNaN width hw false (-q)
  · exact roundMagnitude_noNaN width hw false q

theorem roundSqrt_noNaN (width : Nat) (hw : width = 32 ∨ width = 64)
    (q : Rat) : isNaN (roundSqrt width q) = false :=
  roundMagnitude_noNaN width hw true q

end SpecExt.Builtins.Float
