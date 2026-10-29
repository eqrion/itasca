import Itasca.Runtime.Interp.Numeric.Integer.IntCounts

/-!
Bit-count arithmetic within bounded lane widths.

Main declarations: `count_bits_zero` and `count_bits_width`. A direct consumer is `Interp.Simd.Integer.UnaryBits`.
-/

namespace Itasca.Runtime.Interp.Simd
open Aeneas Aeneas.Std

theorem count_bits_zero (width : Nat) : Primitive.countBits width 0 = 0 := by
  induction width with
  | zero => rfl
  | succ width ih => simp [Primitive.countBits,ih]

theorem count_bits_extend (width extra value : Nat) (bound : value < 2^width) :
    Primitive.countBits (width+extra) value = Primitive.countBits width value := by
  induction width generalizing value with
  | zero =>
    have zero : value=0 := by simpa using bound
    subst value
    simp [count_bits_zero]
  | succ width ih =>
    have half : value/2 < 2^width := by
      rw [Nat.pow_succ] at bound
      omega
    simp only [Nat.succ_add,Primitive.countBits]
    rw [ih (value/2) half]

theorem count_bits_width (width value : Nat) (bound : width ≤ 64) (fits : value < 2^width) :
    Primitive.countBits 64 value = Primitive.countBits width value := by
  have eq := count_bits_extend width (64-width) value fits
  simpa only [Nat.add_sub_of_le bound] using eq
end Itasca.Runtime.Interp.Simd
