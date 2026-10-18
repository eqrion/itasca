import Exec.Interp.Numeric.Integer.IntCounts
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std

theorem countBits_zero (width : Nat) : Primitive.countBits width 0 = 0 := by
  induction width with
  | zero => rfl
  | succ width ih => simp [Primitive.countBits,ih]

theorem countBits_extend (width extra value : Nat) (bound : value < 2^width) :
    Primitive.countBits (width+extra) value = Primitive.countBits width value := by
  induction width generalizing value with
  | zero =>
    have zero : value=0 := by simpa using bound
    subst value
    simp [countBits_zero]
  | succ width ih =>
    have half : value/2 < 2^width := by
      rw [Nat.pow_succ] at bound
      omega
    simp only [Nat.succ_add,Primitive.countBits]
    rw [ih (value/2) half]

theorem countBits_width (width value : Nat) (bound : width ≤ 64) (fits : value < 2^width) :
    Primitive.countBits 64 value = Primitive.countBits width value := by
  have eq := countBits_extend width (64-width) value fits
  simpa only [Nat.add_sub_of_le bound] using eq
end Exec.Interp.Simd
