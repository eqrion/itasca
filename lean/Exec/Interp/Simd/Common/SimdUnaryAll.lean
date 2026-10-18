import Exec.Interp.Simd.Common.SimdUnary
namespace Exec.Interp.Simd
open Aeneas Aeneas.Std

theorem lane_nonzero (width : Nat) (bits : BitVec width) (bound : width ≤ 64) :
    ((⟨bits.setWidth 64⟩ : U64) != 0#u64) = true ↔ bits.toNat ≠ 0 := by
  have value : (bits.setWidth 64).toNat = bits.toNat := by
    rw [BitVec.toNat_setWidth,Nat.mod_eq_of_lt]
    exact lt_of_lt_of_le bits.isLt (Nat.pow_le_pow_right (by decide) bound)
  simp only [bne_iff_ne]
  constructor
  · intro nonzero zero
    apply nonzero
    apply UScalar.eq_of_val_eq
    exact value.trans zero
  · intro nonzero zero
    apply nonzero
    exact value.symm.trans (congrArg UScalar.val zero)

theorem unary_all_iff (width : Nat) (x : BitVec 128) (count : Nat) (bound : width ≤ 64) :
    unaryAll width x count = true ↔ ∀ j, j < count → (laneBits width j x).toNat ≠ 0 := by
  induction count with
  | zero => simp [unaryAll]
  | succ count ih =>
    simp only [unaryAll,Bool.and_eq_true,ih,lane_nonzero width _ bound]
    constructor
    · rintro ⟨earlier,last⟩ j valid
      by_cases eq : j=count
      · simpa only [eq] using last
      · exact earlier j (by omega)
    · intro all
      exact ⟨fun j bound => all j (by omega),all count (by omega)⟩
end Exec.Interp.Simd
